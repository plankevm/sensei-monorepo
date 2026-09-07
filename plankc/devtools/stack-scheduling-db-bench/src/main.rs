mod stats;

use indicatif::{ProgressBar, ProgressStyle};
use sir_stack_scheduling::{
    BlockFinalization,
    display::{graph as render_graph, trace},
    op_graph::CanonicalBlock,
    schedule_graph,
    stack::{ShuffleConfig, StackOps, gas_cost},
};
use sir_stack_scheduling_common::{
    CanonicalBlockRow, CanonicalDatabase, improve_schedule, workspace_corpus_path,
};
use stats::Stats;
use std::{process::ExitCode, time::Instant};

fn main() -> ExitCode {
    match run() {
        Ok(summary) => {
            println!("{summary}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<String, String> {
    let start = Instant::now();
    let path = workspace_corpus_path("stack-scheduling-db");
    let mut rows = CanonicalDatabase::open(&path)?.all()?;
    let graph_count = rows.len();
    let manually_optimized_count = rows.iter().filter(|row| row.manually_optimized).count();
    if graph_count == 0 {
        return Err("database contains no canonical blocks".to_owned());
    }
    let progress = ProgressBar::new(
        u64::try_from(graph_count).expect("canonical graph count does not fit u64"),
    );
    progress.set_style(
        ProgressStyle::with_template("{msg} {pos}/{len}").expect("progress template is valid"),
    );
    progress.set_message("processing");
    let mut stats = Stats::new(graph_count, manually_optimized_count);

    for row in &mut rows {
        let previous_cost = row.best_gas_cost;
        if let Err(error) = process_graph(row, &mut stats) {
            progress.finish_and_clear();
            return Err(error);
        }
        if row.best_gas_cost < previous_cost {
            let schedule = serde_json::from_str::<Box<[StackOps]>>(&row.best_schedule)
                .map_err(|error| error.to_string())?;
            improve_schedule(&path, &row.canonical_hash, &schedule)?;
        }
        progress.inc(1);
    }
    progress.finish_and_clear();

    Ok(stats.render(start.elapsed()))
}

fn process_graph(row: &mut CanonicalBlockRow, stats: &mut Stats) -> Result<(), String> {
    let canonical = serde_json::from_str::<CanonicalBlock>(&row.canonical_graph)
        .map_err(|error| format!("graph {} is invalid: {error}", row.canonical_hash))?;
    let best_known_schedule = serde_json::from_str::<Box<[StackOps]>>(&row.best_schedule)
        .map_err(|error| format!("schedule {} is invalid: {error}", row.canonical_hash))?;
    let encoded_best_known_gas = gas_cost(&best_known_schedule, ShuffleConfig::PRE_AMSTERDAM);
    if encoded_best_known_gas != row.best_gas_cost {
        return Err(format!(
            "schedule {} has gas cost {encoded_best_known_gas}, database records {}",
            row.canonical_hash, row.best_gas_cost
        ));
    }

    let finalization = canonical.finalization;
    let graph = canonical.to_op_graph().map_err(|error| {
        format!("graph {} cannot be reconstructed: {error}", row.canonical_hash)
    })?;
    let result = schedule_graph(&graph, finalization);
    validate_schedule(&row.canonical_hash, &graph, finalization, &result.ops)?;

    let local_gas = gas_cost(&result.ops, ShuffleConfig::PRE_AMSTERDAM);
    let best_known_gas = row.best_gas_cost;
    stats.record(best_known_gas, local_gas, result.candidate_limit_reached, row.manually_optimized);
    if local_gas < best_known_gas {
        row.best_schedule = serde_json::to_string(&result.ops).map_err(|error| {
            format!("failed to encode schedule {}: {error}", row.canonical_hash)
        })?;
        row.best_gas_cost = local_gas;
    }
    Ok(())
}

fn validate_schedule(
    canonical_hash: &str,
    graph: &sir_stack_scheduling::op_graph::OpGraph,
    finalization: BlockFinalization,
    schedule: &[StackOps],
) -> Result<(), String> {
    let trace = trace(
        graph,
        finalization,
        ShuffleConfig::PRE_AMSTERDAM,
        sir_data::StaticAllocId::default(),
        schedule,
    );
    let Some(error) = trace.error else {
        return Ok(());
    };
    Err(format!(
        "generated invalid schedule for {canonical_hash}\n\ngraph:\n{}\n\nschedule:\n{}\n\nvalidation error: {error}",
        render_graph(graph),
        trace.rendering
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use plank_core::Idx;
    use sir_data::OperationIdx;
    use sir_stack_scheduling::op_graph::{CanonicalOperation, CanonicalValueId};

    #[test]
    fn replaces_a_worse_best_known_schedule_in_memory() {
        let graph = CanonicalBlock::new(
            BlockFinalization::ShuffleToOutputs,
            1,
            Box::new([CanonicalOperation {
                inputs_fifo: Box::new([CanonicalValueId::ZERO]),
                output_count: 1,
                effect_predecessors: Box::new([]),
                flippable: false,
            }]),
            Box::new([CanonicalValueId::ZERO + 1]),
        );
        let baseline: Box<[StackOps]> =
            Box::new([StackOps::Dup(0), StackOps::Pop, StackOps::Op(OperationIdx::ZERO)]);
        let mut row = CanonicalBlockRow {
            canonical_hash: "ssb1:test".to_owned(),
            canonical_graph: serde_json::to_string(&graph).unwrap(),
            best_schedule: serde_json::to_string(&baseline).unwrap(),
            best_gas_cost: gas_cost(&baseline, ShuffleConfig::PRE_AMSTERDAM),
            manually_optimized: true,
        };
        let mut stats = Stats::new(1, 1);

        process_graph(&mut row, &mut stats).unwrap();

        assert_eq!(row.best_gas_cost, 0);
        let schedule = serde_json::from_str::<Box<[StackOps]>>(&row.best_schedule).unwrap();
        assert_eq!(schedule.as_ref(), &[StackOps::Op(OperationIdx::ZERO)]);
    }
}
