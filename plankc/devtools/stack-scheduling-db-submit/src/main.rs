use clap::Parser;
use sir_stack_scheduling::stack::{ShuffleConfig, gas_cost, parse_stack_ops};
use sir_stack_scheduling_common::{ScheduleUpdate, improve_schedule, workspace_corpus_path};
use sir_stack_scheduling_db_inspect::{find, render_graph, trace_schedule};
use std::{
    fmt::Write,
    io::{self, Read},
    path::{Path, PathBuf},
    process::ExitCode,
};

#[derive(Parser)]
#[command(about = "Validate and submit an improved stack schedule to the deduplication database")]
struct Args {
    /// Canonical hash, with or without the ssb1: prefix.
    hash: String,

    /// Whitespace-separated stack operations. Reads stdin when omitted.
    #[arg(value_name = "STACK_OP")]
    stack_ops: Vec<String>,

    /// Database directory or canonical-blocks.sqlite3 path.
    #[arg(short, long, default_value_os_t = default_database_path())]
    database: PathBuf,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SubmissionStatus {
    Accepted,
    Rejected,
}

struct SubmissionResult {
    status: SubmissionStatus,
    output: String,
}

fn default_database_path() -> PathBuf {
    workspace_corpus_path("stack-scheduling-db")
}

fn main() -> ExitCode {
    let args = Args::parse();
    let source = if args.stack_ops.is_empty() {
        let mut source = String::new();
        if let Err(error) = io::stdin().read_to_string(&mut source) {
            eprintln!("error: failed to read schedule from stdin: {error}");
            return ExitCode::FAILURE;
        }
        source
    } else {
        args.stack_ops.join(" ")
    };

    match submit(&args.database, &args.hash, &source) {
        Ok(result) => {
            println!("{}", result.output);
            match result.status {
                SubmissionStatus::Accepted => ExitCode::SUCCESS,
                SubmissionStatus::Rejected => ExitCode::FAILURE,
            }
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn submit(database: &Path, hash: &str, source: &str) -> Result<SubmissionResult, String> {
    let entry = find(database, hash)?;
    let graph_text = render_graph(&entry.graph);
    let parsed = parse_stack_ops(source, ShuffleConfig::PRE_AMSTERDAM);
    let gas_cost = gas_cost(&parsed.operations, ShuffleConfig::PRE_AMSTERDAM);
    let trace = trace_schedule(&entry.graph, entry.finalization, &parsed.operations);

    let validation_error = trace.error.as_ref().map(ToString::to_string);
    let (submission_status, status_text) = match parsed.error.or(validation_error) {
        Some(reason) => (SubmissionStatus::Rejected, format!("rejected: {reason}")),
        None => match improve_schedule(database, &entry.canonical_hash, &parsed.operations)? {
            ScheduleUpdate::Improved { previous_cost, new_cost } => (
                SubmissionStatus::Accepted,
                format!("accepted: improved gas cost from {previous_cost} to {new_cost}"),
            ),
            ScheduleUpdate::NotImproved { current_cost } => (
                SubmissionStatus::Rejected,
                format!(
                    "rejected: gas cost {gas_cost} does not improve the current best cost {current_cost}"
                ),
            ),
        },
    };

    let mut output = String::new();
    writeln!(output, "hash: {}", entry.canonical_hash).unwrap();
    writeln!(output, "\ngraph:\n{graph_text}").unwrap();
    writeln!(output, "\nsubmitted schedule (gas: {gas_cost}):\n{}", trace.rendering).unwrap();
    write!(output, "\n{status_text}").unwrap();
    Ok(SubmissionResult { status: submission_status, output })
}

#[cfg(test)]
mod tests {
    use super::*;
    use plank_core::Idx;
    use plank_test_utils::dedent_preserve_indent;
    use sir_data::OperationIdx;
    use sir_stack_scheduling::{
        BlockFinalization,
        op_graph::{CanonicalBlock, CanonicalOperation, CanonicalValueId},
        stack::StackOps,
    };
    use sir_stack_scheduling_common::{
        BLOCKS_FILE_NAME, BLOCKS_HEADER, BlockRow, CANONICAL_BLOCKS_FILE_NAME, CanonicalBlockRow,
        CanonicalDatabase, seed_canonical_database,
    };

    const HASH: &str = "ssb1:test";

    fn database() -> tempfile::TempDir {
        let temporary = tempfile::tempdir().unwrap();
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

        let mut blocks = csv::WriterBuilder::new()
            .has_headers(false)
            .from_path(temporary.path().join(BLOCKS_FILE_NAME))
            .unwrap();
        blocks.write_record(BLOCKS_HEADER).unwrap();
        blocks
            .serialize(BlockRow {
                file: "sample.sir".to_owned(),
                block_id: 0,
                canonical_hash: HASH.to_owned(),
            })
            .unwrap();
        blocks.flush().unwrap();

        seed_canonical_database(
            &temporary.path().join(CANONICAL_BLOCKS_FILE_NAME),
            &[CanonicalBlockRow {
                canonical_hash: HASH.to_owned(),
                canonical_graph: serde_json::to_string(&graph).unwrap(),
                best_schedule: serde_json::to_string(&baseline).unwrap(),
                best_gas_cost: gas_cost(&baseline, ShuffleConfig::PRE_AMSTERDAM),
                manually_optimized: false,
            }],
        )
        .unwrap();
        temporary
    }

    #[test]
    fn accepts_and_persists_a_better_schedule() {
        let database = database();
        let result = submit(database.path(), HASH, "op0").unwrap();
        let expected = dedent_preserve_indent(
            r#"
            hash: ssb1:test

            graph:
            inputs: [v0]
            v1 = op0(v0)
            outputs: [v1]

            submitted schedule (gas: 0):
            ; start:  [v0]
            op0       [v1]

            accepted: improved gas cost from 6 to 0
            "#,
        );
        assert!(result.status == SubmissionStatus::Accepted);
        assert_eq!(result.output, expected);

        let updated = find(database.path(), HASH).unwrap();
        assert_eq!(updated.gas_cost, 0);
        assert_eq!(updated.schedule.as_ref(), &[StackOps::Op(OperationIdx::ZERO)]);
    }

    #[test]
    fn rejects_an_invalid_schedule_and_displays_its_valid_prefix() {
        let database = database();
        let before = CanonicalDatabase::open(database.path()).unwrap().all().unwrap();
        let result = submit(database.path(), HASH, "pop op0").unwrap();
        assert_eq!(CanonicalDatabase::open(database.path()).unwrap().all().unwrap(), before);
        let expected = dedent_preserve_indent(
            r#"
            hash: ssb1:test

            graph:
            inputs: [v0]
            v1 = op0(v0)
            outputs: [v1]

            submitted schedule (gas: 3):
            ; start:  [v0]
            pop         []

            rejected: stack operation 2: op0 underflowed the stack
            "#,
        );
        assert!(result.status == SubmissionStatus::Rejected);
        assert_eq!(result.output, expected);
    }

    #[test]
    fn rejects_an_incomplete_schedule() {
        let database = database();
        let result = submit(database.path(), HASH, "").unwrap();
        let expected = dedent_preserve_indent(
            r#"
            hash: ssb1:test

            graph:
            inputs: [v0]
            v1 = op0(v0)
            outputs: [v1]

            submitted schedule (gas: 0):
            ; start:  [v0]

            rejected: schedule does not execute op0
            "#,
        );
        assert!(result.status == SubmissionStatus::Rejected);
        assert_eq!(result.output, expected);
    }

    #[test]
    fn rejects_a_schedule_that_does_not_improve_gas() {
        let database = database();
        let result = submit(database.path(), HASH, "dup1 pop op0").unwrap();
        let expected = dedent_preserve_indent(
            r#"
            hash: ssb1:test

            graph:
            inputs: [v0]
            v1 = op0(v0)
            outputs: [v1]

            submitted schedule (gas: 6):
            ; start:      [v0]
            dup1      [v0, v0]
            pop           [v0]
            op0           [v1]

            rejected: gas cost 6 does not improve the current best cost 6
            "#,
        );
        assert!(result.status == SubmissionStatus::Rejected);
        assert_eq!(result.output, expected);
    }
}
