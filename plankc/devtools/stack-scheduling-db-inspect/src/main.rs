use clap::Parser;
use csv as _;
use serde_json as _;
use sir_data as _;
use sir_stack_scheduling as _;
use sir_stack_scheduling_common as _;
use sir_stack_scheduling_db_inspect::{
    find, random, render_graph, render_schedule, render_source_blocks,
};
use std::{path::PathBuf, process::ExitCode};

#[cfg(test)]
use plank_test_utils as _;

#[derive(Parser)]
#[command(about = "Display a canonical stack-scheduling graph and its best known schedule")]
struct Args {
    /// Canonical hash or unique hash prefix, with or without the ssb1: prefix.
    #[arg(required_unless_present = "random", conflicts_with = "random")]
    hash: Option<String>,

    /// Pick a random canonical block instead of specifying a hash.
    #[arg(long)]
    random: bool,

    /// Database directory or canonical-blocks.sqlite3 path.
    #[arg(short, long, default_value_os_t = default_database_path())]
    database: PathBuf,
}

fn default_database_path() -> PathBuf {
    sir_stack_scheduling_common::workspace_corpus_path("stack-scheduling-db")
}

fn main() -> ExitCode {
    match run(Args::parse()) {
        Ok(output) => {
            println!("{output}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: Args) -> Result<String, String> {
    let entry = if args.random {
        random(&args.database)?
    } else {
        find(
            &args.database,
            args.hash.as_deref().expect("hash is required unless --random is present"),
        )?
    };
    let source_blocks_text = render_source_blocks(&entry.source_blocks);
    let graph_text = render_graph(&entry.graph);
    let schedule_text = render_schedule(&entry.graph, entry.finalization, &entry.schedule)?;
    Ok(format!(
        "hash: {}\n\n{source_blocks_text}\n\ngraph:\n{graph_text}\n\nbest schedule (gas: {}):\n{schedule_text}",
        entry.canonical_hash, entry.gas_cost
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use plank_test_utils::dedent_preserve_indent;
    use sir_stack_scheduling_common::{
        CANONICAL_BLOCKS_FILE_NAME, CanonicalBlockRow, seed_canonical_database,
    };

    #[test]
    fn renders_a_complete_sqlite_entry_by_hash_or_random_selection() {
        let directory = tempfile::tempdir().unwrap();
        std::fs::write(
            directory.path().join("blocks.csv"),
            "file,block_id,canonical_hash\nsample.sir,0,ssb1:test\n",
        )
        .unwrap();
        let path = directory.path().join(CANONICAL_BLOCKS_FILE_NAME);
        seed_canonical_database(&path, &[CanonicalBlockRow {
            canonical_hash: "ssb1:test".to_owned(),
            canonical_graph: r#"{"finalization":"shuffle_to_outputs","input_count":1,"operations":[],"outputs_fifo":[0]}"#.to_owned(),
            best_schedule: "[]".to_owned(),
            best_gas_cost: 0,
            manually_optimized: false,
        }]).unwrap();
        let expected = dedent_preserve_indent(
            r#"
            hash: ssb1:test

            source blocks (1):
              sample.sir: bb0

            graph:
            inputs: [v0]
            outputs: [v0]

            best schedule (gas: 0):
            ; start:  [v0]
        "#,
        );
        for database in [directory.path(), path.as_path()] {
            for (hash, random) in [
                (Some("ssb1:test"), false),
                (Some("test"), false),
                (Some("tes"), false),
                (None, true),
            ] {
                let output = run(Args {
                    hash: hash.map(str::to_owned),
                    random,
                    database: database.to_owned(),
                })
                .unwrap();
                assert_eq!(output, expected);
            }
        }
    }
}
