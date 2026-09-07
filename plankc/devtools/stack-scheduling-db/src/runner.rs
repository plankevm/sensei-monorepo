use crate::{database::DatabaseWriter, pipeline};
use sir_stack_scheduling_common::Corpus;
use std::path::PathBuf;

pub struct RunConfig {
    pub input: PathBuf,
    pub output_directory: PathBuf,
}

pub fn run(config: RunConfig) {
    let corpus = Corpus::load(config.input);
    let mut database = DatabaseWriter::create(config.output_directory);

    for (index, entry) in corpus.entries().enumerate() {
        eprintln!("[{}/{}] {}", index + 1, corpus.len(), entry.display_path.display());
        pipeline::run(
            &entry.source,
            &entry.display_path,
            |block_id, graph, canonical, schedule| {
                database.collect(&entry.display_path, block_id, graph, canonical, schedule);
            },
        );
    }

    database.finish();
}

#[cfg(test)]
mod tests {
    use super::*;
    use plank_test_utils::dedent_preserve_indent;
    use sir_stack_scheduling_common::{BLOCKS_FILE_NAME, CanonicalBlockRow, CanonicalDatabase};
    use std::fs;

    #[test]
    fn writes_the_complete_two_table_database() {
        let temporary = tempfile::tempdir().unwrap();
        let corpus = temporary.path().join("corpus");
        let output = temporary.path().join("database");
        fs::create_dir(&corpus).unwrap();
        fs::write(
            corpus.join("sample.sir"),
            dedent_preserve_indent(
                r#"
                fn init:
                    entry {
                        stop
                    }
                fn main:
                    entry {
                        x = const 1
                        y = const 2
                        sum = add x y
                        stop
                    }
                "#,
            ),
        )
        .unwrap();

        run(RunConfig { input: corpus.clone(), output_directory: output.clone() });
        run(RunConfig { input: corpus, output_directory: output.clone() });

        let blocks = fs::read_to_string(output.join(BLOCKS_FILE_NAME)).unwrap();
        let canonical_blocks = CanonicalDatabase::open(&output).unwrap().all().unwrap();
        let expected_blocks = dedent_preserve_indent(
            r#"
            file,block_id,canonical_hash
            sample.sir,0,ssb1:f0961e2656d671f102b8cd9583392b9ea008a2f43e777631b2731e3ea82b99c9
            sample.sir,1,ssb1:b456edeffb54263bdc5e7525e9d69c976235fc5c75c11f28ea487539cd7d79d8
            "#,
        ) + "\n";
        let expected_canonical_blocks = dedent_preserve_indent(
            r#"
            canonical_hash,canonical_graph,best_schedule,best_gas_cost,manually_optimized
            ssb1:b456edeffb54263bdc5e7525e9d69c976235fc5c75c11f28ea487539cd7d79d8,"{""finalization"":""last_op_terminates"",""input_count"":0,""operations"":[{""inputs_fifo"":[],""output_count"":0,""effect_predecessors"":[],""flippable"":false},{""inputs_fifo"":[],""output_count"":1,""effect_predecessors"":[],""flippable"":false},{""inputs_fifo"":[],""output_count"":1,""effect_predecessors"":[],""flippable"":false},{""inputs_fifo"":[0,1],""output_count"":1,""effect_predecessors"":[],""flippable"":true}],""outputs_fifo"":[]}","[{""op"":2},{""op"":1},{""op"":3},{""op"":0}]",0,false
            ssb1:f0961e2656d671f102b8cd9583392b9ea008a2f43e777631b2731e3ea82b99c9,"{""finalization"":""last_op_terminates"",""input_count"":0,""operations"":[{""inputs_fifo"":[],""output_count"":0,""effect_predecessors"":[],""flippable"":false}],""outputs_fifo"":[]}","[{""op"":0}]",0,false
            "#,
        ) + "\n";
        assert_eq!(blocks, expected_blocks);
        let expected = csv::Reader::from_reader(expected_canonical_blocks.as_bytes())
            .deserialize::<CanonicalBlockRow>()
            .collect::<Result<Box<[_]>, _>>()
            .unwrap();
        assert_eq!(canonical_blocks, expected);
    }
}
