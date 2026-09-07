# Stack scheduling database builder

This tool runs the current stack-scheduling pipeline over the benchmark corpus and writes a
database under the gitignored workspace directory `corpus/stack-scheduling-db`:

- `blocks.csv`: `(file, block_id) -> canonical_hash`
- `canonical-blocks.sqlite3`:
  `canonical_hash -> (canonical_graph, best_schedule, best_gas_cost, manually_optimized)`

The graph and schedule columns contain compact JSON. Graph operation and value IDs are canonical
IDs, and spill allocation IDs in schedules are normalized to block-local slots. The graph records
all data dependencies, non-data effect predecessors, operation arities, flippability, outputs, and
block finalization, which is sufficient to reconstruct a representative operation graph for stack
scheduling.

Run it with the default corpus at `corpus/stack-scheduling`:

```bash
cargo run --release -p sir-stack-scheduling-db
```

A SIR file or another corpus and output directory can be supplied positionally:

```bash
cargo run --release -p sir-stack-scheduling-db -- \
  corpus/my-input \
  corpus/my-scheduling-db
```

The tool creates SQLite if missing (or initializes an empty database), inserts new graphs, and
updates existing schedules only when cheaper. Re-running it preserves manual improvements, the
runner's `manually_optimized` flags, and previously stored graphs. `blocks.csv` is regenerated for
the current input corpus.

To reproduce a fresh baseline, run against a new output directory. No CSV import command is needed.
