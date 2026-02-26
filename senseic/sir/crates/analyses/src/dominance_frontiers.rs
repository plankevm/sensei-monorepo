use sir_data::{BasicBlockId, DenseIndexSet, IndexVec, index_vec};

pub fn compute_dominance_frontiers(
    dominators: &IndexVec<BasicBlockId, Option<BasicBlockId>>,
    predecessors: &IndexVec<BasicBlockId, Vec<BasicBlockId>>,
) -> IndexVec<BasicBlockId, DenseIndexSet<BasicBlockId>> {
    let mut frontiers = index_vec![DenseIndexSet::new(); dominators.len()];

    for (b, preds) in predecessors.enumerate_idx() {
        if preds.len() < 2 {
            continue;
        }
        let Some(idom) = dominators[b] else {
            continue;
        };
        for &p in preds {
            if dominators[p].is_none() {
                continue;
            }
            let mut runner = p;
            while runner != idom {
                frontiers[runner].add(b);
                runner = dominators[runner].expect("reachable path");
            }
        }
    }

    frontiers
}
