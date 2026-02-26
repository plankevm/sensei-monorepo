use sir_data::{BasicBlockId, DenseIndexSet, EthIRProgram, IndexVec, index_vec};

use crate::compute_predecessors;

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

// iterative dominator algorithm using RPO
pub fn compute_dominators(program: &EthIRProgram) -> IndexVec<BasicBlockId, Option<BasicBlockId>> {
    let mut dominators = index_vec![None; program.basic_blocks.len()];

    for func in program.functions_iter() {
        compute_function_dominators(program, func.entry().id(), &mut dominators);
    }

    dominators
}

fn compute_function_dominators(
    program: &EthIRProgram,
    entry: BasicBlockId,
    dominators: &mut IndexVec<BasicBlockId, Option<BasicBlockId>>,
) {
    dominators[entry] = Some(entry);

    let mut visited = DenseIndexSet::new();
    let mut reverse_post_order = Vec::new();
    dfs_postorder(program, entry, &mut visited, &mut reverse_post_order);
    reverse_post_order.reverse();
    let mut bb_to_rpo_pos = index_vec![0; program.basic_blocks.len()];
    for (pos, &basic_block) in reverse_post_order.iter().enumerate() {
        bb_to_rpo_pos[basic_block] = pos as u32;
    }

    let mut predecessors = IndexVec::new();
    compute_predecessors(program, &mut predecessors);
    let mut changed = true;
    while changed {
        changed = false;
        for bb in reverse_post_order[1..].iter() {
            debug_assert!(
                !predecessors[*bb].is_empty(),
                "non-entry block in RPO has no predecessors"
            );
            let mut new_idom = predecessors[*bb][0];
            for pred in predecessors[*bb][1..].iter() {
                if dominators[*pred].is_some() {
                    new_idom = intersect(*pred, new_idom, dominators, &bb_to_rpo_pos);
                }
            }
            if dominators[*bb] != Some(new_idom) {
                dominators[*bb] = Some(new_idom);
                changed = true;
            }
        }
    }
}

fn intersect(
    bb1: BasicBlockId,
    bb2: BasicBlockId,
    dominators: &IndexVec<BasicBlockId, Option<BasicBlockId>>,
    bb_to_rpo_pos: &IndexVec<BasicBlockId, u32>,
) -> BasicBlockId {
    let mut finger1 = bb1;
    let mut finger2 = bb2;
    while finger1 != finger2 {
        while bb_to_rpo_pos[finger1] > bb_to_rpo_pos[finger2] {
            finger1 = dominators[finger1]
                .expect("intersect only called on blocks with computed dominators");
        }
        while bb_to_rpo_pos[finger2] > bb_to_rpo_pos[finger1] {
            finger2 = dominators[finger2]
                .expect("intersect only called on blocks with computed dominators");
        }
    }
    finger1
}

fn dfs_postorder(
    program: &EthIRProgram,
    bb: BasicBlockId,
    visited: &mut DenseIndexSet<BasicBlockId>,
    postorder: &mut Vec<BasicBlockId>,
) {
    if visited.contains(bb) {
        return;
    }
    visited.add(bb);
    for succ in program.block(bb).successors() {
        dfs_postorder(program, succ, visited, postorder);
    }
    postorder.push(bb);
}

#[cfg(test)]
mod tests {
    use super::*;
    use sir_parser::{EmitConfig, parse_or_panic};

    fn bb(n: u32) -> BasicBlockId {
        BasicBlockId::new(n)
    }

    fn frontier_to_vec(df: &DenseIndexSet<BasicBlockId>) -> Vec<BasicBlockId> {
        df.iter().collect()
    }

    fn frontiers(
        program: &EthIRProgram,
        dominators: &IndexVec<BasicBlockId, Option<BasicBlockId>>,
    ) -> IndexVec<BasicBlockId, DenseIndexSet<BasicBlockId>> {
        let mut predecessors = IndexVec::new();
        compute_predecessors(program, &mut predecessors);
        compute_dominance_frontiers(dominators, &predecessors)
    }

    #[test]
    fn test_loop_back_edge() {
        // A → B → C → B (back-edge)
        //     |
        //     D
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    => @b
                }
                b {
                    x = const 1
                    => x ? @c : @d
                }
                c {
                    => @b
                }
                d {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(1))); // idom(C) = B
        assert_eq!(dominators[bb(3)], Some(bb(1))); // idom(D) = B

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![bb(1)]); // DF(B) = {B}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![bb(1)]); // DF(C) = {B}
        assert_eq!(frontier_to_vec(&df[bb(3)]), vec![]); // DF(D) = {}
    }

    #[test]
    fn test_linear_chain() {
        // A → B → C
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    => @b
                }
                b {
                    => @c
                }
                c {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(1))); // idom(C) = B

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![]); // DF(B) = {}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![]); // DF(C) = {}
    }

    #[test]
    fn test_diamond() {
        //     A
        //    / \
        //   B   C
        //    \ /
        //     D
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    x = const 1
                    => x ? @b : @c
                }
                b {
                    => @d
                }
                c {
                    => @d
                }
                d {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(0))); // idom(C) = A
        assert_eq!(dominators[bb(3)], Some(bb(0))); // idom(D) = A (not B or C)

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![bb(3)]); // DF(B) = {D}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![bb(3)]); // DF(C) = {D}
        assert_eq!(frontier_to_vec(&df[bb(3)]), vec![]); // DF(D) = {}
    }

    #[test]
    fn test_cross_edges() {
        //     A
        //    / \
        //   B   C
        //   |   |
        //   D → E (cross edge from D to E)
        //       |
        //       F
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    x = const 1
                    => x ? @b : @c
                }
                b {
                    => @d
                }
                c {
                    => @e
                }
                d {
                    => @e
                }
                e {
                    => @f
                }
                f {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(0))); // idom(C) = A
        assert_eq!(dominators[bb(3)], Some(bb(1))); // idom(D) = B
        assert_eq!(dominators[bb(4)], Some(bb(0))); // idom(E) = A (common dominator of C and D)
        assert_eq!(dominators[bb(5)], Some(bb(4))); // idom(F) = E

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![bb(4)]); // DF(B) = {E}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![bb(4)]); // DF(C) = {E}
        assert_eq!(frontier_to_vec(&df[bb(3)]), vec![bb(4)]); // DF(D) = {E}
        assert_eq!(frontier_to_vec(&df[bb(4)]), vec![]); // DF(E) = {}
        assert_eq!(frontier_to_vec(&df[bb(5)]), vec![]); // DF(F) = {}
    }

    #[test]
    fn test_nested_loops() {
        // A → B → C ⟷ D (inner loop C-D)
        //     ↑       ↓
        //     +───────E → F (exit)
        //     (D also → B via E, outer backedge)
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    => @b
                }
                b {
                    => @c
                }
                c {
                    => @d
                }
                d {
                    x = const 1
                    => x ? @c : @e
                }
                e {
                    y = const 1
                    => y ? @b : @f
                }
                f {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(1))); // idom(C) = B
        assert_eq!(dominators[bb(3)], Some(bb(2))); // idom(D) = C
        assert_eq!(dominators[bb(4)], Some(bb(3))); // idom(E) = D
        assert_eq!(dominators[bb(5)], Some(bb(4))); // idom(F) = E

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![bb(1)]); // DF(B) = {B}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![bb(1), bb(2)]); // DF(C) = {B, C}
        assert_eq!(frontier_to_vec(&df[bb(3)]), vec![bb(1), bb(2)]); // DF(D) = {B, C}
        assert_eq!(frontier_to_vec(&df[bb(4)]), vec![bb(1)]); // DF(E) = {B}
        assert_eq!(frontier_to_vec(&df[bb(5)]), vec![]); // DF(F) = {}
    }

    #[test]
    fn test_unreachable_block() {
        // A → B, C is in same function but unreachable
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    => @b
                }
                b {
                    stop
                }
                c {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], None); // C is unreachable

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![]); // DF(B) = {}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![]); // DF(C) = {}
    }

    #[test]
    fn test_multiple_entry_points() {
        // Two disconnected components: A → B, C → D
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    => @b
                }
                b {
                    stop
                }
            fn other:
                c {
                    => @d
                }
                d {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(2))); // idom(C) = C (entry of other)
        assert_eq!(dominators[bb(3)], Some(bb(2))); // idom(D) = C

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![]); // DF(B) = {}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![]); // DF(C) = {}
        assert_eq!(frontier_to_vec(&df[bb(3)]), vec![]); // DF(D) = {}
    }

    #[test]
    fn test_stacked_diamonds() {
        //     A
        //    / \
        //   B   C
        //    \ /
        //     D
        //    / \
        //   E   F
        //    \ /
        //     G
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    x = const 1
                    => x ? @b : @c
                }
                b {
                    => @d
                }
                c {
                    => @d
                }
                d {
                    y = const 1
                    => y ? @e : @f
                }
                e {
                    => @g
                }
                f {
                    => @g
                }
                g {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(0))); // idom(C) = A
        assert_eq!(dominators[bb(3)], Some(bb(0))); // idom(D) = A
        assert_eq!(dominators[bb(4)], Some(bb(3))); // idom(E) = D
        assert_eq!(dominators[bb(5)], Some(bb(3))); // idom(F) = D
        assert_eq!(dominators[bb(6)], Some(bb(3))); // idom(G) = D

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![bb(3)]); // DF(B) = {D}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![bb(3)]); // DF(C) = {D}
        assert_eq!(frontier_to_vec(&df[bb(3)]), vec![]); // DF(D) = {}
        assert_eq!(frontier_to_vec(&df[bb(4)]), vec![bb(6)]); // DF(E) = {G}
        assert_eq!(frontier_to_vec(&df[bb(5)]), vec![bb(6)]); // DF(F) = {G}
        assert_eq!(frontier_to_vec(&df[bb(6)]), vec![]); // DF(G) = {}
    }

    #[test]
    fn test_irreducible_cfg() {
        // Irreducible CFG - loop with multiple entries
        //     A
        //    / \
        //   B ↔ C
        //    \ /
        //     D
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    x = const 1
                    => x ? @b : @c
                }
                b {
                    y = const 1
                    => y ? @c : @d
                }
                c {
                    z = const 1
                    => z ? @b : @d
                }
                d {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);
        let df = frontiers(&program, &dominators);

        assert_eq!(dominators[bb(0)], Some(bb(0))); // idom(A) = A
        assert_eq!(dominators[bb(1)], Some(bb(0))); // idom(B) = A
        assert_eq!(dominators[bb(2)], Some(bb(0))); // idom(C) = A
        assert_eq!(dominators[bb(3)], Some(bb(0))); // idom(D) = A (common dominator of B and C paths)

        assert_eq!(frontier_to_vec(&df[bb(0)]), vec![]); // DF(A) = {}
        assert_eq!(frontier_to_vec(&df[bb(1)]), vec![bb(2), bb(3)]); // DF(B) = {C, D}
        assert_eq!(frontier_to_vec(&df[bb(2)]), vec![bb(1), bb(3)]); // DF(C) = {B, D}
        assert_eq!(frontier_to_vec(&df[bb(3)]), vec![]); // DF(D) = {}
    }
}
