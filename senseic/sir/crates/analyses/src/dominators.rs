use sir_data::{BasicBlockId, BasicBlockIdMarker, EthIRProgram, IndexVec, index_vec};

use crate::compute_predecessors;

// uses Semi-NCA
pub fn compute_dominators(program: &EthIRProgram) -> IndexVec<BasicBlockIdMarker, BasicBlockId> {
    let mut result = index_vec![BasicBlockId::ZERO; program.basic_blocks.len()];

    for func in program.functions.iter() {
        compute_function_dominators(program, func.entry(), &mut result);
    }

    result
}

fn compute_function_dominators(
    program: &EthIRProgram,
    entry: BasicBlockId,
    result: &mut IndexVec<BasicBlockIdMarker, BasicBlockId>,
) {
    let mut dfnum = index_vec![usize::MAX; program.basic_blocks.len()];
    let mut parent = index_vec![BasicBlockId::ZERO; program.basic_blocks.len()];
    parent[entry] = entry;
    let mut vertex = Vec::new();
    dfs_number(entry, program, &mut dfnum, &mut parent, &mut vertex);

    let predecessors = compute_predecessors(program);
    let sdom = compute_semi_dominators(&vertex, &dfnum, &parent, &predecessors);

    result[entry] = entry;
    for i in 1..vertex.len() {
        let w = vertex[i];
        let sdom_node = vertex[sdom[w]];

        let mut y = parent[w];
        while dfnum[y] > sdom[w] {
            y = parent[y];
        }

        if y == sdom_node {
            result[w] = sdom_node;
        } else {
            result[w] = result[y];
        }
    }
}

fn dfs_number(
    bb_id: BasicBlockId,
    program: &EthIRProgram,
    dfnum: &mut IndexVec<BasicBlockIdMarker, usize>,
    parent: &mut IndexVec<BasicBlockIdMarker, BasicBlockId>,
    vertex: &mut Vec<BasicBlockId>,
) {
    dfnum[bb_id] = vertex.len();
    vertex.push(bb_id);

    for succ in program.basic_blocks[bb_id].control.iter_outgoing(program) {
        if dfnum[succ] != usize::MAX {
            continue;
        };
        parent[succ] = bb_id;
        dfs_number(succ, program, dfnum, parent, vertex);
    }
}

fn compute_semi_dominators(
    vertex: &[BasicBlockId],
    dfnum: &IndexVec<BasicBlockIdMarker, usize>,
    parent: &IndexVec<BasicBlockIdMarker, BasicBlockId>,
    predecessors: &IndexVec<BasicBlockIdMarker, Vec<BasicBlockId>>,
) -> IndexVec<BasicBlockIdMarker, usize> {
    let mut ancestor: IndexVec<BasicBlockIdMarker, Option<BasicBlockId>> =
        index_vec![None; dfnum.len()];
    let mut sdom = index_vec![usize::MAX; dfnum.len()];
    let mut best = index_vec![BasicBlockId::ZERO; dfnum.len()];
    for &v in vertex {
        sdom[v] = dfnum[v];
        best[v] = v;
    }

    for i in (1..vertex.len()).rev() {
        let w = vertex[i];

        for &pred in &predecessors[w] {
            if dfnum[pred] == usize::MAX {
                continue;
            }

            let candidate_sdom = if dfnum[pred] < dfnum[w] {
                dfnum[pred]
            } else {
                sdom[eval(pred, &mut ancestor, &mut best, &sdom)]
            };

            if candidate_sdom < sdom[w] {
                sdom[w] = candidate_sdom;
            }
        }

        ancestor[w] = Some(parent[w]);
    }

    sdom
}

fn eval(
    v: BasicBlockId,
    ancestor: &mut IndexVec<BasicBlockIdMarker, Option<BasicBlockId>>,
    best: &mut IndexVec<BasicBlockIdMarker, BasicBlockId>,
    sdom: &IndexVec<BasicBlockIdMarker, usize>,
) -> BasicBlockId {
    if ancestor[v].is_none() {
        return v;
    }
    compress(v, ancestor, best, sdom);
    best[v]
}

fn compress(
    v: BasicBlockId,
    ancestor: &mut IndexVec<BasicBlockIdMarker, Option<BasicBlockId>>,
    best: &mut IndexVec<BasicBlockIdMarker, BasicBlockId>,
    sdom: &IndexVec<BasicBlockIdMarker, usize>,
) {
    let a = ancestor[v].unwrap();

    if ancestor[a].is_none() {
        return;
    }

    compress(a, ancestor, best, sdom);

    if sdom[best[a]] < sdom[best[v]] {
        best[v] = best[a];
    }

    ancestor[v] = ancestor[a];
}

#[cfg(test)]
mod tests {
    use super::*;
    use sir_parser::{EmitConfig, parse_or_panic};

    fn bb(n: u32) -> BasicBlockId {
        BasicBlockId::new(n)
    }

    #[test]
    fn test_self_loop() {
        // A → A (self-loop)
        let program = parse_or_panic(
            r#"
            fn init:
                a {
                    => @a
                }
            "#,
            EmitConfig::init_only(),
        );

        let dominators = compute_dominators(&program);

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
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

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
        assert_eq!(dominators[bb(1)], bb(0)); // idom(B) = A
        assert_eq!(dominators[bb(2)], bb(1)); // idom(C) = B
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

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
        assert_eq!(dominators[bb(1)], bb(0)); // idom(B) = A
        assert_eq!(dominators[bb(2)], bb(0)); // idom(C) = A
        assert_eq!(dominators[bb(3)], bb(0)); // idom(D) = A (not B or C)
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

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
        assert_eq!(dominators[bb(1)], bb(0)); // idom(B) = A
        assert_eq!(dominators[bb(2)], bb(0)); // idom(C) = A
        assert_eq!(dominators[bb(3)], bb(1)); // idom(D) = B
        assert_eq!(dominators[bb(4)], bb(0)); // idom(E) = A (common dominator of C and D)
        assert_eq!(dominators[bb(5)], bb(4)); // idom(F) = E
    }

    #[test]
    fn test_nested_loops() {
        // A → B → C → D → C (inner loop)
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

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
        assert_eq!(dominators[bb(1)], bb(0)); // idom(B) = A
        assert_eq!(dominators[bb(2)], bb(1)); // idom(C) = B
        assert_eq!(dominators[bb(3)], bb(2)); // idom(D) = C
        assert_eq!(dominators[bb(4)], bb(3)); // idom(E) = D
        assert_eq!(dominators[bb(5)], bb(4)); // idom(F) = E
    }

    #[test]
    fn test_unreachable_node() {
        // A → B, C is unreachable from A
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
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let mut dominators = index_vec![BasicBlockId::ZERO; program.basic_blocks.len()];
        compute_function_dominators(&program, bb(0), &mut dominators);

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
        assert_eq!(dominators[bb(1)], bb(0)); // idom(B) = A
        assert_eq!(dominators[bb(2)], bb(0)); // C stays at default (ZERO), unreachable
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

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
        assert_eq!(dominators[bb(1)], bb(0)); // idom(B) = A
        assert_eq!(dominators[bb(2)], bb(2)); // idom(C) = C (entry of other)
        assert_eq!(dominators[bb(3)], bb(2)); // idom(D) = C
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

        assert_eq!(dominators[bb(0)], bb(0)); // idom(A) = A
        assert_eq!(dominators[bb(1)], bb(0)); // idom(B) = A
        assert_eq!(dominators[bb(2)], bb(0)); // idom(C) = A
        assert_eq!(dominators[bb(3)], bb(0)); // idom(D) = A (common dominator of B and C paths)
    }
}
