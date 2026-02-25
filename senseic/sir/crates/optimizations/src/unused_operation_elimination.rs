use sir_analyses::{DefUse, UseKind, compute_def_use};
use sir_data::{EthIRProgram, Idx, IndexVec, LocalId, Operation, OperationIdx};

pub struct UnusedOperationElimination {
    def_sites: IndexVec<LocalId, Option<OperationIdx>>,
    pending_removals: Vec<OperationIdx>,
}

impl UnusedOperationElimination {
    pub fn new() -> Self {
        Self { def_sites: IndexVec::new(), pending_removals: Vec::new() }
    }

    pub fn run(&mut self, program: &mut EthIRProgram, uses: &mut DefUse) {
        self.def_sites.clear();
        self.def_sites.resize(program.next_free_local_id.idx(), None);
        self.pending_removals.clear();

        compute_def_use(program, uses);

        for op in program.operations() {
            for out in op.outputs() {
                self.def_sites[*out] = Some(op.id());
            }

            if is_removable(&op.op(), program, uses) {
                self.pending_removals.push(op.id());
            }
        }

        while let Some(op_idx) = self.pending_removals.pop() {
            let op = &program.operations[op_idx];
            if matches!(op, Operation::Noop(())) {
                continue;
            }

            for &input in op.inputs(program) {
                uses[input].retain(|u| u.kind != UseKind::Operation(op_idx));

                if let Some(def_idx) = self.def_sites[input] {
                    let defining_op = &program.operations[def_idx];
                    if !matches!(defining_op, Operation::Noop(()))
                        && is_removable(defining_op, program, uses)
                    {
                        self.pending_removals.push(def_idx);
                    }
                }
            }

            for &out in op.outputs(program) {
                self.def_sites[out] = None;
            }
            program.operations[op_idx] = Operation::Noop(());
        }
    }
}

pub fn run(program: &mut EthIRProgram) {
    let mut uses = DefUse::new();
    UnusedOperationElimination::new().run(program, &mut uses);
}

fn is_removable(op: &Operation, program: &EthIRProgram, uses: &DefUse) -> bool {
    op.kind().is_removable_when_unused()
        && op.outputs(program).iter().all(|out| uses[*out].is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use sir_parser::{EmitConfig, parse_or_panic};
    use sir_test_utils::assert_trim_strings_eq_with_diff;

    fn run_pass(source: &str) -> String {
        let mut ir = parse_or_panic(source, EmitConfig::init_only());
        run(&mut ir);
        sir_data::display_program(&ir)
    }

    // Note: block outputs count as uses, even if the successor never uses the input.
    #[test]
    fn test_block_outputs_count_as_uses() {
        let input = r#"
            fn init:
                entry {
                    cond = const 1
                    => cond ? @left : @right
                }
                left -> a {
                    a = const 10
                    => @merge
                }
                right -> b {
                    dead = const 99
                    b = const 20
                    => @merge
                }
                merge x {
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x1
        => $0 ? @1 : @2
    }

    @1 -> $1 {
        $1 = const 0xa
        => @3
    }

    @2 -> $3 {
        noop
        $3 = const 0x14
        => @3
    }

    @3 $4 {
        stop
    }
        "#;

        let actual = run_pass(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "block outputs count as uses");
    }

    #[test]
    fn test_cross_block_chain_eliminated() {
        let input = r#"
            fn init:
                entry {
                    a = const 0
                    => @next
                }
                next {
                    b = sload a
                    c = add b b
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        noop
        => @1
    }

    @1 {
        noop
        noop
        stop
    }
        "#;

        let actual = run_pass(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "cross block chain eliminated");
    }

    #[test]
    fn test_side_effecting_ops_preserved() {
        let input = r#"
            fn init:
                entry {
                    a = const 1
                    b = const 2
                    sum unused = icall @callee a b
                    key = const 0
                    sstore key sum
                    stop
                }
            fn callee:
                entry x y -> s d {
                    s = add x y
                    d = sub x y
                    iret
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 2)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 $0 $1 -> $2 $3 {
        $2 = add $0 $1
        $3 = sub $0 $1
        iret
    }

    @1 {
        $4 = const 0x1
        $5 = const 0x2
        $6 $7 = icall @0 $4 $5
        $8 = const 0x0
        sstore $8 $6
        stop
    }
        "#;

        let actual = run_pass(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "side effecting ops preserved");
    }

    #[test]
    fn test_control_flow_vars_preserved() {
        let input = r#"
            fn init:
                entry {
                    cond = const 1
                    => cond ? @true : @false
                }
                true {
                    stop
                }
                false {
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x1
        => $0 ? @1 : @2
    }

    @1 {
        stop
    }

    @2 {
        stop
    }
        "#;

        let actual = run_pass(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "control flow vars preserved");
    }

    #[test]
    fn test_mixed_live_dead_chains() {
        let input = r#"
            fn init:
                entry {
                    x = const 1
                    y = add x x
                    key = const 0
                    sstore key y
                    z = add x x
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x1
        $1 = add $0 $0
        $2 = const 0x0
        sstore $2 $1
        noop
        stop
    }
        "#;

        let actual = run_pass(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "mixed live dead chains");
    }
}
