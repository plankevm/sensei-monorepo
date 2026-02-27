use std::collections::HashMap;

use sir_data::{Control, EthIRProgram, LocalId, Operation, operation::InlineOperands};

pub struct CopyPropagation {
    copy_map: HashMap<LocalId, LocalId>,
}

impl CopyPropagation {
    pub fn new() -> Self {
        Self { copy_map: HashMap::new() }
    }

    pub fn run(&mut self, program: &mut EthIRProgram) {
        for bb in program.basic_blocks.iter_mut() {
            self.copy_map.clear();

            let ops_span = bb.operations;
            for op in &program.operations[ops_span] {
                if let Operation::SetCopy(InlineOperands { ins: [src], outs: [dst] }) = op {
                    let resolved_src = self.copy_map.get(src).unwrap_or(src);
                    let prev = self.copy_map.insert(*dst, *resolved_src);
                    debug_assert!(prev.is_none(), "SSA violation: {:?} defined twice", dst);
                }
            }

            for op_idx in ops_span.iter() {
                let mut op = program.operations[op_idx];
                for input in op.inputs_mut(&mut program.locals) {
                    replace_if_copied(input, &self.copy_map);
                }
                program.operations[op_idx] = op;
            }

            for local in &mut program.locals[bb.outputs] {
                replace_if_copied(local, &self.copy_map);
            }

            match &mut bb.control {
                Control::Branches(branch) => {
                    replace_if_copied(&mut branch.condition, &self.copy_map);
                }
                Control::Switch(switch) => {
                    replace_if_copied(&mut switch.condition, &self.copy_map);
                }
                _ => {}
            }
        }
    }
}

fn replace_if_copied(input: &mut LocalId, copy_map: &HashMap<LocalId, LocalId>) {
    if let Some(replacement) = copy_map.get(input) {
        *input = *replacement;
    }
}

#[cfg(test)]
mod tests {
    use super::CopyPropagation;
    use sir_parser::{EmitConfig, parse_or_panic};
    use sir_test_utils::assert_trim_strings_eq_with_diff;

    fn run_copy_prop(source: &str) -> String {
        let mut ir = parse_or_panic(source, EmitConfig::init_only());
        CopyPropagation::new().run(&mut ir);
        sir_data::display_program(&ir)
    }

    #[test]
    fn test_copy_chains_and_inline_operands() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry b {
                    a1 = copy b
                    a2 = copy b
                    c1 = copy a1
                    c2 = copy a2
                    d = add c1 c2
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 {
        $1 = copy $0
        $2 = copy $0
        $3 = copy $0
        $4 = copy $0
        $5 = add $0 $0
        stop
    }
        "#;

        let actual = run_copy_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "copy chains and inline operands");
    }

    #[test]
    fn test_phi_nodes_block_propagation() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry b -> a_out {
                    a = copy b
                    a_out = copy a
                    => @next
                }
                next a_in {
                    c = add a_in a_in
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 -> $0 {
        $1 = copy $0
        $2 = copy $0
        => @2
    }

    @2 $3 {
        $4 = add $3 $3
        stop
    }
        "#;

        let actual = run_copy_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "phi nodes block propagation");
    }

    #[test]
    fn test_branch_condition_propagation() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry x {
                    cond = copy x
                    => cond ? @nonzero : @zero
                }
                nonzero {
                    stop
                }
                zero {
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 {
        $1 = copy $0
        => $0 ? @2 : @3
    }

    @2 {
        stop
    }

    @3 {
        stop
    }
        "#;

        let actual = run_copy_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "branch condition propagation");
    }

    #[test]
    fn test_switch_condition_propagation() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry x {
                    cond = copy x
                    switch cond {
                        0 => @case_zero
                        default => @case_default
                    }
                }
                case_zero {
                    stop
                }
                case_default {
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 {
        $1 = copy $0
        switch $0 {
            0 => @2,
            else => @3
        }

    }

    @2 {
        stop
    }

    @3 {
        stop
    }
        "#;

        let actual = run_copy_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "switch condition propagation");
    }

    #[test]
    fn test_icall_argument_propagation() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn callee:
                entry x -> result {
                    result = add x x
                    iret
                }
            fn caller:
                entry b {
                    a = copy b
                    sum = icall @callee a
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 1)
    fn @2 -> entry @2  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 -> $1 {
        $1 = add $0 $0
        iret
    }

    @2 $2 {
        $3 = copy $2
        $4 = icall @1 $2
        stop
    }
        "#;

        let actual = run_copy_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "icall argument propagation");
    }

    #[test]
    fn test_copy_map_does_not_leak_between_blocks() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry b -> a b {
                    a = copy b
                    => @next
                }
                next c d {
                    e = add c d
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 -> $0 $0 {
        $1 = copy $0
        => @2
    }

    @2 $2 $3 {
        $4 = add $2 $3
        stop
    }
        "#;

        let actual = run_copy_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "copy map does not leak between blocks",
        );
    }
}
