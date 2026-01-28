use std::collections::HashMap;

use sir_data::{
    Control, EthIRProgram, LocalId, LocalIdMarker, X32,
    operation::{InlineOperands, OpVisitorMut},
};

struct CopyReplacer<'a> {
    copy_map: &'a HashMap<LocalId, LocalId>,
    locals: &'a mut [LocalId],
}

fn replace_if_copied(input: &mut X32<LocalIdMarker>, copy_map: &HashMap<LocalId, LocalId>) {
    if let Some(replacement) = copy_map.get(input) {
        *input = *replacement;
    }
}

impl OpVisitorMut<()> for CopyReplacer<'_> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut InlineOperands<INS, OUTS>,
    ) {
        for input in &mut data.ins {
            replace_if_copied(input, &self.copy_map);
        }
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut sir_data::operation::AllocatedIns<INS, OUTS>,
    ) {
        let start = data.ins_start.idx();
        for i in start..start + INS {
            replace_if_copied(&mut self.locals[i], &self.copy_map);
        }
    }

    fn visit_static_alloc_mut(&mut self, _data: &mut sir_data::operation::StaticAllocData) {}

    fn visit_memory_load_mut(&mut self, data: &mut sir_data::operation::MemoryLoadData) {
        replace_if_copied(&mut data.ptr, &self.copy_map);
    }

    fn visit_memory_store_mut(&mut self, data: &mut sir_data::operation::MemoryStoreData) {
        replace_if_copied(&mut data.ptr, &self.copy_map);
        replace_if_copied(&mut data.value, &self.copy_map);
    }

    fn visit_set_small_const_mut(&mut self, _data: &mut sir_data::operation::SetSmallConstData) {}

    fn visit_set_large_const_mut(&mut self, _data: &mut sir_data::operation::SetLargeConstData) {}

    fn visit_set_data_offset_mut(&mut self, _data: &mut sir_data::operation::SetDataOffsetData) {}

    fn visit_icall_mut(&mut self, data: &mut sir_data::operation::InternalCallData) {
        let start = data.ins_start.idx();
        let end = data.outs_start.idx();
        for i in start..end {
            replace_if_copied(&mut self.locals[i], &self.copy_map);
        }
    }

    fn visit_void_mut(&mut self) {}
}

pub fn run(program: &mut EthIRProgram) {
    let mut copy_map: HashMap<LocalId, LocalId> = HashMap::new();
    for bb in program.basic_blocks.iter_mut() {
        let ops_range = bb.operations.clone();
        copy_map.clear();

        for op in &mut program.operations[ops_range.clone()] {
            if let sir_data::Operation::SetCopy(InlineOperands { ins: [src], outs: [dst] }) = op {
                let resolved_src = copy_map.get(src).unwrap_or(src);
                copy_map.insert(*dst, *resolved_src);
            }
        }

        let locals = program.locals.as_raw_slice_mut();
        let mut replacer = CopyReplacer { copy_map: &copy_map, locals };
        for op in &mut program.operations[ops_range] {
            op.visit_data_mut(&mut replacer);
        }

        let outputs_range = bb.outputs.clone();
        for index in outputs_range.start.idx()..outputs_range.end.idx() {
            let local = &mut locals[index];
            replace_if_copied(local, &copy_map);
        }

        match &mut bb.control {
            Control::Branches(branch) => {
                replace_if_copied(&mut branch.condition, &copy_map);
            }
            Control::Switch(switch) => {
                replace_if_copied(&mut switch.condition, &copy_map);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sir_parser::{EmitConfig, parse_or_panic};
    use sir_test_utils::assert_trim_strings_eq_with_diff;

    fn run_copy_prop(source: &str) -> String {
        let mut ir = parse_or_panic(source, EmitConfig::init_only());
        run(&mut ir);
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
}
