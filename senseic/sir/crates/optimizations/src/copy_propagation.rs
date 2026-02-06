use std::collections::HashMap;

use sir_data::{
    Control, EthIRProgram, LocalId, LocalIdMarker, LocalIndexMarker, Operation, RelSliceMut, Span,
    X32,
    operation::{
        AllocatedIns, InlineOperands, InternalCallData, MemoryLoadData, MemoryStoreData,
        OpVisitorMut, SetDataOffsetData, SetLargeConstData, SetSmallConstData, StaticAllocData,
    },
};

struct CopyReplacer<'a> {
    copy_map: &'a HashMap<LocalId, LocalId>,
    locals: RelSliceMut<'a, LocalIndexMarker, LocalId>,
}

fn replace_if_copied(input: &mut X32<LocalIdMarker>, copy_map: &HashMap<LocalId, LocalId>) {
    if let Some(replacement) = copy_map.get(input) {
        *input = *replacement;
    }
}

impl<'d> OpVisitorMut<'d, ()> for CopyReplacer<'_> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d mut InlineOperands<INS, OUTS>,
    ) {
        for input in &mut data.ins {
            replace_if_copied(input, self.copy_map);
        }
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d mut AllocatedIns<INS, OUTS>,
    ) {
        for idx in Span::new(data.ins_start, data.ins_start + INS as u32).iter() {
            replace_if_copied(&mut self.locals[idx], self.copy_map);
        }
    }

    fn visit_static_alloc_mut(&mut self, _data: &'d mut StaticAllocData) {}

    fn visit_memory_load_mut(&mut self, data: &'d mut MemoryLoadData) {
        replace_if_copied(&mut data.ptr, self.copy_map);
    }

    fn visit_memory_store_mut(&mut self, data: &'d mut MemoryStoreData) {
        for input in &mut data.ins {
            replace_if_copied(input, self.copy_map);
        }
    }

    fn visit_set_small_const_mut(&mut self, _data: &'d mut SetSmallConstData) {}

    fn visit_set_large_const_mut(&mut self, _data: &'d mut SetLargeConstData) {}

    fn visit_set_data_offset_mut(&mut self, _data: &'d mut SetDataOffsetData) {}

    fn visit_icall_mut(&mut self, data: &'d mut InternalCallData) {
        for idx in Span::new(data.ins_start, data.outs_start).iter() {
            replace_if_copied(&mut self.locals[idx], self.copy_map);
        }
    }

    fn visit_void_mut(&mut self) {}
}

pub fn run(program: &mut EthIRProgram) {
    let mut copy_map: HashMap<LocalId, LocalId> = HashMap::new();
    for bb in program.basic_blocks.iter_mut() {
        copy_map.clear();

        let ops_span = bb.operations;
        for op in &mut program.operations[ops_span] {
            if let Operation::SetCopy(InlineOperands { ins: [src], outs: [dst] }) = op {
                let resolved_src = copy_map.get(src).unwrap_or(src);
                let prev = copy_map.insert(*dst, *resolved_src);
                debug_assert!(prev.is_none(), "SSA violation: {:?} defined twice", dst);
            }
        }

        let locals = program.locals.as_rel_slice_mut();
        let mut replacer = CopyReplacer { copy_map: &copy_map, locals };
        for op in &mut program.operations[ops_span] {
            op.visit_data_mut(&mut replacer);
        }

        for local in &mut program.locals[bb.outputs] {
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

    #[test]
    fn test_copy_map_does_not_leak_between_blocks() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry b {
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

    @1 $0 {
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
