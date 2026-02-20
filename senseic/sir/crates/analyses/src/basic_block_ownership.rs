use sir_data::{BasicBlockId, EthIRProgram, FunctionId, IndexVec, index_vec};

#[derive(Debug, Clone)]
pub struct BasicBlockOwnershipAndReachability {
    ownership: IndexVec<BasicBlockId, Option<FunctionId>>,
}

impl BasicBlockOwnershipAndReachability {
    pub fn analyze(program: &EthIRProgram) -> Self {
        let mut ownership = index_vec![None; program.basic_blocks.len()];

        for func in program.functions_iter() {
            Self::mark_reachable_blocks(&mut ownership, program, func.entry().id(), func.id());
        }

        Self { ownership }
    }

    fn mark_reachable_blocks(
        ownership: &mut IndexVec<BasicBlockId, Option<FunctionId>>,
        program: &EthIRProgram,
        current: BasicBlockId,
        owner: FunctionId,
    ) {
        if ownership[current].is_some() {
            return;
        }

        ownership[current] = Some(owner);

        for successor in program.block(current).successors() {
            Self::mark_reachable_blocks(ownership, program, successor, owner);
        }
    }

    pub fn get_owner(&self, block: BasicBlockId) -> Option<FunctionId> {
        self.ownership[block]
    }

    pub fn is_reachable(&self, block: BasicBlockId) -> bool {
        self.ownership[block].is_some()
    }

    pub fn blocks_owned_by(&self, func: FunctionId) -> impl Iterator<Item = BasicBlockId> + '_ {
        self.ownership
            .enumerate_idx()
            .filter_map(move |(bb_id, owner)| if *owner == Some(func) { Some(bb_id) } else { None })
    }

    pub fn unreachable_blocks(&self) -> impl Iterator<Item = BasicBlockId> + '_ {
        self.ownership.enumerate_idx().filter_map(
            move |(bb_id, owner)| {
                if owner.is_none() { Some(bb_id) } else { None }
            },
        )
    }

    pub fn display_ir_with_function_grouping(&self, program: &EthIRProgram) -> String {
        use std::fmt::Write;
        let mut output = String::new();

        for func in program.functions_iter() {
            writeln!(&mut output, "fn @{}:", func.id()).unwrap();

            for bb_id in self.blocks_owned_by(func.id()) {
                writeln!(&mut output, "{}", program.block(bb_id)).unwrap();
            }
        }

        let mut unreachable = self.unreachable_blocks().peekable();
        if unreachable.peek().is_some() {
            writeln!(&mut output, "// Unreachable basic blocks").unwrap();
            for bb_id in unreachable {
                writeln!(&mut output, "{}", program.block(bb_id)).unwrap();
            }
        }

        if !program.data_segments.is_empty() {
            writeln!(&mut output).unwrap();

            for (segment_id, data) in program.data_segments.enumerate_idx() {
                write!(&mut output, "data .{segment_id} ").unwrap();

                write!(&mut output, "0x").unwrap();
                for &byte in data {
                    write!(&mut output, "{:02x}", byte).unwrap();
                }
                writeln!(&mut output).unwrap();
            }
        }

        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sir_data::{Branch, Control, builder::EthIRBuilder, operation::*};

    #[test]
    fn test_simple_ownership() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let mut bb0 = func.begin_basic_block();
        bb0.add_operation(Operation::Noop(()));
        let bb0_id = bb0.finish(Control::ContinuesTo(BasicBlockId::new(1))).unwrap();

        let mut bb1 = func.begin_basic_block();
        bb1.add_operation(Operation::Stop(()));
        let bb1_id = bb1.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb0_id);
        let program = builder.build(func_id, None);

        let analysis = BasicBlockOwnershipAndReachability::analyze(&program);

        assert_eq!(analysis.get_owner(bb0_id), Some(func_id));
        assert_eq!(analysis.get_owner(bb1_id), Some(func_id));

        assert!(analysis.is_reachable(bb0_id));
        assert!(analysis.is_reachable(bb1_id));

        assert!(analysis.unreachable_blocks().next().is_none());
    }

    #[test]
    fn test_unreachable_blocks() {
        let mut builder = EthIRBuilder::new();

        let mut func = builder.begin_function();
        let mut bb0 = func.begin_basic_block();
        bb0.add_operation(Operation::Stop(()));
        let bb0_id = bb0.finish(Control::LastOpTerminates).unwrap();
        let func_id = func.finish(bb0_id);

        let mut orphan_func = builder.begin_function();
        let mut bb1 = orphan_func.begin_basic_block();
        bb1.add_operation(Operation::Stop(()));
        let bb1_id = bb1.finish(Control::LastOpTerminates).unwrap();

        let program = builder.build(func_id, None);

        let analysis = BasicBlockOwnershipAndReachability::analyze(&program);

        assert!(analysis.is_reachable(bb0_id));
        assert!(!analysis.is_reachable(bb1_id));

        assert_eq!(analysis.unreachable_blocks().collect::<Vec<_>>(), vec![bb1_id]);
    }

    #[test]
    fn test_multiple_functions() {
        let mut builder = EthIRBuilder::new();

        let mut func0 = builder.begin_function();

        let mut bb0 = func0.begin_basic_block();
        bb0.add_operation(Operation::Noop(()));
        let bb0_id = bb0.finish(Control::LastOpTerminates).unwrap();

        let mut bb1 = func0.begin_basic_block();
        bb1.add_operation(Operation::Stop(()));
        let bb1_id = bb1.finish(Control::LastOpTerminates).unwrap();

        func0.set_control(bb0_id, Control::ContinuesTo(bb1_id)).unwrap();

        let func0_id = func0.finish(bb0_id);

        let mut func1 = builder.begin_function();
        let mut bb2 = func1.begin_basic_block();
        bb2.add_operation(Operation::Noop(()));
        let bb2_id = bb2.finish(Control::InternalReturn).unwrap();
        let func1_id = func1.finish(bb2_id);

        let program = builder.build(func0_id, None);

        let analysis = BasicBlockOwnershipAndReachability::analyze(&program);

        assert_eq!(analysis.get_owner(bb0_id), Some(func0_id));
        assert_eq!(analysis.get_owner(bb1_id), Some(func0_id));
        assert_eq!(analysis.get_owner(bb2_id), Some(func1_id));

        assert_eq!(analysis.blocks_owned_by(func0_id).collect::<Vec<_>>(), vec![bb0_id, bb1_id]);
        assert_eq!(analysis.blocks_owned_by(func1_id).collect::<Vec<_>>(), vec![bb2_id]);
    }

    #[test]
    fn test_branching_control_flow() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let condition = func.new_local();

        let bb1_id = func.ir_builder.next_basic_block_id() + 1;
        let bb2_id = func.ir_builder.next_basic_block_id() + 2;

        let mut bb0 = func.begin_basic_block();
        bb0.add_operation(Operation::Noop(()));
        let bb0_id = bb0
            .finish(Control::Branches(Branch {
                condition,
                zero_target: bb1_id,
                non_zero_target: bb2_id,
            }))
            .unwrap();

        let mut bb1 = func.begin_basic_block();
        bb1.add_operation(Operation::Stop(()));
        let bb1_id_actual = bb1.finish(Control::LastOpTerminates).unwrap();

        let mut bb2 = func.begin_basic_block();
        bb2.add_operation(Operation::Stop(()));
        let bb2_id_actual = bb2.finish(Control::LastOpTerminates).unwrap();

        assert_eq!(bb1_id, bb1_id_actual);
        assert_eq!(bb2_id, bb2_id_actual);

        let func_id = func.finish(bb0_id);
        let program = builder.build(func_id, None);

        let analysis = BasicBlockOwnershipAndReachability::analyze(&program);

        assert_eq!(analysis.get_owner(bb0_id), Some(func_id));
        assert_eq!(analysis.get_owner(bb1_id), Some(func_id));
        assert_eq!(analysis.get_owner(bb2_id), Some(func_id));

        assert!(analysis.is_reachable(bb0_id));
        assert!(analysis.is_reachable(bb1_id));
        assert!(analysis.is_reachable(bb2_id));
    }
}
