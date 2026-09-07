use std::num::NonZero;

use plank_core::Idx;
use proptest::prelude::*;
use sir_data::{OperationIdx, StaticAllocId};

use crate::{
    BlockFinalization,
    depth_first_search::SearchConfig,
    op_graph::{OpGraph, OpGraphBuilder, OpNodeKind},
    scheduler,
    stack::ShuffleConfig,
    validation,
};

fn generated_graph() -> impl Strategy<Value = (OpGraph, BlockFinalization)> {
    (
        0usize..5,
        prop::collection::vec(
            (
                prop::collection::vec(any::<usize>(), 0..4),
                0usize..3,
                prop::collection::vec(any::<usize>(), 0..4),
                any::<bool>(),
            ),
            0..20,
        ),
        prop::collection::vec(any::<usize>(), 0..5),
        any::<bool>(),
    )
        .prop_map(|(input_count, operations, outputs, terminates)| {
            let mut builder = OpGraphBuilder::with_capacity(operations.len() + 1, 64);
            let mut values =
                (0..input_count).map(|_| builder.push_input_value()).collect::<Vec<_>>();
            let mut builder = builder.end_inputs_begin_ops();
            let mut predecessors = Vec::new();
            for (inputs, output_count, effects, flippable) in operations {
                let index = OperationIdx::new(u32::try_from(predecessors.len()).unwrap());
                let kind = if flippable && inputs.len() >= 2 && !values.is_empty() {
                    OpNodeKind::Flippable(index)
                } else {
                    OpNodeKind::Normal(index)
                };
                let mut operation = builder.begin_op(kind);
                if !values.is_empty() {
                    for input in inputs {
                        operation.add_input(values[input % values.len()]);
                    }
                }
                if !predecessors.is_empty() {
                    for effect in effects {
                        operation.add_predecessor(predecessors[effect % predecessors.len()]);
                    }
                }
                predecessors.push(operation.id());
                let mut operation = operation.end_inputs_begin_outputs();
                values.extend((0..output_count).map(|_| operation.add_output()));
            }
            if terminates {
                let index = OperationIdx::new(u32::try_from(predecessors.len()).unwrap());
                let mut operation = builder.begin_op(OpNodeKind::Normal(index));
                for predecessor in predecessors {
                    operation.add_predecessor(predecessor);
                }
                if let Some(&value) = values.last() {
                    operation.add_input(value);
                }
                let _operation = operation.end_inputs_begin_outputs();
            }
            let mut builder = builder.end_ops_begin_end_stack();
            if !terminates && !values.is_empty() {
                for output in outputs {
                    builder.push_end_stack_value(values[output % values.len()]);
                }
            }
            let finalization = if terminates {
                BlockFinalization::LastOpTerminates
            } else {
                BlockFinalization::ShuffleToOutputs
            };
            (builder.finish(), finalization)
        })
}

proptest! {
    #[test]
    fn expanded_schedules_preserve_stack_and_effects((graph, finalization) in generated_graph()) {
        let result = scheduler::schedule(
            finalization,
            StaticAllocId::ZERO,
            ShuffleConfig::PRE_AMSTERDAM,
            SearchConfig {
                max_candidates: NonZero::new(20).unwrap(),
                copy_all_inputs: false,
                alignment_factor: 5,
                arity_factor: 5,
                layout_alignment_factor: 2,
            },
            &graph,
        );
        let validation = validation::validate(
            &graph,
            finalization,
            ShuffleConfig::PRE_AMSTERDAM,
            StaticAllocId::ZERO,
            &result.ops,
        );
        prop_assert!(validation.is_ok(), "{validation:?}");
    }
}
