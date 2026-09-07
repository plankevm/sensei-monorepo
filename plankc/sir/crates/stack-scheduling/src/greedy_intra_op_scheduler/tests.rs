use crate::{
    greedy_intra_op_scheduler::greedy_schedule_op,
    op_graph::{OpGraph, OpGraphBuilder, OpNodeId, OpNodeKind, OpSet, ValueNodeId},
    stack::{EvmStack, ShuffleConfig, StackOps, TrackedStack},
};
use StackOps::*;
use plank_core::Idx;
use proptest::prelude::*;
use sir_data::{OperationIdx, StaticAllocId};
use std::collections::HashSet;

fn build_graph(
    start_stack: &[u32],
    start_spilled: &[u32],
    target_inputs: &[u32],
    last_uses: &HashSet<ValueNodeId>,
) -> (OpGraph, OpNodeId) {
    let total_values = start_stack
        .iter()
        .chain(start_spilled)
        .chain(target_inputs)
        .copied()
        .max()
        .map_or(0, |max| max as usize + 1);

    let mut builder = OpGraphBuilder::with_capacity(target_inputs.len() + 1, total_values);
    let mut values = Vec::with_capacity(total_values);
    for _ in 0..total_values {
        values.push(builder.push_input_value());
    }

    let mut builder = builder.end_inputs_begin_ops();
    let op_id = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        for &value in target_inputs {
            op.add_input(values[value as usize]);
        }
        let op_id = op.id();
        drop(op.end_inputs_begin_outputs());
        op_id
    };

    let mut seen_non_last_uses = HashSet::with_capacity(target_inputs.len());
    for &value in target_inputs {
        let value = values[value as usize];
        if !last_uses.contains(&value) && seen_non_last_uses.insert(value) {
            let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            op.add_input(value);
            drop(op.end_inputs_begin_outputs());
        }
    }

    (builder.end_ops_begin_end_stack().finish(), op_id)
}

fn assert_intra_op_schedule_exists(
    config: ShuffleConfig,
    start_stack: impl AsRef<[u32]>,
    start_spilled: impl AsRef<[u32]>,
    target_inputs: impl AsRef<[u32]>,
    last_uses: impl AsRef<[u32]>,
) -> Vec<StackOps> {
    let start_stack = start_stack.as_ref();
    let start_spilled = start_spilled.as_ref();
    let target_inputs = target_inputs.as_ref();
    let last_uses = last_uses.as_ref();

    let last_uses = last_uses.iter().copied().map(ValueNodeId::new).collect::<HashSet<_>>();
    let (graph, op_id) = build_graph(start_stack, start_spilled, target_inputs, &last_uses);
    let target = graph.get_op(op_id).inputs_fifo;

    let mut evm_stack = EvmStack::new();
    for &value in start_stack.iter().rev() {
        evm_stack.push(ValueNodeId::new(value));
    }

    let complete_backing = vec![0; graph.words_per_set() as usize];
    let complete = OpSet::new(&complete_backing, graph.total_ops());
    let mut ops = Vec::new();

    let mut stack = TrackedStack::new_from_parts(
        StaticAllocId::ZERO,
        |op| ops.push(op),
        evm_stack.fifo(),
        start_spilled.iter().map(|&v| ValueNodeId::new(v)).collect(),
    );

    for &value in target {
        assert!(
            stack.fifo().contains(&value) || stack.get_spilled(value).is_some(),
            "target input is neither on the stack nor spilled"
        );
    }

    greedy_schedule_op(config, &mut stack, &graph, op_id, complete, false);

    for &value in start_stack {
        let value = ValueNodeId::new(value);
        if !last_uses.contains(&value) {
            assert!(
                stack.find_first(value).is_some() || stack.get_spilled(value).is_some(),
                "non last use value {value:?} not preserved"
            );
        }
    }

    for &op in &ops {
        assert!(op.is_valid(config));
    }

    let last = ops.pop();
    assert_eq!(last, Some(Op(OperationIdx::new(0))), "last op not `Op(...)`");

    ops
}

fn assert_intra_op_schedule(
    config: ShuffleConfig,
    start_stack: impl AsRef<[u32]>,
    start_spilled: impl AsRef<[u32]>,
    target_inputs: impl AsRef<[u32]>,
    last_uses: impl AsRef<[u32]>,
    expected_ops: impl AsRef<[StackOps]>,
) {
    let ops = assert_intra_op_schedule_exists(
        config,
        start_stack,
        start_spilled,
        target_inputs,
        last_uses,
    );
    let expected = expected_ops.as_ref();
    let mut actual = String::new();
    use std::fmt::Write;
    for (i, e) in ops.iter().enumerate() {
        if i > 0 {
            write!(actual, ", ").unwrap();
        }
        write!(actual, "{e}").unwrap();
    }
    assert_eq!(&ops, expected, "actual = [{actual}]");
}

const fn store(id: u32) -> StackOps {
    StackOps::Store(StaticAllocId::new(id))
}

const fn load(id: u32) -> StackOps {
    StackOps::Load(StaticAllocId::new(id))
}

struct AssertScheduleBuilder {
    config: ShuffleConfig,
    spilled: Vec<u32>,
    last_uses: Vec<u32>,
}

impl AssertScheduleBuilder {
    fn max_swap_depth(mut self, depth: u8) -> Self {
        self.config = ShuffleConfig::max_swap_no_exchange(depth);
        self
    }

    fn spilled(mut self, values: impl AsRef<[u32]>) -> Self {
        self.spilled = values.as_ref().into();
        self
    }

    fn last_uses(mut self, values: impl AsRef<[u32]>) -> Self {
        self.last_uses = values.as_ref().into();
        self
    }

    fn assert(
        self,
        start: impl AsRef<[u32]>,
        target: impl AsRef<[u32]>,
        expected: impl AsRef<[StackOps]>,
    ) {
        assert_intra_op_schedule(
            self.config,
            start,
            self.spilled,
            target,
            self.last_uses,
            expected,
        );
    }
}

fn opts() -> AssertScheduleBuilder {
    AssertScheduleBuilder {
        config: ShuffleConfig::default(),
        spilled: Vec::new(),
        last_uses: Vec::new(),
    }
}

#[test]
fn schedules_flipped_operand_order() {
    let mut builder = OpGraphBuilder::with_capacity(1, 2);
    let high = builder.push_input_value();
    let deep = builder.push_input_value();
    let mut builder = builder.end_inputs_begin_ops();
    let op_id = {
        let mut op = builder.begin_op(OpNodeKind::Flippable(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(deep);
        let op_id = op.id();
        drop(op.end_inputs_begin_outputs());
        op_id
    };
    let graph = builder.end_ops_begin_end_stack().finish();
    let complete_backing = vec![0; graph.words_per_set() as usize];
    let complete = OpSet::new(&complete_backing, graph.total_ops());
    let mut ops = Vec::new();
    let mut stack = TrackedStack::new_from_parts(
        StaticAllocId::ZERO,
        |op| ops.push(op),
        &[deep, high],
        Vec::new(),
    );

    greedy_schedule_op(ShuffleConfig::default(), &mut stack, &graph, op_id, complete, true);

    assert_eq!(ops, [Flipped(OperationIdx::ZERO)]);
}

#[test]
fn no_inputs_do_nothing() {
    opts().spilled([3]).assert([1, 2], [], []);
}

#[test]
fn dup_available_input() {
    opts().assert([1], [1], [Dup(0)]);
}

#[test]
fn load_spilled_input() {
    opts().spilled([7]).assert([], [7], [load(0)]);
}

#[test]
fn last_use_in_place() {
    opts().last_uses([7]).assert([7], [7], []);
}

#[test]
fn simple_swap() {
    opts().last_uses([1, 2]).assert([1, 2], [2, 1], [Swap(1)]);
}

#[test]
fn scratch_suboptimal_permute() {
    opts().last_uses([1, 2]).assert([0, 1, 2], [0, 1, 2], [Swap(2), Swap(1), Dup(2)]);
}

#[test]
fn permutes_below_a_correct_prefix() {
    opts().last_uses([1, 2, 3]).assert([1, 3, 2], [1, 2, 3], [Swap(1), Swap(2), Swap(1)]);
}

#[test]
fn preserves_a_non_last_use_in_the_tail() {
    opts().last_uses([1, 3]).assert([1, 2, 3], [2, 1, 3], [Dup(1), Swap(3), Swap(2)]);
}

#[test]
fn spills_until_a_push_is_in_reach() {
    opts().max_swap_depth(2).assert([9, 8, 1], [1], [store(0), Dup(1)]);
}

#[test]
fn pops_instead_of_spilling_an_already_spilled_value() {
    opts().max_swap_depth(1).spilled([9]).assert([9, 1], [1], [Pop, Dup(0)]);
}

#[test]
fn spills_an_unreachable_swap_top() {
    opts().max_swap_depth(1).last_uses([1]).assert([9, 8, 1], [1], [store(0), Swap(1)]);
}

#[test]
fn spill_and_rebuild_correctly_when_swap_unreachable() {
    opts().max_swap_depth(1).spilled([3]).assert(
        [2, 3],
        [2, 2, 3],
        [load(0), Pop, Dup(0), load(0), Swap(1), Dup(0)],
    );
}

#[test]
fn spill_and_rebuild_when_already_preserved_on_swap_unreachable() {
    opts().max_swap_depth(1).spilled([0]).assert(
        [0, 1, 2, 3],
        [2, 0],
        [Dup(0), Pop, Pop, store(1), Dup(0), load(0), Swap(1)],
    );
}

#[test]
fn everything_but_preserve_correct_requiring_spill() {
    opts().max_swap_depth(2).last_uses([0, 5]).spilled([5]).assert(
        [0, 1, 2, 3, 4, 5, 6],
        [5, 1, 0, 5],
        [
            Dup(1),
            load(0),
            Pop,
            store(1),
            store(2),
            Pop,
            store(3),
            store(4),
            store(5),
            Pop,
            load(0),
            load(2),
            load(1),
            load(0),
        ],
    );
}

#[derive(Debug, Clone, Copy)]
struct RawValue {
    is_on_stack: bool,
    is_spilled: bool,
    stack_order: u16,
    is_last_use: bool,
}

fn raw_value() -> impl Strategy<Value = RawValue> {
    (0u8..3, any::<u16>(), any::<bool>()).prop_map(|(placement, stack_order, is_last_use)| {
        RawValue {
            is_on_stack: placement <= 1,
            is_spilled: placement >= 1,
            stack_order,
            is_last_use,
        }
    })
}

fn generated_schedule() -> impl Strategy<Value = (u8, Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>)> {
    (prop::collection::vec(raw_value(), 1..32), 1u8..=24)
        .prop_flat_map(|(values, max_swap_depth)| {
            let value_len = u32::try_from(values.len()).unwrap();
            (Just(values), prop::collection::vec(0..value_len, 0..32), Just(max_swap_depth))
        })
        .prop_map(|(values, target, max_swap_depth)| {
            let value_len = u32::try_from(values.len()).unwrap();
            let mut stack: Vec<u32> =
                (0..value_len).filter(|&i| values[i as usize].is_on_stack).collect();
            stack.sort_by_key(|&i| values[i as usize].stack_order);

            let spilled = (0..value_len).filter(|&i| values[i as usize].is_spilled).collect();
            let last_uses = (0..value_len)
                .filter(|&i| values[i as usize].is_last_use && target.contains(&i))
                .collect();

            (max_swap_depth, last_uses, spilled, stack, target)
        })
}

proptest! {
    #[test]
    fn generated_operand_schedules_are_correct(
        (max_swap_depth, last_uses, spilled, stack, target) in generated_schedule(),
    ) {
        let config = ShuffleConfig::max_swap_no_exchange(max_swap_depth);
        assert_intra_op_schedule_exists(config, stack, spilled, target, last_uses);
    }
}
