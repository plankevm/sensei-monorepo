use std::collections::{HashSet, VecDeque};

use crate::{
    BlockFinalization,
    depth_first_search::{self, SearchConfig, SearchResult},
    greedy_intra_op_scheduler::greedy_schedule_op,
    greedy_shuffler,
    op_graph::{BitsetWord, OpGraph, OpNodeId, OpNodeKind, OpSetMut, ValueNodeId},
    stack::{EvmStack, ShuffleConfig, StackOps, TrackedStack},
    treegraph::build_tree_graph,
    validation,
};
use plank_core::{DenseIndexSet, Idx, IndexVec};
use sir_data::{OperationIdx, StaticAllocId};
use smallvec::SmallVec;

const SCRATCH_OP_SET_INLINE_CAPACITY: usize = 512 / BitsetWord::BITS as usize;

#[derive(Clone, Copy, Debug)]
pub(crate) enum GreedyPolicy {
    First,
    Last,
    Cheapest,
    CheapestLast,
    MostExpensive,
    MostExpensiveLast,
    OutputsBottomUp,
    OutputsBottomUpExpensive,
    OutputsBottomUpLast,
    OutputsTopDown,
    OutputsTopDownExpensive,
    Scrambled(u32),
    CheapestScrambled(u32),
    OutputsBottomUpScrambled(u32),
    HighestArityScrambled(u32),
    HighestArity,
    HighestArityLast,
}

pub fn schedule(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    mut search: SearchConfig,
    graph: &OpGraph,
) -> SearchResult {
    let (zero_arity_count, unary_count, binary_count, high_arity_count, total_arity) =
        graph.op_ids().fold((0, 0, 0, 0, 0), |(zero, unary, binary, high, total), operation| {
            let arity = graph.get_op(operation).inputs_fifo.len();
            (
                zero + usize::from(arity == 0),
                unary + usize::from(arity == 1),
                binary + usize::from(arity == 2),
                high + usize::from(arity >= 3),
                total + arity,
            )
        });
    let mut uses = IndexVec::<ValueNodeId, u32>::from_vec(vec![0; graph.total_values() as usize]);
    for operation in graph.op_ids() {
        for &input in graph.get_op(operation).inputs_fifo {
            uses[input] += 1;
        }
    }
    for &output in graph.output_values_fifo() {
        uses[output] += 1;
    }
    let max_uses = uses.iter().copied().max().unwrap_or(0);
    let excess_uses = uses.iter().map(|uses| uses.saturating_sub(1)).sum::<u32>();
    search.alignment_factor = if zero_arity_count <= 14 && excess_uses >= 2 {
        6
    } else if graph.input_values_fifo().len() >= 7 && binary_count <= 8 {
        4
    } else {
        5
    };
    search.arity_factor =
        if graph.input_values_fifo().len() >= 9 && unary_count >= 1 { 5 } else { 3 };
    search.layout_alignment_factor = if graph.total_ops() >= 33 && zero_arity_count <= 18 {
        3
    } else if graph.total_ops() <= 32 && graph.output_values_fifo().len() >= 8 {
        1
    } else {
        2
    };
    search.copy_all_inputs = (unary_count <= 1 && high_arity_count >= 2)
        || (binary_count <= 10 && high_arity_count >= 4)
        || (graph.total_ops() >= 23 && total_arity <= 24)
        || (max_uses >= 11 && excess_uses <= 15)
        || (zero_arity_count <= 7 && max_uses >= 5);
    let trees = build_tree_graph(graph);
    let compare_original = trees.graph.total_ops() != graph.total_ops()
        && (graph.total_ops() <= 13
            || (graph.total_ops() == 14
                && trees.graph.total_ops() <= 4
                && graph.input_values_fifo().len() <= 5));
    let (mut result, original_result) = if compare_original {
        let (tree_result, original_result) = rayon::join(
            || {
                depth_first_search::schedule(
                    finalization,
                    next_alloc_id,
                    shuffle,
                    search,
                    &trees.graph,
                )
            },
            || depth_first_search::schedule(finalization, next_alloc_id, shuffle, search, graph),
        );
        (tree_result, Some(original_result))
    } else {
        (
            depth_first_search::schedule(
                finalization,
                next_alloc_id,
                shuffle,
                search,
                &trees.graph,
            ),
            None,
        )
    };
    result.ops = trees.expand_schedule(graph, &result.ops);
    finalize_result(&mut result, graph, next_alloc_id, shuffle);
    if let Some(mut original_result) = original_result {
        finalize_result(&mut original_result, graph, next_alloc_id, shuffle);
        result.candidate_limit_reached |= original_result.candidate_limit_reached;
        if crate::stack::gas_cost(&original_result.ops, shuffle)
            < crate::stack::gas_cost(&result.ops, shuffle)
        {
            result.ops = original_result.ops;
            result.spill_count = original_result.spill_count;
        }
    }
    let validated_next_alloc =
        validation::validate(graph, finalization, shuffle, next_alloc_id, &result.ops)
            .unwrap_or_else(|error| {
                panic!("stack scheduler produced an invalid schedule: {error}")
            });
    assert_eq!(
        validated_next_alloc - next_alloc_id,
        result.spill_count,
        "stack scheduler reported an incorrect spill count"
    );
    result
}

fn finalize_result(
    result: &mut SearchResult,
    graph: &OpGraph,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
) {
    let simplify = |ops| {
        simplify_stack_ops(ops, shuffle.max_swap_depth, shuffle.max_dup_depth, |operation| {
            graph.op_ids().any(|candidate| {
                    matches!(graph.get_op(candidate).kind, OpNodeKind::Flippable(index) if index == operation)
                })
        })
    };
    let ops = simplify(std::mem::take(&mut result.ops));
    if result.spill_count == 0 {
        result.ops = ops;
        return;
    }
    let loaded = ops
        .iter()
        .filter_map(|operation| match operation {
            StackOps::Load(allocation) => Some(*allocation),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut allocations = hashbrown::HashMap::new();
    let mut next_retained_alloc_id = next_alloc_id;
    let mut retained_spill_count = 0;
    let mut without_unused_spills = Vec::with_capacity(ops.len());
    for operation in ops {
        match operation {
            StackOps::Store(allocation) if loaded.contains(&allocation) => {
                allocations.insert(allocation, next_retained_alloc_id);
                without_unused_spills.push(StackOps::Store(next_retained_alloc_id));
                next_retained_alloc_id += 1;
                retained_spill_count += 1;
            }
            StackOps::Store(_) => without_unused_spills.push(StackOps::Pop),
            StackOps::Load(allocation) => without_unused_spills.push(StackOps::Load(
                *allocations.get(&allocation).expect("load precedes its retained store"),
            )),
            operation => without_unused_spills.push(operation),
        }
    }
    result.ops = simplify(without_unused_spills.into_boxed_slice());
    result.spill_count = retained_spill_count;
}

pub(crate) fn simplify_stack_ops(
    ops: Box<[StackOps]>,
    max_swap_depth: u8,
    max_dup_depth: u8,
    is_flippable: impl Fn(OperationIdx) -> bool,
) -> Box<[StackOps]> {
    let mut simplified = Vec::with_capacity(ops.len());
    for operation in ops {
        let operation = match operation {
            StackOps::Op(operation)
                if simplified.last() == Some(&StackOps::Swap(1)) && is_flippable(operation) =>
            {
                simplified.pop();
                StackOps::Flipped(operation)
            }
            StackOps::Flipped(operation) if simplified.last() == Some(&StackOps::Swap(1)) => {
                simplified.pop();
                StackOps::Op(operation)
            }
            operation => operation,
        };
        if let StackOps::Swap(depth) = operation
            && depth >= 2
            && let [.., StackOps::Swap(previous), StackOps::Dup(0)] = simplified.as_slice()
            && usize::from(*previous) + 1 == usize::from(depth)
            && *previous <= max_dup_depth
        {
            let duplicated = *previous;
            simplified.truncate(simplified.len() - 2);
            simplified.push(StackOps::Dup(duplicated));
            simplified.push(StackOps::Swap(1));
            continue;
        }
        if let StackOps::Swap(depth) = operation
            && let [.., StackOps::Swap(previous), StackOps::Pop, StackOps::Dup(0)] =
                simplified.as_slice()
            && *previous == depth
            && depth < max_swap_depth
            && max_dup_depth >= 1
        {
            simplified.truncate(simplified.len() - 3);
            simplified.push(StackOps::Dup(1));
            simplified.push(StackOps::Swap(depth + 1));
            simplified.push(StackOps::Pop);
            continue;
        }
        if operation == StackOps::Swap(1)
            && let [.., StackOps::Swap(first), StackOps::Swap(second), StackOps::Dup(duplicated)] =
                simplified.as_slice()
            && first == duplicated
            && *first < max_swap_depth
            && *second < max_swap_depth
        {
            let first = *first;
            let second = *second;
            simplified.truncate(simplified.len() - 3);
            simplified.push(StackOps::Dup(0));
            simplified.push(StackOps::Swap(first + 1));
            simplified.push(StackOps::Swap(second + 1));
            continue;
        }
        if operation == StackOps::Swap(1)
            && let Some(StackOps::Dup(duplicated)) = simplified.last()
            && *duplicated < max_swap_depth
        {
            let duplicated = *duplicated;
            let swap_end = simplified.len() - 1;
            let swap_begin = simplified[..swap_end]
                .iter()
                .rposition(|operation| !matches!(operation, StackOps::Swap(_)))
                .map_or(0, |position| position + 1);
            let chain_start = simplified[swap_begin..swap_end]
                .iter()
                .rposition(|operation| *operation == StackOps::Swap(duplicated))
                .map(|position| swap_begin + position);
            if let Some(chain_start) = chain_start
                && simplified[chain_start..swap_end].iter().enumerate().all(
                    |(offset, operation)| {
                        u8::try_from(offset)
                            .ok()
                            .and_then(|offset| duplicated.checked_sub(offset))
                            .is_some_and(|depth| *operation == StackOps::Swap(depth))
                    },
                )
            {
                let chain_len = swap_end - chain_start;
                simplified.truncate(chain_start);
                simplified.push(StackOps::Dup(0));
                for offset in 0..chain_len {
                    simplified.push(StackOps::Swap(
                        duplicated + 1
                            - u8::try_from(offset).expect("swap chain length exceeds u8"),
                    ));
                }
                continue;
            }
        }
        if operation == StackOps::Swap(1)
            && let [.., StackOps::Swap(1), StackOps::Pop, StackOps::Dup(duplicated)] =
                simplified.as_slice()
            && *duplicated < max_dup_depth
            && max_swap_depth >= 2
        {
            let duplicated = *duplicated;
            simplified.truncate(simplified.len() - 3);
            simplified.push(StackOps::Dup(duplicated + 1));
            simplified.push(StackOps::Swap(2));
            simplified.push(StackOps::Pop);
            continue;
        }
        if operation == StackOps::Swap(1)
            && let [.., StackOps::Dup(first), StackOps::Swap(middle), StackOps::Dup(second)] =
                simplified.as_slice()
            && *second >= 1
            && second != middle
            && *first < max_dup_depth
            && *middle < max_swap_depth
        {
            let first = *first;
            let middle = *middle;
            let second = *second;
            simplified.truncate(simplified.len() - 3);
            simplified.push(StackOps::Dup(second - 1));
            simplified.push(StackOps::Dup(first + 1));
            simplified.push(StackOps::Swap(middle + 1));
            continue;
        }
        let is_redundant = matches!(
            (simplified.last(), operation),
            (Some(StackOps::Dup(duplicated)), StackOps::Swap(swapped))
                if usize::from(*duplicated) + 1 == usize::from(swapped)
        );
        if is_redundant {
            continue;
        }
        let cancels_previous = matches!(
            (simplified.last(), operation),
            (Some(StackOps::Swap(previous)), StackOps::Swap(current)) if *previous == current
        ) || matches!(
            (simplified.last(), operation),
            (Some(StackOps::Dup(_) | StackOps::Load(_)), StackOps::Pop)
        );
        if cancels_previous {
            simplified.pop();
        } else if operation == StackOps::Pop
            && let [.., StackOps::Dup(0), StackOps::Store(allocation)] = simplified.as_slice()
        {
            let allocation = *allocation;
            simplified.pop();
            simplified.pop();
            simplified.push(StackOps::Store(allocation));
        } else if let (Some(StackOps::Store(stored)), StackOps::Load(loaded)) =
            (simplified.last(), operation)
            && stored == &loaded
        {
            simplified.pop();
            simplified.push(StackOps::Dup(0));
            simplified.push(StackOps::Store(loaded));
        } else {
            simplified.push(operation);
        }
    }
    let simplified = simplify_stack_runs(simplified, max_swap_depth);
    simplify_dup_runs(simplified, max_swap_depth, max_dup_depth).into_boxed_slice()
}

fn shorter_dup_run(
    run: &[StackOps],
    initial: &[usize],
    target: &[usize],
    max_swap_depth: usize,
    max_dup_depth: usize,
) -> Option<Vec<StackOps>> {
    const MAX_STATES: usize = 2_000;

    let mut seen = HashSet::new();
    seen.insert(target.to_vec());
    let mut queue = VecDeque::from([(target.to_vec(), Vec::new())]);
    while let Some((state, reverse_operations)) = queue.pop_front() {
        if reverse_operations.len() + 1 >= run.len() {
            continue;
        }
        let mut predecessors = Vec::new();
        if state.len() >= 2 {
            for depth in 0..=state.len().saturating_sub(2).min(max_dup_depth) {
                if state[0] == state[depth + 1] {
                    let mut predecessor = state.clone();
                    predecessor.remove(0);
                    predecessors.push((predecessor, StackOps::Dup(u8::try_from(depth).ok()?)));
                }
            }
        }
        for &value in initial {
            if !state.contains(&value) {
                let mut predecessor = Vec::with_capacity(state.len() + 1);
                predecessor.push(value);
                predecessor.extend_from_slice(&state);
                predecessors.push((predecessor, StackOps::Pop));
            }
        }
        for depth in 1..state.len().min(max_swap_depth + 1) {
            let mut predecessor = state.clone();
            predecessor.swap(0, depth);
            predecessors.push((predecessor, StackOps::Swap(u8::try_from(depth).ok()?)));
        }
        for (predecessor, operation) in predecessors {
            if predecessor == initial {
                let mut operations = reverse_operations.clone();
                operations.push(operation);
                operations.reverse();
                return Some(operations);
            }
            if seen.len() == MAX_STATES || !seen.insert(predecessor.clone()) {
                continue;
            }
            let mut operations = reverse_operations.clone();
            operations.push(operation);
            queue.push_back((predecessor, operations));
        }
    }
    None
}

fn single_dup_candidate(
    initial: &[usize],
    target: &[usize],
    max_swap_depth: usize,
    max_dup_depth: usize,
) -> Option<Vec<StackOps>> {
    let duplicated = initial
        .iter()
        .copied()
        .find(|value| target.iter().filter(|candidate| candidate == &value).count() == 2)?;
    if duplicated > max_dup_depth {
        return None;
    }
    let duplicate_label = initial.len();
    let current =
        std::iter::once(duplicate_label).chain(initial.iter().copied()).collect::<Vec<_>>();
    let mut best = None;
    for labeled_occurrence in 0..2 {
        let mut seen = 0;
        let labeled_target = target
            .iter()
            .map(|&value| {
                if value != duplicated {
                    return value;
                }
                let label = if seen == labeled_occurrence { duplicate_label } else { value };
                seen += 1;
                label
            })
            .collect::<Vec<_>>();
        let Some(swaps) = canonical_swaps(current.clone(), &labeled_target, max_swap_depth) else {
            continue;
        };
        let mut operations = Vec::with_capacity(swaps.len() + 1);
        operations.push(StackOps::Dup(u8::try_from(duplicated).ok()?));
        operations.extend(swaps);
        if best.as_ref().is_none_or(|current: &Vec<_>| operations.len() < current.len()) {
            best = Some(operations);
        }
    }
    best
}

fn simplify_dup_runs(
    operations: Vec<StackOps>,
    max_swap_depth: u8,
    max_dup_depth: u8,
) -> Vec<StackOps> {
    let mut result = Vec::with_capacity(operations.len());
    let mut remaining = operations.as_slice();
    while let Some((&operation, tail)) = remaining.split_first() {
        if !matches!(operation, StackOps::Swap(_) | StackOps::Dup(_) | StackOps::Pop) {
            result.push(operation);
            remaining = tail;
            continue;
        }
        let run_length = remaining
            .iter()
            .take_while(|operation| {
                matches!(operation, StackOps::Swap(_) | StackOps::Dup(_) | StackOps::Pop)
            })
            .count();
        let run = &remaining[..run_length];
        let dup_count =
            run.iter().filter(|operation| matches!(operation, StackOps::Dup(_))).count();
        if dup_count == 0 {
            result.extend_from_slice(run);
            remaining = &remaining[run_length..];
            continue;
        }

        let mut required_len = 0_isize;
        let mut stack_delta = 0_isize;
        for operation in run {
            let accessed = match operation {
                StackOps::Swap(depth) | StackOps::Dup(depth) => isize::from(*depth) + 1,
                StackOps::Pop => 1,
                _ => unreachable!("stack run contains an unsupported operation"),
            };
            required_len = required_len.max(accessed - stack_delta);
            stack_delta += match operation {
                StackOps::Dup(_) => 1,
                StackOps::Pop => -1,
                StackOps::Swap(_) => 0,
                _ => unreachable!("stack run contains an unsupported operation"),
            };
        }
        let initial = (0..usize::try_from(required_len)
            .expect("required stack length is negative"))
            .collect::<Vec<_>>();
        let mut target = initial.clone();
        for operation in run {
            match operation {
                StackOps::Swap(depth) => target.swap(0, usize::from(*depth)),
                StackOps::Dup(depth) => target.insert(0, target[usize::from(*depth)]),
                StackOps::Pop => {
                    target.remove(0);
                }
                _ => unreachable!("stack run contains an unsupported operation"),
            }
        }
        let has_pop = run.iter().any(|operation| matches!(operation, StackOps::Pop));
        let direct = (dup_count == 1 && !has_pop)
            .then(|| {
                single_dup_candidate(
                    &initial,
                    &target,
                    usize::from(max_swap_depth),
                    usize::from(max_dup_depth),
                )
            })
            .flatten();
        let shorter = direct.filter(|candidate| candidate.len() < run.len()).or_else(|| {
            (run_length <= 7)
                .then(|| {
                    shorter_dup_run(
                        run,
                        &initial,
                        &target,
                        usize::from(max_swap_depth),
                        usize::from(max_dup_depth),
                    )
                })
                .flatten()
        });
        if let Some(shorter) = shorter {
            result.extend(shorter);
        } else {
            result.extend_from_slice(run);
        }
        remaining = &remaining[run_length..];
    }
    result
}

fn canonical_swaps(
    mut current: Vec<usize>,
    target: &[usize],
    max_swap_depth: usize,
) -> Option<Vec<StackOps>> {
    let mut operations = Vec::new();
    while current != target {
        let mut destination = target
            .iter()
            .position(|&position| position == current[0])
            .expect("stack permutation lost a position");
        if destination == 0 {
            destination = (1..current.len())
                .find(|&position| current[position] != target[position])
                .expect("stack permutation mismatch disappeared");
        }
        if destination > max_swap_depth {
            return None;
        }
        let depth = u8::try_from(destination).ok()?;
        current.swap(0, destination);
        operations.push(StackOps::Swap(depth));
    }
    Some(operations)
}

fn search_stack_run(
    current: Vec<usize>,
    target: &[usize],
    removed: &mut Vec<usize>,
    operations: &mut Vec<StackOps>,
    best: &mut Vec<StackOps>,
    max_swap_depth: usize,
) {
    if operations.len() + removed.len() >= best.len() {
        return;
    }
    if removed.is_empty() {
        let Some(swaps) = canonical_swaps(current, target, max_swap_depth) else {
            return;
        };
        if operations.len() + swaps.len() < best.len() {
            best.clear();
            best.extend_from_slice(operations);
            best.extend(swaps);
        }
        return;
    }

    for index in (0..removed.len()).rev() {
        let removed_value = removed.swap_remove(index);
        let depth = current
            .iter()
            .position(|&value| value == removed_value)
            .expect("removed stack value disappeared");
        if depth <= max_swap_depth {
            let mut next = current.clone();
            let operation_count = operations.len();
            if depth > 0 {
                next.swap(0, depth);
                operations.push(StackOps::Swap(
                    u8::try_from(depth).expect("checked stack depth exceeds u8"),
                ));
            }
            next.remove(0);
            operations.push(StackOps::Pop);
            search_stack_run(next, target, removed, operations, best, max_swap_depth);
            operations.truncate(operation_count);
        }
        removed.push(removed_value);
        let last = removed.len() - 1;
        removed.swap(index, last);
    }
}

fn simplify_stack_runs(operations: Vec<StackOps>, max_swap_depth: u8) -> Vec<StackOps> {
    let mut result = Vec::with_capacity(operations.len());
    let mut remaining = operations.as_slice();
    while let Some((&operation, tail)) = remaining.split_first() {
        if !matches!(operation, StackOps::Swap(_) | StackOps::Pop) {
            result.push(operation);
            remaining = tail;
            continue;
        }
        let run_length = remaining
            .iter()
            .take_while(|operation| matches!(operation, StackOps::Swap(_) | StackOps::Pop))
            .count();
        let run = &remaining[..run_length];
        let mut removed_count = 0;
        let mut required_len = 0;
        for operation in run {
            match operation {
                StackOps::Swap(depth) => {
                    required_len = required_len.max(removed_count + usize::from(*depth) + 1);
                }
                StackOps::Pop => {
                    removed_count += 1;
                    required_len = required_len.max(removed_count);
                }
                _ => unreachable!("stack run contains an unsupported operation"),
            }
        }
        // Keep exhaustive deletion-order search bounded for long cleanup sequences.
        if removed_count > 6 {
            result.extend_from_slice(run);
            remaining = &remaining[run_length..];
            continue;
        }

        let initial = (0..required_len).collect::<Vec<_>>();
        let mut target = initial.clone();
        for operation in run {
            match operation {
                StackOps::Swap(depth) => target.swap(0, usize::from(*depth)),
                StackOps::Pop => {
                    target.remove(0);
                }
                _ => unreachable!("stack run contains an unsupported operation"),
            }
        }
        let mut removed =
            initial.iter().copied().filter(|value| !target.contains(value)).collect::<Vec<_>>();
        let mut best = run.to_vec();
        search_stack_run(
            initial,
            &target,
            &mut removed,
            &mut Vec::new(),
            &mut best,
            usize::from(max_swap_depth),
        );
        result.extend(best);
        remaining = &remaining[run_length..];
    }
    result
}

fn output_priority(graph: &OpGraph, operation: OpNodeId) -> usize {
    let mut pending = graph.get_op(operation).outputs_fifo.to_vec();
    let mut seen = DenseIndexSet::with_capacity_in_bits(graph.total_values() as usize);
    let mut best = 0;
    while let Some(value) = pending.pop() {
        if !seen.add(value) {
            continue;
        }
        if let Some(position) =
            graph.output_values_fifo().iter().position(|&output| output == value)
        {
            best = best.max(position + 1);
        }
        for consumer in graph.get_consumers(value).iter() {
            pending.extend_from_slice(graph.get_op(consumer).outputs_fifo);
        }
    }
    best
}

fn scrambled_priority(operation: OpNodeId, seed: u32) -> u32 {
    let value = u32::try_from(operation.idx()).expect("operation index exceeds u32") ^ seed;
    let value = (value ^ (value >> 16)).wrapping_mul(0x7feb_352d);
    let value = (value ^ (value >> 15)).wrapping_mul(0x846c_a68b);
    value ^ (value >> 16)
}

pub fn greedy_schedule(
    ops_sink: impl FnMut(StackOps),
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    config: ShuffleConfig,
    graph: &OpGraph,
    policy: GreedyPolicy,
) -> StaticAllocId {
    let mut completable_backing = SmallVec::<[BitsetWord; SCRATCH_OP_SET_INLINE_CAPACITY]>::new();
    completable_backing.resize(graph.words_per_set() as usize, 0);
    let mut completable = OpSetMut::new(&mut completable_backing, graph.total_ops());

    let mut complete_backing = SmallVec::<[BitsetWord; SCRATCH_OP_SET_INLINE_CAPACITY]>::new();
    complete_backing.resize(graph.words_per_set() as usize, 0);
    let mut complete = OpSetMut::new(&mut complete_backing, graph.total_ops());

    let mut stack = {
        let mut inner = EvmStack::new();
        for input in graph.input_values_fifo().iter().rev() {
            inner.push(input);
        }
        TrackedStack::new_from_evm(next_alloc_id, ops_sink, inner, 8)
    };

    'schedule: loop {
        completable.clear();
        graph.collect_next_completable_into(complete.as_ref(), &mut completable);
        let mut best = None;
        for op in completable.iter() {
            let mut normal_ops = Vec::new();
            let mut normal_stack = stack.clone_with(|op| normal_ops.push(op));
            greedy_schedule_op(config, &mut normal_stack, graph, op, complete.as_ref(), false);
            let normal_cost = crate::stack::gas_cost(&normal_ops, config);

            let (cost, flipped) = if matches!(graph.get_op(op).kind, OpNodeKind::Flippable(_)) {
                let mut flipped_ops = Vec::new();
                let mut flipped_stack = stack.clone_with(|op| flipped_ops.push(op));
                greedy_schedule_op(config, &mut flipped_stack, graph, op, complete.as_ref(), true);
                let flipped_cost = crate::stack::gas_cost(&flipped_ops, config);
                if flipped_cost < normal_cost { (flipped_cost, true) } else { (normal_cost, false) }
            } else {
                (normal_cost, false)
            };
            let output_priority = output_priority(graph, op);
            let better = best.is_none_or(|(best_cost, best_op, _, best_priority)| match policy {
                GreedyPolicy::First => false,
                GreedyPolicy::Last => true,
                GreedyPolicy::Cheapest => cost < best_cost,
                GreedyPolicy::CheapestLast => cost <= best_cost,
                GreedyPolicy::MostExpensive => cost > best_cost,
                GreedyPolicy::MostExpensiveLast => cost >= best_cost,
                GreedyPolicy::OutputsBottomUp => {
                    (output_priority, std::cmp::Reverse(cost))
                        > (best_priority, std::cmp::Reverse(best_cost))
                }
                GreedyPolicy::OutputsBottomUpExpensive => {
                    (output_priority, cost) > (best_priority, best_cost)
                }
                GreedyPolicy::OutputsBottomUpLast => {
                    (output_priority, std::cmp::Reverse(cost))
                        >= (best_priority, std::cmp::Reverse(best_cost))
                }
                GreedyPolicy::OutputsTopDown => {
                    (std::cmp::Reverse(output_priority), std::cmp::Reverse(cost))
                        > (std::cmp::Reverse(best_priority), std::cmp::Reverse(best_cost))
                }
                GreedyPolicy::OutputsTopDownExpensive => {
                    (std::cmp::Reverse(output_priority), cost)
                        > (std::cmp::Reverse(best_priority), best_cost)
                }
                GreedyPolicy::Scrambled(seed) => {
                    scrambled_priority(op, seed) > scrambled_priority(best_op, seed)
                }
                GreedyPolicy::CheapestScrambled(seed) => {
                    (std::cmp::Reverse(cost), scrambled_priority(op, seed))
                        > (std::cmp::Reverse(best_cost), scrambled_priority(best_op, seed))
                }
                GreedyPolicy::OutputsBottomUpScrambled(seed) => {
                    (output_priority, std::cmp::Reverse(cost), scrambled_priority(op, seed))
                        > (
                            best_priority,
                            std::cmp::Reverse(best_cost),
                            scrambled_priority(best_op, seed),
                        )
                }
                GreedyPolicy::HighestArityScrambled(seed) => {
                    (
                        graph.get_op(op).inputs_fifo.len(),
                        std::cmp::Reverse(cost),
                        scrambled_priority(op, seed),
                    ) > (
                        graph.get_op(best_op).inputs_fifo.len(),
                        std::cmp::Reverse(best_cost),
                        scrambled_priority(best_op, seed),
                    )
                }
                GreedyPolicy::HighestArity => {
                    (graph.get_op(op).inputs_fifo.len(), std::cmp::Reverse(cost))
                        > (graph.get_op(best_op).inputs_fifo.len(), std::cmp::Reverse(best_cost))
                }
                GreedyPolicy::HighestArityLast => {
                    (graph.get_op(op).inputs_fifo.len(), std::cmp::Reverse(cost))
                        >= (graph.get_op(best_op).inputs_fifo.len(), std::cmp::Reverse(best_cost))
                }
            });
            if better {
                best = Some((cost, op, flipped, output_priority));
            }
            if matches!(policy, GreedyPolicy::First) {
                break;
            }
        }
        let Some((_, op, flipped, _)) = best else {
            break 'schedule;
        };
        greedy_schedule_op(config, &mut stack, graph, op, complete.as_ref(), flipped);
        complete.add(op);
    }

    if finalization == BlockFinalization::ShuffleToOutputs {
        greedy_shuffler::shuffle(config, &mut stack, graph);
    }

    stack.into_next_alloc_id()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op_graph::OpGraphBuilder;
    use plank_core::Idx;

    #[test]
    fn removes_and_renumbers_unused_spills() {
        let graph = OpGraphBuilder::with_capacity(0, 0)
            .end_inputs_begin_ops()
            .end_ops_begin_end_stack()
            .finish();
        let mut result = SearchResult {
            ops: Box::new([
                StackOps::Store(StaticAllocId::ZERO),
                StackOps::Store(StaticAllocId::ZERO + 1),
                StackOps::Load(StaticAllocId::ZERO + 1),
            ]),
            spill_count: 2,
            candidate_limit_reached: false,
        };

        finalize_result(&mut result, &graph, StaticAllocId::ZERO, ShuffleConfig::PRE_AMSTERDAM);

        assert_eq!(result.ops.as_ref(), [StackOps::Pop]);
        assert_eq!(result.spill_count, 0);
    }

    #[test]
    fn simplifies_stack_operation_identities() {
        let first = StaticAllocId::default();
        let second = first + 1;
        let simplified = simplify_stack_ops(
            Box::new([
                StackOps::Swap(2),
                StackOps::Swap(2),
                StackOps::Dup(3),
                StackOps::Pop,
                StackOps::Load(first),
                StackOps::Pop,
                StackOps::Dup(0),
                StackOps::Store(first),
                StackOps::Pop,
                StackOps::Store(second),
                StackOps::Load(second),
            ]),
            16,
            16,
            |_| false,
        );

        assert_eq!(
            simplified.as_ref(),
            [StackOps::Store(first), StackOps::Dup(0), StackOps::Store(second)]
        );
    }

    #[test]
    fn folds_a_swap_into_a_flippable_operation() {
        let operation = OperationIdx::ZERO;
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Swap(1), StackOps::Op(operation)]),
            16,
            16,
            |candidate| candidate == operation,
        );
        let unflipped = simplify_stack_ops(
            Box::new([StackOps::Swap(1), StackOps::Flipped(operation)]),
            16,
            16,
            |_| true,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Flipped(operation)]);
        assert_eq!(unflipped.as_ref(), [StackOps::Op(operation)]);
    }

    #[test]
    fn simplifies_swap_runs_to_their_minimal_permutation() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Swap(1), StackOps::Swap(2), StackOps::Swap(1), StackOps::Swap(2)]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Swap(2), StackOps::Swap(1)]);
    }

    #[test]
    fn moves_a_dup_before_two_arbitrary_swaps() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Swap(7), StackOps::Swap(5), StackOps::Dup(7), StackOps::Swap(1)]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Dup(0), StackOps::Swap(8), StackOps::Swap(6)]);
    }

    #[test]
    fn moves_a_dup_before_a_swap_and_pop() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Swap(1), StackOps::Pop, StackOps::Dup(4), StackOps::Swap(1)]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Dup(5), StackOps::Swap(2), StackOps::Pop]);
    }

    #[test]
    fn moves_a_dup_before_a_pop_and_swap() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Swap(3), StackOps::Pop, StackOps::Dup(0), StackOps::Swap(3)]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Dup(1), StackOps::Swap(4), StackOps::Pop]);
    }

    #[test]
    fn pulls_a_dup_before_a_swap() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Swap(5), StackOps::Dup(0), StackOps::Swap(6)]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Dup(5), StackOps::Swap(1)]);
    }

    #[test]
    fn moves_a_dup_before_a_descending_swap_chain() {
        let simplified = simplify_stack_ops(
            Box::new([
                StackOps::Swap(7),
                StackOps::Swap(6),
                StackOps::Swap(5),
                StackOps::Swap(4),
                StackOps::Dup(7),
                StackOps::Swap(1),
            ]),
            16,
            16,
            |_| false,
        );

        assert_eq!(
            simplified.as_ref(),
            [
                StackOps::Dup(0),
                StackOps::Swap(8),
                StackOps::Swap(7),
                StackOps::Swap(6),
                StackOps::Swap(5),
            ]
        );
    }

    #[test]
    fn shortens_interleaved_dups_and_swaps() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Dup(3), StackOps::Swap(1), StackOps::Dup(5), StackOps::Swap(1)]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Dup(4), StackOps::Dup(4), StackOps::Swap(2)]);
    }

    #[test]
    fn shortens_dups_interleaved_by_a_deeper_swap() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Dup(7), StackOps::Swap(3), StackOps::Dup(13), StackOps::Swap(1)]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Dup(12), StackOps::Dup(8), StackOps::Swap(4)]);
    }

    #[test]
    fn removes_a_dup_swap_pop_identity() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Dup(2), StackOps::Swap(3), StackOps::Pop]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), []);
    }

    #[test]
    fn simplifies_interleaved_swaps_and_pops() {
        let simplified = simplify_stack_ops(
            Box::new([StackOps::Swap(1), StackOps::Pop, StackOps::Swap(1), StackOps::Pop]),
            16,
            16,
            |_| false,
        );

        assert_eq!(simplified.as_ref(), [StackOps::Swap(2), StackOps::Pop, StackOps::Pop]);
    }
}
