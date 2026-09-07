use std::{num::NonZero, sync::Arc as Rc};

use hashbrown::HashMap;
use plank_core::{Idx, IndexVec};
use rayon::prelude::*;
use sir_data::StaticAllocId;
use smallvec::SmallVec;

use crate::{
    BlockFinalization,
    greedy_intra_op_scheduler::{
        copy_schedule_op, greedy_schedule_op, greedy_schedule_op_preserving,
    },
    greedy_shuffler,
    op_graph::{BitsetWord, OpGraph, OpNodeId, OpNodeKind, OpSet, OpSetMut, ValueNodeId},
    scheduler::{GreedyPolicy, greedy_schedule},
    stack::{EvmStack, ShuffleConfig, StackOps, TrackedStack},
};

const BASE_COST_FACTOR: u32 = 100;
const SCRATCH_OP_SET_INLINE_CAPACITY: usize = 512 / BitsetWord::BITS as usize;
const ESTIMATED_STACK_OPS_PER_GRAPH_OP: usize = 8;

#[derive(Clone, Copy)]
pub struct SearchConfig {
    pub max_candidates: NonZero<usize>,
    pub(crate) copy_all_inputs: bool,
    pub(crate) alignment_factor: u32,
    pub(crate) arity_factor: u32,
    pub(crate) layout_alignment_factor: u32,
}

pub struct SearchResult {
    pub ops: Box<[StackOps]>,
    pub spill_count: u32,
    pub candidate_limit_reached: bool,
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct SearchState {
    complete: Box<[BitsetWord]>,
    values: Box<[ValueNodeId]>,
    stack_end: usize,
}

struct SearchNode {
    state: Rc<SearchState>,
    completed_count: u32,
    executed_cost: u32,
}

struct Child {
    node: SearchNode,
    transition_ops: Box<[StackOps]>,
    lower_bound: u32,
    priority: u32,
}

struct OrderBeamState {
    complete: Box<[BitsetWord]>,
    values: Box<[ValueNodeId]>,
    stack_end: usize,
    operations: Vec<StackOps>,
    cost: u32,
}

struct BeamState {
    values: Box<[ValueNodeId]>,
    stack_end: usize,
    operations: Vec<StackOps>,
    cost: u32,
}

struct Search<'a> {
    finalization: BlockFinalization,
    graph: &'a OpGraph,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    max_candidates: usize,
    assessed_candidates: usize,
    candidate_limit_reached: bool,
    best_cost: u32,
    best_ops: Box<[StackOps]>,
    best_spill_count: u32,
    path: Vec<StackOps>,
    best_state_costs: HashMap<Rc<SearchState>, u32>,
    allow_tail_swaps: bool,
    copy_all_inputs: bool,
    alignment_factor: u32,
    arity_factor: u32,
}

fn initial_permutation(
    graph: &OpGraph,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    inputs: &[ValueNodeId],
    initial_spill_count: usize,
    sorted_target: &[ValueNodeId],
    rotation: usize,
) -> (SearchNode, Vec<StackOps>) {
    let mut target = sorted_target.to_vec();
    let first_output = target
        .iter()
        .position(|value| graph.output_values_fifo().contains(value))
        .unwrap_or(target.len());
    target[first_output..].rotate_left(rotation);
    let mut stack = inputs[initial_spill_count..].to_vec();
    let mut ops = (0..initial_spill_count)
        .map(|index| {
            StackOps::Store(
                next_alloc_id + u32::try_from(index).expect("initial spill index overflow"),
            )
        })
        .collect::<Vec<_>>();
    while stack != target {
        let destination = target
            .iter()
            .position(|&value| value == stack[0])
            .expect("initial stack permutation lost a value");
        let destination = if destination == 0 {
            (1..stack.len())
                .find(|&position| stack[position] != target[position])
                .expect("permutation mismatch disappeared")
        } else {
            destination
        };
        stack.swap(0, destination);
        ops.push(StackOps::Swap(u8::try_from(destination).expect("swap overflow")));
    }
    let values = stack.into_iter().chain(inputs[..initial_spill_count].iter().copied()).collect();
    (
        SearchNode {
            state: Rc::new(SearchState {
                complete: vec![0; graph.words_per_set() as usize].into_boxed_slice(),
                values,
                stack_end: inputs.len() - initial_spill_count,
            }),
            completed_count: 0,
            executed_cost: stack_ops_cost(&ops, shuffle),
        },
        ops,
    )
}

pub(crate) fn greedy_incumbent(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    graph: &OpGraph,
) -> SearchResult {
    let mut incumbent_ops = Vec::new();
    let incumbent_next_alloc_id = greedy_schedule(
        |op| incumbent_ops.push(op),
        finalization,
        next_alloc_id,
        shuffle,
        graph,
        GreedyPolicy::First,
    );
    let mut incumbent_cost = stack_ops_cost(&incumbent_ops, shuffle);
    let mut incumbent_spill_count = incumbent_next_alloc_id - next_alloc_id;
    if graph.total_ops() <= 1 {
        return SearchResult {
            ops: incumbent_ops.into_boxed_slice(),
            spill_count: incumbent_spill_count,
            candidate_limit_reached: false,
        };
    }

    for policy in [
        GreedyPolicy::Last,
        GreedyPolicy::Cheapest,
        GreedyPolicy::CheapestLast,
        GreedyPolicy::MostExpensive,
        GreedyPolicy::MostExpensiveLast,
        GreedyPolicy::OutputsBottomUp,
        GreedyPolicy::OutputsBottomUpExpensive,
        GreedyPolicy::OutputsBottomUpLast,
        GreedyPolicy::OutputsTopDown,
        GreedyPolicy::OutputsTopDownExpensive,
        GreedyPolicy::HighestArity,
        GreedyPolicy::HighestArityLast,
        GreedyPolicy::CheapestScrambled(0xb7e1_5163),
        GreedyPolicy::OutputsBottomUpScrambled(0xb7e1_5163),
        GreedyPolicy::HighestArityScrambled(0xb7e1_5163),
        GreedyPolicy::Scrambled(0xb7e1_5163),
        GreedyPolicy::Scrambled(0x9e37_79b9),
        GreedyPolicy::Scrambled(0x243f_6a88),
        GreedyPolicy::Scrambled(0x85a3_08d3),
        GreedyPolicy::Scrambled(0x1319_8a2e),
        GreedyPolicy::Scrambled(0x0370_7344),
        GreedyPolicy::Scrambled(0xa409_3822),
        GreedyPolicy::Scrambled(0x299f_31d0),
        GreedyPolicy::Scrambled(0x082e_fa98),
        GreedyPolicy::Scrambled(0xec4e_6c89),
        GreedyPolicy::Scrambled(0x4528_21e6),
        GreedyPolicy::Scrambled(0x38d0_1377),
        GreedyPolicy::Scrambled(0xbe54_66cf),
        GreedyPolicy::Scrambled(0x34e9_0c6c),
        GreedyPolicy::Scrambled(0xc0ac_29b7),
        GreedyPolicy::Scrambled(0xc97c_50dd),
    ] {
        let mut candidate_ops = Vec::new();
        let candidate_alloc_id = greedy_schedule(
            |op| candidate_ops.push(op),
            finalization,
            next_alloc_id,
            shuffle,
            graph,
            policy,
        );
        let candidate_cost = stack_ops_cost(&candidate_ops, shuffle);
        if candidate_cost < incumbent_cost {
            incumbent_ops = candidate_ops;
            incumbent_cost = candidate_cost;
            incumbent_spill_count = candidate_alloc_id - next_alloc_id;
        }
    }

    SearchResult {
        ops: incumbent_ops.into_boxed_slice(),
        spill_count: incumbent_spill_count,
        candidate_limit_reached: false,
    }
}

pub fn schedule(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    config: SearchConfig,
    graph: &OpGraph,
) -> SearchResult {
    let incumbent = greedy_incumbent(finalization, next_alloc_id, shuffle, graph);
    if graph.total_ops() == 0 {
        return incumbent;
    }
    let incumbent_cost = stack_ops_cost(&incumbent.ops, shuffle);
    let incumbent_ops = incumbent.ops.into_vec();
    let incumbent_spill_count = incumbent.spill_count;

    let inputs = graph.input_values_fifo().iter().collect::<Vec<_>>();
    let initial_spill_count = inputs.len().saturating_sub(usize::from(shuffle.max_swap_depth) + 1);
    let mut initial_ops = (0..initial_spill_count)
        .map(|index| {
            StackOps::Store(
                next_alloc_id + u32::try_from(index).expect("initial spill index overflow"),
            )
        })
        .collect::<Vec<_>>();
    let mut stack = inputs[initial_spill_count..].to_vec();
    let should_permute = inputs.len() >= 2;
    let unpermuted_values =
        stack.iter().chain(inputs[..initial_spill_count].iter()).copied().collect::<Box<_>>();
    let mut alternate_starts = Vec::new();
    if should_permute {
        let mut target = stack.clone();
        target.sort_by_key(|&value| {
            if let Some(position) = graph
                .output_values_fifo()
                .iter()
                .enumerate()
                .filter_map(|(position, output)| (*output == value).then_some(position))
                .next_back()
            {
                (1, position, 0)
            } else {
                let consumers = graph.get_consumers(value);
                let (operation_position, input_position) = consumers
                    .iter()
                    .last()
                    .map(|operation| {
                        let input_position = graph
                            .get_op(operation)
                            .inputs_fifo
                            .iter()
                            .rposition(|&input| input == value)
                            .expect("consumer does not use its consumed value");
                        (operation.idx(), input_position)
                    })
                    .unwrap_or((usize::MAX, 0));
                (0, operation_position, input_position)
            }
        });
        let first_output = target
            .iter()
            .position(|value| graph.output_values_fifo().contains(value))
            .unwrap_or(target.len());
        let output_count = target.len() - first_output;
        if output_count > 0 {
            for offset in 1..output_count {
                alternate_starts.push(initial_permutation(
                    graph,
                    next_alloc_id,
                    shuffle,
                    &inputs,
                    initial_spill_count,
                    &target,
                    (initial_spill_count + offset) % output_count,
                ));
            }
            target[first_output..].rotate_left(initial_spill_count % output_count);
        }
        while stack != target {
            let destination = target
                .iter()
                .position(|&value| value == stack[0])
                .expect("initial stack permutation lost a value");
            let destination = if destination == 0 {
                (1..stack.len())
                    .find(|&position| stack[position] != target[position])
                    .expect("permutation mismatch disappeared")
            } else {
                destination
            };
            stack.swap(0, destination);
            initial_ops.push(StackOps::Swap(u8::try_from(destination).expect("swap overflow")));
        }
    }
    alternate_starts.sort_by_key(|(_, ops)| stack_ops_cost(ops, shuffle));
    let values = stack.into_iter().chain(inputs[..initial_spill_count].iter().copied()).collect();
    let start = SearchNode {
        state: Rc::new(SearchState {
            complete: vec![0; graph.words_per_set() as usize].into_boxed_slice(),
            values,
            stack_end: inputs.len() - initial_spill_count,
        }),
        completed_count: 0,
        executed_cost: stack_ops_cost(&initial_ops, shuffle),
    };
    let unpermuted_start = SearchNode {
        state: Rc::new(SearchState {
            complete: vec![0; graph.words_per_set() as usize].into_boxed_slice(),
            values: unpermuted_values,
            stack_end: inputs.len() - initial_spill_count,
        }),
        completed_count: 0,
        executed_cost: stack_ops_cost(&initial_ops[..initial_spill_count], shuffle),
    };
    let max_candidates = config.max_candidates.get();
    let mut search = Search {
        finalization,
        graph,
        next_alloc_id,
        shuffle,
        max_candidates: if should_permute { max_candidates * 4 / 5 } else { max_candidates },
        assessed_candidates: 0,
        candidate_limit_reached: false,
        best_cost: incumbent_cost,
        best_ops: incumbent_ops.into_boxed_slice(),
        best_spill_count: incumbent_spill_count,
        path: {
            let mut path = Vec::with_capacity(
                initial_ops.len() + graph.total_ops() as usize * ESTIMATED_STACK_OPS_PER_GRAPH_OP,
            );
            path.extend_from_slice(&initial_ops);
            path
        },
        best_state_costs: HashMap::new(),
        allow_tail_swaps: false,
        copy_all_inputs: config.copy_all_inputs,
        alignment_factor: config.alignment_factor,
        arity_factor: config.arity_factor,
    };
    let ((_, beam_results), policy_results) = rayon::join(
        || {
            rayon::join(
                || {
                    if !should_permute {
                        search.visit(start);
                    } else {
                        search.path.truncate(initial_spill_count);
                        search.visit(unpermuted_start);
                        search.max_candidates = if alternate_starts.is_empty() {
                            max_candidates
                        } else {
                            max_candidates * 9 / 10
                        };
                        search.path.clear();
                        search.path.extend_from_slice(&initial_ops);
                        search.visit(start);
                        search.max_candidates = max_candidates;
                        for (alternate_start, alternate_ops) in alternate_starts {
                            if search.assessed_candidates == max_candidates {
                                break;
                            }
                            search.path.clear();
                            search.path.extend_from_slice(&alternate_ops);
                            search.visit(alternate_start);
                        }
                    }
                    search.optimize_initial_spills(&inputs, initial_spill_count, 300);
                    search.improve_adjacent_order(100);
                },
                || {
                    rayon::join(
                        || beam_schedule(finalization, next_alloc_id, shuffle, graph, 64, 3),
                        || beam_schedule(finalization, next_alloc_id, shuffle, graph, 56, 0),
                    )
                },
            )
        },
        || {
            policy_candidates(
                finalization,
                next_alloc_id,
                shuffle,
                graph,
                config.layout_alignment_factor,
            )
        },
    );
    for beam_result in [beam_results.0, beam_results.1] {
        let beam_cost = stack_ops_cost(&beam_result.ops, shuffle);
        if beam_cost < search.best_cost {
            search.best_cost = beam_cost;
            search.best_ops = beam_result.ops;
            search.best_spill_count = beam_result.spill_count;
        }
    }
    simplify_result(&mut search.best_ops, graph, shuffle);
    search.best_cost = stack_ops_cost(&search.best_ops, shuffle);
    for policy_result in policy_results {
        let policy_cost = stack_ops_cost(&policy_result.ops, shuffle);
        if policy_cost < search.best_cost {
            search.best_cost = policy_cost;
            search.best_ops = policy_result.ops;
            search.best_spill_count = policy_result.spill_count;
        }
    }
    search.improve_operand_layouts(16);
    search.optimize_tail(4, 5_000);

    SearchResult {
        ops: search.best_ops,
        spill_count: search.best_spill_count,
        candidate_limit_reached: search.candidate_limit_reached,
    }
}

fn policy_candidates(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    graph: &OpGraph,
    layout_alignment_factor: u32,
) -> Vec<SearchResult> {
    if graph.total_ops() < 8 {
        return Vec::new();
    }
    let mut policy_results = (0_u32..69)
        .into_par_iter()
        .map(|iteration| {
            let policy = match iteration {
                0 => GreedyPolicy::First,
                1 => GreedyPolicy::Cheapest,
                2 => GreedyPolicy::OutputsBottomUp,
                _ => {
                    let seed = iteration.wrapping_mul(0x9e37_79b9).wrapping_add(0xd1b5_4a35);
                    if iteration < 54 {
                        GreedyPolicy::Scrambled(seed)
                    } else {
                        match iteration % 3 {
                            0 => GreedyPolicy::CheapestScrambled(seed),
                            1 => GreedyPolicy::HighestArityScrambled(seed),
                            _ => GreedyPolicy::OutputsBottomUpScrambled(seed),
                        }
                    }
                }
            };
            let mut policy_ops = Vec::new();
            let policy_alloc_id = greedy_schedule(
                |operation| policy_ops.push(operation),
                finalization,
                next_alloc_id,
                shuffle,
                graph,
                policy,
            );
            improve_schedule_order(
                finalization,
                next_alloc_id,
                shuffle,
                graph,
                SearchResult {
                    ops: policy_ops.into_boxed_slice(),
                    spill_count: policy_alloc_id - next_alloc_id,
                    candidate_limit_reached: false,
                },
                100,
                2,
            )
        })
        .collect::<Vec<_>>();
    policy_results.sort_unstable_by_key(|result| stack_ops_cost(&result.ops, shuffle));
    policy_results.par_iter_mut().take(2).for_each(|result| {
        simplify_result(&mut result.ops, graph, shuffle);
    });
    policy_results.sort_unstable_by_key(|result| stack_ops_cost(&result.ops, shuffle));
    let mut layout_results = policy_results
        .par_iter()
        .take(31)
        .enumerate()
        .map(|(index, result)| {
            let order = result
                .ops
                .iter()
                .filter_map(|&operation| graph_operation_id(graph, operation))
                .collect::<Vec<_>>();
            let width = if index < 5 {
                32
            } else if index < 28 {
                8
            } else {
                4
            };
            beam_schedule_in_order(
                finalization,
                next_alloc_id,
                shuffle,
                graph,
                &order,
                width,
                if index < 3 {
                    layout_alignment_factor
                } else if index < 8 {
                    4
                } else {
                    [3, 5][index % 2]
                },
                index < 5,
            )
        })
        .collect::<Vec<_>>();
    layout_results.sort_unstable_by_key(|result| stack_ops_cost(&result.ops, shuffle));
    layout_results.par_iter_mut().take(2).for_each(|result| {
        simplify_result(&mut result.ops, graph, shuffle);
    });
    policy_results.extend(layout_results);
    policy_results
}

fn beam_schedule(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    graph: &OpGraph,
    width: usize,
    arity_factor: u32,
) -> SearchResult {
    let inputs = graph.input_values_fifo().iter().collect::<Box<_>>();
    let mut frontier = vec![OrderBeamState {
        complete: vec![0; graph.words_per_set() as usize].into_boxed_slice(),
        stack_end: inputs.len(),
        values: inputs,
        operations: Vec::new(),
        cost: 0,
    }];
    for _ in 0..graph.total_ops() {
        let mut candidates = Vec::new();
        for state in frontier {
            let complete = OpSet::new(&state.complete, graph.total_ops());
            let mut completable_backing = vec![0; graph.words_per_set() as usize];
            let mut completable = OpSetMut::new(&mut completable_backing, graph.total_ops());
            graph.collect_next_completable_into(complete, &mut completable);
            for operation in completable.iter() {
                let operation_view = graph.get_op(operation);
                let can_flip = matches!(operation_view.kind, OpNodeKind::Flippable(_));
                for flipped in [false, true].into_iter().take(1 + usize::from(can_flip)) {
                    let copy_inputs = !operation_view.inputs_fifo.is_empty()
                        && (operation_view.inputs_fifo.len() <= 2
                            || (operation_view.inputs_fifo.len() == 3 && graph.total_ops() <= 20)
                            || ((4..=6).contains(&operation_view.inputs_fifo.len())
                                && graph.total_ops() <= 10));
                    let preserve_inputs = if arity_factor == 0
                        && ((operation_view.inputs_fifo.len() == 2 && graph.total_ops() <= 20)
                            || (operation_view.inputs_fifo.len() == 3 && graph.total_ops() <= 20)
                            || (4..=6).contains(&operation_view.inputs_fifo.len())
                                && graph.total_ops() <= 10)
                    {
                        operation_view
                            .inputs_fifo
                            .iter()
                            .copied()
                            .filter(|&input| graph.is_last_use(complete, input))
                            .collect::<SmallVec<[_; 6]>>()
                    } else {
                        SmallVec::new()
                    };
                    for strategy in 0..1 + usize::from(copy_inputs) + preserve_inputs.len() {
                        let mut transition = Vec::new();
                        let mut stack = TrackedStack::new_from_parts(
                            next_alloc_id,
                            |operation| transition.push(operation),
                            &state.values[..state.stack_end],
                            state.values[state.stack_end..].to_vec(),
                        );
                        if strategy == 0 {
                            greedy_schedule_op(
                                shuffle, &mut stack, graph, operation, complete, flipped,
                            );
                        } else if copy_inputs && strategy == 1 {
                            copy_schedule_op(shuffle, &mut stack, graph, operation, flipped);
                        } else {
                            greedy_schedule_op_preserving(
                                shuffle,
                                &mut stack,
                                graph,
                                operation,
                                complete,
                                flipped,
                                Some(preserve_inputs[strategy - 1 - usize::from(copy_inputs)]),
                            );
                        }
                        let mut next_complete = complete.clone_backing();
                        OpSetMut::new(&mut next_complete, graph.total_ops()).add(operation);
                        let completed = OpSet::new(&next_complete, graph.total_ops());
                        if finalization == BlockFinalization::ShuffleToOutputs {
                            while stack
                                .top()
                                .is_some_and(|value| graph.uses_remaining(completed, value) == 0)
                            {
                                stack.pop();
                            }
                        }
                        let values =
                            [stack.fifo(), stack.underlying_spilled()].concat().into_boxed_slice();
                        let stack_end = stack.fifo().len();
                        drop(stack);
                        let cost = state.cost + stack_ops_cost(&transition, shuffle);
                        let remaining = remaining_cost_lower_bound(
                            &next_complete,
                            &values[..stack_end],
                            &values[stack_end..],
                            finalization == BlockFinalization::ShuffleToOutputs,
                            graph,
                        );
                        let priority = layout_priority(
                            cost,
                            remaining,
                            &values[..stack_end],
                            graph.output_values_fifo(),
                            if arity_factor == 0 { 4 } else { 1 },
                        )
                        .saturating_sub(
                            u32::try_from(operation_view.inputs_fifo.len())
                                .expect("operation arity exceeds u32")
                                * BASE_COST_FACTOR
                                * arity_factor,
                        );
                        let mut operations = state.operations.clone();
                        operations.extend(transition);
                        candidates.push((
                            priority,
                            OrderBeamState {
                                complete: next_complete.into_boxed_slice(),
                                values,
                                stack_end,
                                operations,
                                cost,
                            },
                        ));
                    }
                }
            }
        }
        candidates.sort_unstable_by_key(|(priority, _)| *priority);
        let mut next_frontier = Vec::with_capacity(width);
        for (_, candidate) in candidates {
            if next_frontier.iter().any(|existing: &OrderBeamState| {
                existing.complete == candidate.complete
                    && existing.stack_end == candidate.stack_end
                    && existing.values == candidate.values
            }) {
                continue;
            }
            next_frontier.push(candidate);
            if next_frontier.len() == width {
                break;
            }
        }
        frontier = next_frontier;
    }

    let mut completed = Vec::with_capacity(frontier.len());
    for state in frontier {
        let mut final_operations = Vec::new();
        let mut stack = TrackedStack::new_from_parts(
            next_alloc_id,
            |operation| final_operations.push(operation),
            &state.values[..state.stack_end],
            state.values[state.stack_end..].to_vec(),
        );
        if finalization == BlockFinalization::ShuffleToOutputs {
            greedy_shuffler::shuffle(shuffle, &mut stack, graph);
        }
        let spill_count =
            u32::try_from(stack.underlying_spilled().len()).expect("spill count overflow");
        drop(stack);
        let cost = state.cost + stack_ops_cost(&final_operations, shuffle);
        let mut operations = state.operations;
        operations.extend(final_operations);
        completed.push((cost, operations.into_boxed_slice(), spill_count));
    }
    completed.sort_unstable_by_key(|(cost, _, _)| *cost);
    let mut best = None;
    for (_, mut operations, spill_count) in completed.into_iter().take(2) {
        simplify_result(&mut operations, graph, shuffle);
        let cost = stack_ops_cost(&operations, shuffle);
        if best.as_ref().is_none_or(|(best_cost, _, _)| cost < *best_cost) {
            best = Some((cost, operations, spill_count));
        }
    }
    let (_, ops, spill_count) = best.expect("beam scheduling retained no candidates");
    SearchResult { ops, spill_count, candidate_limit_reached: false }
}

fn beam_schedule_in_order(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    graph: &OpGraph,
    order: &[OpNodeId],
    width: usize,
    alignment_factor: u32,
    allow_copy_inputs: bool,
) -> SearchResult {
    let inputs = graph.input_values_fifo().iter().collect::<Box<_>>();
    let minimum_spill_count = inputs.len().saturating_sub(usize::from(shuffle.max_swap_depth) + 1);
    let maximum_spill_count = if inputs.len() >= 10 {
        (minimum_spill_count + 4).min(inputs.len())
    } else {
        minimum_spill_count
    };
    let mut frontier = Vec::new();
    for spill_count in minimum_spill_count..=maximum_spill_count {
        let initial_operations = (0..spill_count)
            .map(|index| {
                StackOps::Store(
                    next_alloc_id + u32::try_from(index).expect("initial spill index overflow"),
                )
            })
            .collect::<Vec<_>>();
        let initial_stack = inputs[spill_count..].to_vec();
        frontier.push(BeamState {
            stack_end: initial_stack.len(),
            values: initial_stack.iter().chain(&inputs[..spill_count]).copied().collect(),
            cost: stack_ops_cost(&initial_operations, shuffle),
            operations: initial_operations,
        });
    }
    let mut complete_backing = vec![0; graph.words_per_set() as usize];
    for &operation in order {
        let complete = OpSet::new(&complete_backing, graph.total_ops());
        let operation_view = graph.get_op(operation);
        let can_flip = matches!(operation_view.kind, OpNodeKind::Flippable(_));
        let mut next_complete = complete.clone_backing();
        OpSetMut::new(&mut next_complete, graph.total_ops()).add(operation);
        let needs_final_shuffle = finalization == BlockFinalization::ShuffleToOutputs;
        let demand = remaining_demand(&next_complete, needs_final_shuffle, graph);
        let mut candidates = Vec::new();
        for state in frontier {
            let swap_count =
                state.stack_end.saturating_sub(1).min(usize::from(shuffle.max_swap_depth));
            for swap_depth in 0..=swap_count {
                for flipped in [false, true].into_iter().take(1 + usize::from(can_flip)) {
                    let copy_inputs = allow_copy_inputs
                        && swap_depth == 0
                        && !operation_view.inputs_fifo.is_empty()
                        && (operation_view.inputs_fifo.len() <= 3
                            || (operation_view.inputs_fifo.len() == 4 && graph.total_ops() <= 10));
                    let preserve_inputs = if allow_copy_inputs
                        && swap_depth <= 1
                        && ((2..=3).contains(&operation_view.inputs_fifo.len())
                            && graph.total_ops() <= 20
                            || operation_view.inputs_fifo.len() == 4 && graph.total_ops() <= 10)
                    {
                        operation_view
                            .inputs_fifo
                            .iter()
                            .copied()
                            .filter(|&input| graph.is_last_use(complete, input))
                            .collect::<SmallVec<[_; 4]>>()
                    } else {
                        SmallVec::new()
                    };
                    for strategy in 0..1 + usize::from(copy_inputs) + preserve_inputs.len() {
                        let mut transition = Vec::new();
                        let mut stack = TrackedStack::new_from_parts(
                            next_alloc_id,
                            |operation| transition.push(operation),
                            &state.values[..state.stack_end],
                            state.values[state.stack_end..].to_vec(),
                        );
                        if swap_depth > 0 {
                            stack.swap(
                                u8::try_from(swap_depth).expect("bounded swap depth exceeds u8"),
                            );
                        }
                        if strategy == 0 {
                            greedy_schedule_op(
                                shuffle, &mut stack, graph, operation, complete, flipped,
                            );
                        } else if copy_inputs && strategy == 1 {
                            copy_schedule_op(shuffle, &mut stack, graph, operation, flipped);
                        } else {
                            greedy_schedule_op_preserving(
                                shuffle,
                                &mut stack,
                                graph,
                                operation,
                                complete,
                                flipped,
                                Some(preserve_inputs[strategy - 1 - usize::from(copy_inputs)]),
                            );
                        }
                        if needs_final_shuffle {
                            let completed = OpSet::new(&next_complete, graph.total_ops());
                            while stack
                                .top()
                                .is_some_and(|value| graph.uses_remaining(completed, value) == 0)
                            {
                                stack.pop();
                            }
                        }
                        let values =
                            [stack.fifo(), stack.underlying_spilled()].concat().into_boxed_slice();
                        let stack_end = stack.fifo().len();
                        drop(stack);
                        let cost = state.cost + stack_ops_cost(&transition, shuffle);
                        let remaining = demand_cost_lower_bound(
                            &demand,
                            &values[..stack_end],
                            &values[stack_end..],
                            needs_final_shuffle,
                        );
                        let priority = layout_priority(
                            cost,
                            remaining,
                            &values[..stack_end],
                            graph.output_values_fifo(),
                            alignment_factor,
                        );
                        let mut operations = state.operations.clone();
                        operations.extend(transition);
                        candidates
                            .push((priority, BeamState { values, stack_end, operations, cost }));
                    }
                }
            }
        }
        candidates.sort_unstable_by_key(|(priority, _)| *priority);
        let mut next_frontier = Vec::with_capacity(width);
        for (_, candidate) in candidates {
            if next_frontier.iter().any(|existing: &BeamState| {
                existing.stack_end == candidate.stack_end && existing.values == candidate.values
            }) {
                continue;
            }
            next_frontier.push(candidate);
            if next_frontier.len() == width {
                break;
            }
        }
        frontier = next_frontier;
        complete_backing = next_complete;
    }

    let mut best = None;
    for state in frontier {
        let mut final_operations = Vec::new();
        let mut stack = TrackedStack::new_from_parts(
            next_alloc_id,
            |operation| final_operations.push(operation),
            &state.values[..state.stack_end],
            state.values[state.stack_end..].to_vec(),
        );
        if finalization == BlockFinalization::ShuffleToOutputs {
            greedy_shuffler::shuffle(shuffle, &mut stack, graph);
        }
        let spill_count =
            u32::try_from(stack.underlying_spilled().len()).expect("spill count overflow");
        drop(stack);
        let cost = state.cost + stack_ops_cost(&final_operations, shuffle);
        if best.as_ref().is_none_or(|(best_cost, _, _)| cost < *best_cost) {
            let mut operations = state.operations;
            operations.extend(final_operations);
            best = Some((cost, operations.into_boxed_slice(), spill_count));
        }
    }
    let (_, ops, spill_count) = best.expect("beam scheduling retained no candidates");
    SearchResult { ops, spill_count, candidate_limit_reached: false }
}

fn simplify_result(ops: &mut Box<[StackOps]>, graph: &OpGraph, shuffle: ShuffleConfig) {
    *ops = crate::scheduler::simplify_stack_ops(
        std::mem::take(ops),
        shuffle.max_swap_depth,
        shuffle.max_dup_depth,
        |operation| {
            graph.op_ids().any(|candidate| {
                matches!(graph.get_op(candidate).kind, OpNodeKind::Flippable(index) if index == operation)
            })
        },
    );
}

fn graph_operation_id(graph: &OpGraph, scheduled: StackOps) -> Option<OpNodeId> {
    let index = match scheduled {
        StackOps::Op(index) | StackOps::Flipped(index) | StackOps::CallRetPush(index) => index,
        _ => return None,
    };
    graph.op_ids().find(|&candidate| {
        matches!(
            (scheduled, graph.get_op(candidate).kind),
            (
                StackOps::Op(_) | StackOps::Flipped(_),
                OpNodeKind::Flippable(candidate_index) | OpNodeKind::Normal(candidate_index)
            ) if candidate_index == index
        ) || matches!(
            (scheduled, graph.get_op(candidate).kind),
            (StackOps::CallRetPush(_), OpNodeKind::RetDestPush(candidate_index))
                if candidate_index == index
        )
    })
}

fn improve_schedule_order(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    graph: &OpGraph,
    mut incumbent: SearchResult,
    max_trials: usize,
    passes: usize,
) -> SearchResult {
    if graph.total_ops() < 2 {
        return incumbent;
    }
    let mut order = incumbent
        .ops
        .iter()
        .filter_map(|&operation| graph_operation_id(graph, operation))
        .collect::<Vec<_>>();
    assert_eq!(order.len(), graph.total_ops() as usize);
    let mut best_cost = stack_ops_cost(&incumbent.ops, shuffle);
    let trial_count = (order.len() - 1).min(max_trials);
    for _ in 0..passes {
        for trial in 0..trial_count {
            let position = trial * (order.len() - 1) / trial_count;
            let earlier = order[position];
            let later = order[position + 1];
            if graph.get_predecessors(later).contains(earlier) {
                continue;
            }
            order.swap(position, position + 1);
            let (candidate_ops, spill_count) =
                schedule_in_order(finalization, next_alloc_id, shuffle, graph, &order);
            let candidate_cost = stack_ops_cost(&candidate_ops, shuffle);
            if candidate_cost <= best_cost {
                if candidate_cost < best_cost {
                    best_cost = candidate_cost;
                    incumbent.ops = candidate_ops;
                    incumbent.spill_count = spill_count;
                }
            } else {
                order.swap(position, position + 1);
            }
        }
    }
    for trial in 0_u32..24 {
        let first = usize::try_from(trial.wrapping_mul(0x9e37_79b9).wrapping_add(0x243f_6a88))
            .expect("u32 does not fit usize")
            % order.len();
        let second = usize::try_from(trial.wrapping_mul(0x85eb_ca6b).wrapping_add(0xb7e1_5163))
            .expect("u32 does not fit usize")
            % order.len();
        if first == second {
            continue;
        }
        order.swap(first, second);
        let mut positions = IndexVec::<OpNodeId, usize>::from_vec(vec![0; order.len()]);
        for (position, &operation) in order.iter().enumerate() {
            positions[operation] = position;
        }
        let valid = order.iter().enumerate().all(|(position, &operation)| {
            graph
                .get_predecessors(operation)
                .iter()
                .all(|predecessor| positions[predecessor] < position)
        });
        if !valid {
            order.swap(first, second);
            continue;
        }
        let (candidate_ops, spill_count) =
            schedule_in_order(finalization, next_alloc_id, shuffle, graph, &order);
        let candidate_cost = stack_ops_cost(&candidate_ops, shuffle);
        if candidate_cost <= best_cost {
            if candidate_cost < best_cost {
                best_cost = candidate_cost;
                incumbent.ops = candidate_ops;
                incumbent.spill_count = spill_count;
            }
        } else {
            order.swap(first, second);
        }
    }
    for trial in 32_u32..40 {
        let source = usize::try_from(trial.wrapping_mul(0x9e37_79b9).wrapping_add(0x243f_6a88))
            .expect("u32 does not fit usize")
            % order.len();
        let destination =
            usize::try_from(trial.wrapping_mul(0x85eb_ca6b).wrapping_add(0xb7e1_5163))
                .expect("u32 does not fit usize")
                % order.len();
        if source == destination {
            continue;
        }
        let mut candidate_order = order.clone();
        let operation = candidate_order.remove(source);
        candidate_order.insert(destination, operation);
        let mut positions = IndexVec::<OpNodeId, usize>::from_vec(vec![0; order.len()]);
        for (position, &operation) in candidate_order.iter().enumerate() {
            positions[operation] = position;
        }
        let valid = candidate_order.iter().enumerate().all(|(position, &operation)| {
            graph
                .get_predecessors(operation)
                .iter()
                .all(|predecessor| positions[predecessor] < position)
        });
        if !valid {
            continue;
        }
        let (candidate_ops, spill_count) =
            schedule_in_order(finalization, next_alloc_id, shuffle, graph, &candidate_order);
        let candidate_cost = stack_ops_cost(&candidate_ops, shuffle);
        if candidate_cost <= best_cost {
            order = candidate_order;
            if candidate_cost < best_cost {
                best_cost = candidate_cost;
                incumbent.ops = candidate_ops;
                incumbent.spill_count = spill_count;
            }
        }
    }
    incumbent
}

fn schedule_in_order(
    finalization: BlockFinalization,
    next_alloc_id: StaticAllocId,
    shuffle: ShuffleConfig,
    graph: &OpGraph,
    order: &[OpNodeId],
) -> (Box<[StackOps]>, u32) {
    let mut operations = Vec::new();
    let mut complete_backing = vec![0; graph.words_per_set() as usize];
    let mut complete = OpSetMut::new(&mut complete_backing, graph.total_ops());
    let mut inner = EvmStack::new();
    for input in graph.input_values_fifo().iter().rev() {
        inner.push(input);
    }
    let mut stack = TrackedStack::new_from_evm(next_alloc_id, |op| operations.push(op), inner, 8);
    for &operation in order {
        let operation_view = graph.get_op(operation);
        let can_flip = matches!(operation_view.kind, OpNodeKind::Flippable(_));
        let mut best = None;
        for flipped in [false, true].into_iter().take(1 + usize::from(can_flip)) {
            let mut trial_ops = Vec::new();
            let mut trial = stack.clone_with(|op| trial_ops.push(op));
            greedy_schedule_op(shuffle, &mut trial, graph, operation, complete.as_ref(), flipped);
            let cost = stack_ops_cost(&trial_ops, shuffle);
            if best.is_none_or(|(best_cost, _)| cost < best_cost) {
                best = Some((cost, flipped));
            }
        }
        let (_, flipped) = best.expect("every operation has a scheduling strategy");
        greedy_schedule_op(shuffle, &mut stack, graph, operation, complete.as_ref(), flipped);
        complete.add(operation);
    }
    if finalization == BlockFinalization::ShuffleToOutputs {
        greedy_shuffler::shuffle(shuffle, &mut stack, graph);
    }
    let spill_count =
        u32::try_from(stack.underlying_spilled().len()).expect("spill count overflow");
    drop(stack);
    (operations.into_boxed_slice(), spill_count)
}

impl Search<'_> {
    fn optimize_initial_spills(
        &mut self,
        inputs: &[ValueNodeId],
        minimum_spill_count: usize,
        candidate_budget: usize,
    ) {
        if inputs.len() < 10 {
            return;
        }
        let extra_spill_count = (inputs.len() - minimum_spill_count).min(4);
        for extra in 1..=extra_spill_count {
            let spill_count = minimum_spill_count + extra;
            let path = (0..spill_count)
                .map(|index| {
                    StackOps::Store(
                        self.next_alloc_id
                            + u32::try_from(index).expect("initial spill index overflow"),
                    )
                })
                .collect::<Vec<_>>();
            let values =
                inputs[spill_count..].iter().chain(&inputs[..spill_count]).copied().collect();
            self.path = path;
            self.assessed_candidates = 0;
            self.max_candidates = candidate_budget;
            self.best_state_costs.clear();
            self.visit(SearchNode {
                state: Rc::new(SearchState {
                    complete: vec![0; self.graph.words_per_set() as usize].into_boxed_slice(),
                    values,
                    stack_end: inputs.len() - spill_count,
                }),
                completed_count: 0,
                executed_cost: stack_ops_cost(&self.path, self.shuffle),
            });
        }
    }

    fn improve_operand_layouts(&mut self, width: usize) {
        let order = self
            .best_ops
            .iter()
            .filter_map(|&operation| graph_operation_id(self.graph, operation))
            .collect::<Vec<_>>();
        let candidate = beam_schedule_in_order(
            self.finalization,
            self.next_alloc_id,
            self.shuffle,
            self.graph,
            &order,
            width,
            4,
            false,
        );
        let candidate_cost = stack_ops_cost(&candidate.ops, self.shuffle);
        if candidate_cost < self.best_cost {
            self.best_cost = candidate_cost;
            self.best_ops = candidate.ops;
            self.best_spill_count = candidate.spill_count;
        }
    }

    fn improve_adjacent_order(&mut self, max_trials: usize) {
        if self.graph.total_ops() < 2 {
            return;
        }
        let mut order = self
            .best_ops
            .iter()
            .filter_map(|&operation| graph_operation_id(self.graph, operation))
            .collect::<Vec<_>>();
        assert_eq!(order.len(), self.graph.total_ops() as usize);

        let trial_count = (order.len() - 1).min(max_trials);
        for _ in 0..10 {
            for trial in 0..trial_count {
                let position = trial * (order.len() - 1) / trial_count;
                let earlier = order[position];
                let later = order[position + 1];
                if self.graph.get_predecessors(later).contains(earlier) {
                    continue;
                }
                order.swap(position, position + 1);
                let (candidate_ops, spill_count) = schedule_in_order(
                    self.finalization,
                    self.next_alloc_id,
                    self.shuffle,
                    self.graph,
                    &order,
                );
                let candidate_cost = stack_ops_cost(&candidate_ops, self.shuffle);
                if candidate_cost <= self.best_cost {
                    if candidate_cost < self.best_cost {
                        self.best_cost = candidate_cost;
                        self.best_ops = candidate_ops;
                        self.best_spill_count = spill_count;
                    }
                } else {
                    order.swap(position, position + 1);
                }
            }
        }
    }

    fn optimize_tail(&mut self, tail_operations: u32, candidate_budget: usize) {
        if self.finalization != BlockFinalization::ShuffleToOutputs || self.graph.total_ops() == 0 {
            return;
        }

        let prefix_operation_count = self.graph.total_ops().saturating_sub(tail_operations);
        let mut seen_operations = 0;
        let mut prefix_end = 0;
        if prefix_operation_count > 0 {
            for (position, operation) in self.best_ops.iter().enumerate() {
                if matches!(
                    operation,
                    StackOps::Op(_) | StackOps::Flipped(_) | StackOps::CallRetPush(_)
                ) {
                    seen_operations += 1;
                    if seen_operations == prefix_operation_count {
                        prefix_end = position + 1;
                        break;
                    }
                }
            }
        }
        let prefix = self.best_ops[..prefix_end].to_vec();
        let mut complete = vec![0; self.graph.words_per_set() as usize];
        let mut stack = TrackedStack::new_from_parts(
            self.next_alloc_id,
            |_| {},
            &self.graph.input_values_fifo().iter().collect::<Vec<_>>(),
            Vec::new(),
        );
        for &operation in &prefix {
            match operation {
                StackOps::Swap(depth) => stack.swap(depth),
                StackOps::Dup(depth) => stack.dup(depth),
                StackOps::Pop => stack.pop(),
                StackOps::Store(expected) => assert_eq!(stack.spill_top(), expected),
                StackOps::Load(allocation) => stack.load(allocation),
                StackOps::Op(_) | StackOps::Flipped(_) | StackOps::CallRetPush(_) => {
                    let operation_id = graph_operation_id(self.graph, operation)
                        .expect("scheduled operation is absent from the graph");
                    let flipped = matches!(operation, StackOps::Flipped(_));
                    stack.op(self.graph, operation_id, flipped);
                    OpSetMut::new(&mut complete, self.graph.total_ops()).add(operation_id);
                }
                StackOps::Exchange(_, _) => {
                    unreachable!("pre-Amsterdam schedule contains an exchange")
                }
            }
        }

        let values = [stack.fifo(), stack.underlying_spilled()].concat().into_boxed_slice();
        let stack_end = stack.fifo().len();
        drop(stack);
        self.path = prefix;
        self.assessed_candidates = 0;
        self.max_candidates = candidate_budget;
        self.best_state_costs.clear();
        self.allow_tail_swaps = true;
        self.visit(SearchNode {
            state: Rc::new(SearchState {
                complete: complete.into_boxed_slice(),
                values,
                stack_end,
            }),
            completed_count: prefix_operation_count,
            executed_cost: stack_ops_cost(&self.path, self.shuffle),
        });
        self.allow_tail_swaps = false;
    }

    fn precondition_target(
        &self,
        current_stack: &[ValueNodeId],
        complete: OpSet<'_>,
    ) -> Option<Vec<ValueNodeId>> {
        if !(2..=usize::from(self.shuffle.max_swap_depth) + 1).contains(&current_stack.len())
            || !current_stack
                .iter()
                .enumerate()
                .all(|(position, value)| !current_stack[position + 1..].contains(value))
        {
            return None;
        }
        let mut target = current_stack.to_vec();
        target.sort_by_key(|&value| {
            if let Some(position) = self
                .graph
                .output_values_fifo()
                .iter()
                .enumerate()
                .filter_map(|(position, output)| (*output == value).then_some(position))
                .next_back()
            {
                (1, position, 0)
            } else {
                let consumers = self.graph.get_consumers(value);
                let (operation_position, input_position) = consumers
                    .iter()
                    .filter(|&operation| !complete.contains(operation))
                    .last()
                    .map(|operation| {
                        let input_position = self
                            .graph
                            .get_op(operation)
                            .inputs_fifo
                            .iter()
                            .rposition(|&input| input == value)
                            .expect("consumer does not use its consumed value");
                        (operation.idx(), input_position)
                    })
                    .unwrap_or((usize::MAX, 0));
                (0, operation_position, input_position)
            }
        });
        (target != current_stack).then_some(target)
    }

    fn visit(&mut self, node: SearchNode) {
        if !record_if_improved(&mut self.best_state_costs, &node.state, node.executed_cost) {
            return;
        }

        if node.completed_count == self.graph.total_ops() {
            self.finish(node);
            return;
        }
        if self.assessed_candidates == self.max_candidates {
            self.candidate_limit_reached = true;
            return;
        }

        let complete = OpSet::new(&node.state.complete, self.graph.total_ops());
        let mut completable_backing =
            SmallVec::<[BitsetWord; SCRATCH_OP_SET_INLINE_CAPACITY]>::new();
        completable_backing.resize(self.graph.words_per_set() as usize, 0);
        let mut completable = OpSetMut::new(&mut completable_backing, self.graph.total_ops());
        self.graph.collect_next_completable_into(complete, &mut completable);
        let completable = completable.iter().collect::<SmallVec<[OpNodeId; 32]>>();

        let precondition_target =
            self.precondition_target(&node.state.values[..node.state.stack_end], complete);
        let mut children = Vec::with_capacity(completable.len() + 10);
        if self.allow_tail_swaps
            && node.completed_count + 4 >= self.graph.total_ops()
            && (2..=7).contains(&node.state.stack_end)
        {
            let max_depth = node.state.stack_end.min(usize::from(self.shuffle.max_swap_depth) + 1);
            for depth in 1..max_depth {
                if self.assessed_candidates == self.max_candidates {
                    self.candidate_limit_reached = true;
                    break;
                }
                self.assessed_candidates += 1;
                let child = self.build_swap_child(
                    &node,
                    u8::try_from(depth).expect("bounded stack depth exceeds u8"),
                );
                if child.lower_bound < self.best_cost {
                    children.push(child);
                }
            }
        }
        let dead_depth = node.state.values[..node.state.stack_end]
            .iter()
            .position(|&value| self.graph.uses_remaining(complete, value) == 0)
            .filter(|&depth| depth <= usize::from(self.shuffle.max_swap_depth));
        if let Some(depth) = dead_depth {
            children.push(self.build_shrink_child(
                &node,
                Some(u8::try_from(depth).expect("dead value depth exceeds u8")),
            ));
        }
        if node.state.stack_end > usize::from(self.shuffle.max_swap_depth) && dead_depth != Some(0)
        {
            children.push(self.build_shrink_child(&node, None));
        }
        if let Some(target) = precondition_target {
            let first_output = target
                .iter()
                .position(|value| self.graph.output_values_fifo().contains(value))
                .unwrap_or(target.len());
            let output_count = target.len() - first_output;
            children.push(self.build_precondition_child(&node, &target));
            if output_count > 1 {
                let mut rotated = target.clone();
                rotated[first_output..].rotate_left(1);
                if rotated != node.state.values[..node.state.stack_end] {
                    children.push(self.build_precondition_child(&node, &rotated));
                }
            }
        }
        'operations: for op in completable {
            let operation = self.graph.get_op(op);
            let can_flip = matches!(operation.kind, OpNodeKind::Flippable(_));
            let can_copy_inputs = (self.copy_all_inputs
                && !operation.inputs_fifo.is_empty()
                && operation.inputs_fifo.len() <= 2)
                || operation
                    .inputs_fifo
                    .iter()
                    .enumerate()
                    .any(|(i, input)| operation.inputs_fifo[i + 1..].contains(input));
            for flipped in [false, true].into_iter().take(1 + usize::from(can_flip)) {
                for copy_inputs in [false, true].into_iter().take(1 + usize::from(can_copy_inputs))
                {
                    if self.assessed_candidates == self.max_candidates {
                        self.candidate_limit_reached = true;
                        break 'operations;
                    }
                    self.assessed_candidates += 1;
                    let child = self.build_child(&node, complete, op, flipped, copy_inputs);
                    if child.lower_bound >= self.best_cost {
                        continue;
                    }
                    children.push(child);
                }
            }
        }
        children.sort_unstable_by_key(|child| child.priority);

        for child in children {
            let path_len = self.path.len();
            self.path.extend_from_slice(&child.transition_ops);
            self.visit(child.node);
            self.path.truncate(path_len);
        }
    }

    fn build_swap_child(&self, node: &SearchNode, depth: u8) -> Child {
        let mut values = node.state.values.clone();
        values.swap(0, usize::from(depth));
        let transition_ops: Box<[StackOps]> = Box::new([StackOps::Swap(depth)]);
        let remaining_cost = remaining_cost_lower_bound(
            &node.state.complete,
            &values[..node.state.stack_end],
            &values[node.state.stack_end..],
            self.finalization == BlockFinalization::ShuffleToOutputs,
            self.graph,
        );
        let executed_cost = node.executed_cost + stack_ops_cost(&transition_ops, self.shuffle);
        let priority = child_priority(
            executed_cost,
            remaining_cost,
            &values[..node.state.stack_end],
            self.graph.output_values_fifo(),
            self.alignment_factor,
        );

        Child {
            node: SearchNode {
                state: Rc::new(SearchState {
                    complete: node.state.complete.clone(),
                    values,
                    stack_end: node.state.stack_end,
                }),
                completed_count: node.completed_count,
                executed_cost,
            },
            transition_ops,
            lower_bound: executed_cost + remaining_cost,
            priority,
        }
    }

    fn build_shrink_child(&self, node: &SearchNode, dead_depth: Option<u8>) -> Child {
        let mut transition_ops = Vec::new();
        let mut stack = TrackedStack::new_from_parts(
            self.next_alloc_id,
            |op| transition_ops.push(op),
            &node.state.values[..node.state.stack_end],
            node.state.values[node.state.stack_end..].to_vec(),
        );
        if let Some(depth) = dead_depth {
            if depth > 0 {
                stack.swap(depth);
            }
            stack.pop();
        } else {
            let top = stack.top().expect("cannot spill an empty stack");
            if stack.get_spilled(top).is_some() {
                stack.pop();
            } else {
                stack.spill_top();
            }
        }
        let remaining_cost = remaining_cost_lower_bound(
            &node.state.complete,
            stack.fifo(),
            stack.underlying_spilled(),
            self.finalization == BlockFinalization::ShuffleToOutputs,
            self.graph,
        );
        let values = [stack.fifo(), stack.underlying_spilled()].concat();
        let stack_end = stack.fifo().len();
        drop(stack);
        let executed_cost = node.executed_cost + stack_ops_cost(&transition_ops, self.shuffle);
        let priority = child_priority(
            executed_cost,
            remaining_cost,
            &values[..stack_end],
            self.graph.output_values_fifo(),
            self.alignment_factor,
        );

        Child {
            node: SearchNode {
                state: Rc::new(SearchState {
                    complete: node.state.complete.clone(),
                    values: values.into_boxed_slice(),
                    stack_end,
                }),
                completed_count: node.completed_count,
                executed_cost,
            },
            transition_ops: transition_ops.into_boxed_slice(),
            lower_bound: executed_cost + remaining_cost,
            priority,
        }
    }

    fn build_precondition_child(&self, node: &SearchNode, target: &[ValueNodeId]) -> Child {
        let mut transition_ops = Vec::new();
        let mut stack = TrackedStack::new_from_parts(
            self.next_alloc_id,
            |op| transition_ops.push(op),
            &node.state.values[..node.state.stack_end],
            node.state.values[node.state.stack_end..].to_vec(),
        );
        while stack.fifo() != target {
            let destination = target
                .iter()
                .position(|&value| value == stack.fifo()[0])
                .expect("stack precondition lost a value");
            let destination = if destination == 0 {
                (1..target.len())
                    .find(|&position| stack.fifo()[position] != target[position])
                    .expect("stack precondition mismatch disappeared")
            } else {
                destination
            };
            stack.swap(u8::try_from(destination).expect("swap overflow"));
        }
        let remaining_cost = remaining_cost_lower_bound(
            &node.state.complete,
            stack.fifo(),
            stack.underlying_spilled(),
            self.finalization == BlockFinalization::ShuffleToOutputs,
            self.graph,
        );
        let values = [stack.fifo(), stack.underlying_spilled()].concat();
        let stack_end = stack.fifo().len();
        drop(stack);
        let executed_cost = node.executed_cost + stack_ops_cost(&transition_ops, self.shuffle);
        let priority = child_priority(
            executed_cost,
            remaining_cost,
            &values[..stack_end],
            self.graph.output_values_fifo(),
            self.alignment_factor,
        );

        Child {
            node: SearchNode {
                state: Rc::new(SearchState {
                    complete: node.state.complete.clone(),
                    values: values.into_boxed_slice(),
                    stack_end,
                }),
                completed_count: node.completed_count,
                executed_cost,
            },
            transition_ops: transition_ops.into_boxed_slice(),
            lower_bound: executed_cost + remaining_cost,
            priority,
        }
    }

    fn build_child(
        &self,
        node: &SearchNode,
        complete: OpSet<'_>,
        op: OpNodeId,
        flipped: bool,
        copy_inputs: bool,
    ) -> Child {
        let operation = self.graph.get_op(op);
        let outputs_are_dead = operation
            .outputs_fifo
            .iter()
            .all(|&output| self.graph.uses_remaining(complete, output) == 0);
        let mut transition_ops = Vec::with_capacity(ESTIMATED_STACK_OPS_PER_GRAPH_OP);
        let mut stack = TrackedStack::new_from_parts(
            self.next_alloc_id,
            |op| transition_ops.push(op),
            &node.state.values[..node.state.stack_end],
            node.state.values[node.state.stack_end..].to_vec(),
        );
        if copy_inputs {
            copy_schedule_op(self.shuffle, &mut stack, self.graph, op, flipped);
        } else {
            greedy_schedule_op(self.shuffle, &mut stack, self.graph, op, complete, flipped);
        }

        let complete = {
            let mut backing = complete.clone_backing();
            OpSetMut::new(&mut backing, self.graph.total_ops()).add(op);
            backing.into_boxed_slice()
        };
        let completed = OpSet::new(&complete, self.graph.total_ops());
        if self.finalization == BlockFinalization::ShuffleToOutputs {
            while stack.top().is_some_and(|value| self.graph.uses_remaining(completed, value) == 0)
            {
                stack.pop();
            }
        }

        let remaining_cost = if node.completed_count + 1 == self.graph.total_ops()
            && self.finalization == BlockFinalization::ShuffleToOutputs
        {
            let mut final_ops = Vec::new();
            let mut final_stack = stack.clone_with(|op| final_ops.push(op));
            greedy_shuffler::shuffle(self.shuffle, &mut final_stack, self.graph);
            stack_ops_cost(&final_ops, self.shuffle)
        } else {
            remaining_cost_lower_bound(
                &complete,
                stack.fifo(),
                stack.underlying_spilled(),
                self.finalization == BlockFinalization::ShuffleToOutputs,
                self.graph,
            )
        };
        let values = [stack.fifo(), stack.underlying_spilled()].concat();
        let stack_end = stack.fifo().len();
        drop(stack);
        let transition_cost = stack_ops_cost(&transition_ops, self.shuffle);
        let executed_cost = node.executed_cost + transition_cost;

        let priority = child_priority(
            executed_cost,
            remaining_cost,
            &values[..stack_end],
            self.graph.output_values_fifo(),
            self.alignment_factor,
        )
        .saturating_sub(
            u32::try_from(operation.inputs_fifo.len()).expect("operation arity exceeds u32")
                * BASE_COST_FACTOR
                * self.arity_factor
                + u32::from(outputs_are_dead) * BASE_COST_FACTOR * 5,
        );

        Child {
            node: SearchNode {
                state: Rc::new(SearchState {
                    complete,
                    values: values.into_boxed_slice(),
                    stack_end,
                }),
                completed_count: node.completed_count + 1,
                executed_cost,
            },
            transition_ops: transition_ops.into_boxed_slice(),
            lower_bound: executed_cost + remaining_cost,
            priority,
        }
    }

    fn finish(&mut self, node: SearchNode) {
        let mut final_ops = Vec::new();
        let mut stack = TrackedStack::new_from_parts(
            self.next_alloc_id,
            |op| final_ops.push(op),
            &node.state.values[..node.state.stack_end],
            node.state.values[node.state.stack_end..].to_vec(),
        );
        if self.finalization == BlockFinalization::ShuffleToOutputs {
            greedy_shuffler::shuffle(self.shuffle, &mut stack, self.graph);
        }
        let spill_count = u32::try_from(stack.underlying_spilled().len()).expect("overflow");
        drop(stack);

        let cost = node.executed_cost + stack_ops_cost(&final_ops, self.shuffle);
        if cost >= self.best_cost {
            return;
        }

        self.best_cost = cost;
        let mut best_ops = Vec::with_capacity(self.path.len() + final_ops.len());
        best_ops.extend_from_slice(&self.path);
        best_ops.extend_from_slice(&final_ops);
        self.best_ops = best_ops.into_boxed_slice();
        self.best_spill_count = spill_count;
    }
}

fn record_if_improved(
    best_state_costs: &mut HashMap<Rc<SearchState>, u32>,
    state: &Rc<SearchState>,
    cost: u32,
) -> bool {
    if best_state_costs.get(state).is_some_and(|&best_cost| best_cost <= cost) {
        return false;
    }
    best_state_costs.insert(state.clone(), cost);
    true
}

fn layout_priority(
    executed_cost: u32,
    remaining_cost: u32,
    stack: &[ValueNodeId],
    outputs: &[ValueNodeId],
    alignment_factor: u32,
) -> u32 {
    let exact_alignment = stack
        .iter()
        .rev()
        .zip(outputs.iter().rev())
        .filter(|(current, target)| current == target)
        .count();
    let reward = u32::try_from(exact_alignment).expect("stack alignment exceeds u32")
        * BASE_COST_FACTOR
        * alignment_factor;
    (executed_cost + remaining_cost).saturating_sub(reward)
}

fn child_priority(
    executed_cost: u32,
    remaining_cost: u32,
    stack: &[ValueNodeId],
    outputs: &[ValueNodeId],
    alignment_factor: u32,
) -> u32 {
    let exact_alignment = stack
        .iter()
        .rev()
        .zip(outputs.iter().rev())
        .filter(|(current, target)| current == target)
        .count();
    let reward = u32::try_from(exact_alignment).expect("stack alignment exceeds u32")
        * BASE_COST_FACTOR
        * alignment_factor;
    (executed_cost + remaining_cost).saturating_sub(reward)
}

fn remaining_demand(
    complete: &[BitsetWord],
    needs_final_shuffle: bool,
    graph: &OpGraph,
) -> IndexVec<ValueNodeId, u32> {
    let complete = OpSet::new(complete, graph.total_ops());
    let mut demand = IndexVec::<ValueNodeId, u32>::from_vec(vec![0; graph.total_values() as usize]);
    for operation in graph.op_ids().filter(|&operation| !complete.contains(operation)) {
        for &input in graph.get_op(operation).inputs_fifo {
            demand[input] += 1;
        }
    }
    if needs_final_shuffle {
        for &output in graph.output_values_fifo() {
            demand[output] += 1;
        }
    }
    demand
}

fn demand_cost_lower_bound(
    demand: &IndexVec<ValueNodeId, u32>,
    stack: &[ValueNodeId],
    spilled: &[ValueNodeId],
    needs_final_shuffle: bool,
) -> u32 {
    const COPY_COST: u32 = 3 * BASE_COST_FACTOR;
    const LOAD_COST: u32 = 6 * BASE_COST_FACTOR;

    let demand_cost = demand
        .enumerate_idx()
        .map(|(value, &demand)| {
            let source_cost =
                u32::from(demand > 0 && !stack.contains(&value) && spilled.contains(&value))
                    * LOAD_COST;
            source_cost + demand.saturating_sub(1) * COPY_COST
        })
        .sum::<u32>();
    let cleanup_cost = if needs_final_shuffle {
        u32::try_from(stack.iter().filter(|&&value| demand[value] == 0).count()).expect("overflow")
            * COPY_COST
    } else {
        0
    };

    demand_cost + cleanup_cost
}

fn remaining_cost_lower_bound(
    complete: &[BitsetWord],
    stack: &[ValueNodeId],
    spilled: &[ValueNodeId],
    needs_final_shuffle: bool,
    graph: &OpGraph,
) -> u32 {
    demand_cost_lower_bound(
        &remaining_demand(complete, needs_final_shuffle, graph),
        stack,
        spilled,
        needs_final_shuffle,
    )
}

fn stack_ops_cost(ops: &[StackOps], shuffle: ShuffleConfig) -> u32 {
    let cost = crate::stack::gas_cost(ops, shuffle);
    u32::try_from(cost).expect("stack operation cost overflow") * BASE_COST_FACTOR
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_revisits_a_state_at_lower_cost() {
        let state =
            Rc::new(SearchState { complete: Box::new([]), values: Box::new([]), stack_end: 0 });
        let equal_state =
            Rc::new(SearchState { complete: Box::new([]), values: Box::new([]), stack_end: 0 });
        let mut best_state_costs = HashMap::new();

        assert!(record_if_improved(&mut best_state_costs, &state, 10));
        assert!(!record_if_improved(&mut best_state_costs, &equal_state, 10));
        assert!(!record_if_improved(&mut best_state_costs, &equal_state, 11));
        assert!(record_if_improved(&mut best_state_costs, &equal_state, 9));
    }
}
