use smallvec::SmallVec;

use crate::{
    op_graph::{OpGraph, OpNodeId, OpSet, ValueNodeId},
    stack::{ShuffleConfig, StackOps, TrackedStack},
};

mod permute;

#[cfg(test)]
mod tests;

const SCHEDULE_MAX_STEPS: usize = 100_000;
const PERMUTE_PATHS_BUDGET: usize = 100;

fn only_contains_unique(values: &[ValueNodeId]) -> bool {
    values.iter().enumerate().all(|(i, value)| !values[i + 1..].contains(value))
}

pub(crate) fn copy_schedule_op<Sink: FnMut(StackOps)>(
    config: ShuffleConfig,
    stack: &mut TrackedStack<Sink>,
    graph: &OpGraph,
    op_id: OpNodeId,
    flipped: bool,
) {
    let op = graph.get_op(op_id);
    let mut flipped_inputs = SmallVec::<[ValueNodeId; 32]>::new();
    let inputs = if flipped {
        flipped_inputs.extend_from_slice(op.inputs_fifo);
        flipped_inputs.swap(0, 1);
        flipped_inputs.as_slice()
    } else {
        op.inputs_fifo
    };

    while inputs.iter().rev().enumerate().any(|(pushed, &value)| {
        stack.get_spilled(value).is_none()
            && stack
                .find_first(value)
                .is_none_or(|depth| usize::from(depth) + pushed > usize::from(config.max_dup_depth))
    }) {
        let top = stack.top().expect("an input is neither on the stack nor spilled");
        if stack.get_spilled(top).is_some() {
            stack.pop();
        } else {
            stack.spill_top();
        }
    }

    for &value in inputs.iter().rev() {
        if let Some(depth) =
            stack.find_first(value).filter(|&depth| depth <= u16::from(config.max_dup_depth))
        {
            stack.dup(depth.try_into().expect("depth was checked against the u8 limit"));
        } else {
            stack.unspill(value);
        }
    }
    stack.op(graph, op_id, flipped);
}

pub(crate) fn greedy_schedule_op<Sink: FnMut(StackOps)>(
    config: ShuffleConfig,
    stack: &mut TrackedStack<Sink>,
    graph: &OpGraph,
    op_id: OpNodeId,
    complete: OpSet<'_>,
    flipped: bool,
) {
    greedy_schedule_op_preserving(config, stack, graph, op_id, complete, flipped, None);
}

pub(crate) fn greedy_schedule_op_preserving<Sink: FnMut(StackOps)>(
    config: ShuffleConfig,
    stack: &mut TrackedStack<Sink>,
    graph: &OpGraph,
    op_id: OpNodeId,
    complete: OpSet<'_>,
    flipped: bool,
    preserve: Option<ValueNodeId>,
) {
    assert!(only_contains_unique(stack.fifo()), "expecting all start stack values to be unique");

    let op = graph.get_op(op_id);
    let mut flipped_inputs = SmallVec::<[ValueNodeId; 32]>::new();
    let inputs = if flipped {
        flipped_inputs.extend_from_slice(op.inputs_fifo);
        flipped_inputs.swap(0, 1);
        flipped_inputs.as_slice()
    } else {
        op.inputs_fifo
    };

    let unique_last_uses_on_stack = stack
        .fifo()
        .iter()
        .copied()
        .filter(|value| {
            Some(*value) != preserve
                && graph.is_last_use(complete, *value)
                && inputs.contains(value)
        })
        .collect::<SmallVec<[_; 32]>>();

    let head = unique_last_uses_on_stack.len().try_into().expect("overflow");

    let mut preparer =
        GreedyOperandPreparer::new(head, config, stack, inputs, &unique_last_uses_on_stack);

    for _ in 0..SCHEDULE_MAX_STEPS {
        if matches!(preparer.progress(), Ok(Status::Complete)) {
            stack.op(graph, op_id, flipped);
            return;
        }
    }

    unreachable!("schedule didn't complete after {SCHEDULE_MAX_STEPS} steps");
}

enum Status {
    Complete,
    NotDone,
}

struct GoBackToProgressStart;

struct GreedyOperandPreparer<'a, Sink: FnMut(StackOps)> {
    head: u16,
    config: ShuffleConfig,
    stack: &'a mut TrackedStack<Sink>,
    target: &'a [ValueNodeId],
    last_uses: &'a [ValueNodeId],
    to_preserve: SmallVec<[ValueNodeId; 32]>,
    to_push: SmallVec<[ValueNodeId; 32]>,
    incremental_spills_left: u16,
}

impl<'a, Sink: FnMut(StackOps)> GreedyOperandPreparer<'a, Sink> {
    fn is_complete(&self) -> bool {
        usize::from(self.head) == self.target.len()
            && self.stack.fifo().iter().zip(self.target).all(|(a, b)| a == b)
    }

    fn progress(&mut self) -> Result<Status, GoBackToProgressStart> {
        assert!(self.head <= self.stack.len());

        if self.is_complete() {
            return Ok(Status::Complete);
        }

        if self.head > 0 && self.stack.fifo()[0] != self.target_head_top() {
            let permuted = self.swap_next_best()?;
            if permuted {
                return Ok(Status::NotDone);
            }
        }

        let total_left_to_push = self.target.len() - usize::from(self.head);
        if total_left_to_push == 0 {
            self.permute_until_complete()
        } else {
            self.push_next_single_best()?;
            Ok(Status::NotDone)
        }
    }

    fn push_next_single_best(&mut self) -> Result<(), GoBackToProgressStart> {
        let (i, &value) = self
            .to_push
            .iter()
            .enumerate()
            .max_by_key(|&(_i, &value)| {
                if self.to_preserve.contains(&value) {
                    return self.target.len();
                }
                let depth_delta = self.target.len() - usize::from(self.head);
                for (i, &want) in self.target.iter().enumerate().rev() {
                    let hi = i.checked_sub(depth_delta);
                    if hi.is_none_or(|hi| self.stack.fifo()[hi] != want) && want == value {
                        return i;
                    }
                }

                unreachable!("{value} not in target");
            })
            .expect("nothing left to push");
        self.to_push.swap_remove(i);
        self.try_push(value)
    }

    fn swap_next_best(&mut self) -> Result<bool, GoBackToProgressStart> {
        let swaps = permute::best_permute(
            &self.to_preserve,
            self.last_uses,
            usize::from(self.head),
            self.stack.fifo(),
            self.target,
            PERMUTE_PATHS_BUDGET,
            false,
        );
        if swaps.is_empty() {
            return Ok(false);
        }

        for swap in swaps {
            self.try_swap(swap)?;
        }

        Ok(true)
    }

    fn permute_until_complete(&mut self) -> Result<Status, GoBackToProgressStart> {
        assert_eq!(usize::from(self.head), self.target.len());
        let swaps = permute::best_permute(
            &self.to_preserve,
            self.last_uses,
            usize::from(self.head),
            self.stack.fifo(),
            self.target,
            PERMUTE_PATHS_BUDGET,
            true,
        );

        for &swap in &swaps {
            self.try_swap(swap)?;
        }

        Ok(Status::Complete)
    }

    fn new(
        head: u16,
        config: ShuffleConfig,
        stack: &'a mut TrackedStack<Sink>,
        target: &'a [ValueNodeId],
        last_uses: &'a [ValueNodeId],
    ) -> Self {
        // May include spilled values => algorithm will *try* to get a copy on the stack again.
        let to_preserve = stack.fifo()[..usize::from(head)]
            .iter()
            .copied()
            .filter(|value| target.contains(value) && !last_uses.contains(value))
            .collect();

        let mut to_push = SmallVec::<[ValueNodeId; 32]>::from_slice(target);
        for &value in last_uses {
            let i = to_push.iter().position(|&v| v == value).expect("last use not in target");
            to_push.remove(i);
        }
        to_push.reverse();

        let incremental_spills_left = stack.len();
        Self {
            head,
            config,
            stack,
            target,
            last_uses,
            to_preserve,
            to_push,
            incremental_spills_left,
        }
    }

    fn try_swap(&mut self, depth: u16) -> Result<(), GoBackToProgressStart> {
        if let Ok(depth) = depth.try_into()
            && depth <= self.config.max_swap_depth
        {
            let value = self.stack.top().expect("trying to swap without top");
            if self.head <= u16::from(depth)
                && let Some(pi) = self.to_preserve.iter().position(|&v| v == value)
            {
                self.to_preserve.swap_remove(pi);
            }

            self.stack.swap(depth);
            return Ok(());
        }

        let incremental = depth - u16::from(self.config.max_swap_depth);
        let total_to_spill =
            if only_contains_unique(self.target) && incremental <= self.incremental_spills_left {
                self.incremental_spills_left -= incremental;
                incremental
            } else {
                depth + 1
            };
        for _ in 0..total_to_spill {
            self.spill_top();
        }

        Err(GoBackToProgressStart)
    }

    fn try_push(&mut self, value: ValueNodeId) -> Result<(), GoBackToProgressStart> {
        if let Some(pos) = self
            .stack
            .find_first(value)
            .filter(|&depth| depth <= u16::from(self.config.max_dup_depth))
        {
            self.stack.dup(pos as u8);
            self.head += 1;
            return Ok(());
        }

        if let Some(alloc) = self.stack.get_spilled(value) {
            self.stack.load(alloc);
            self.head += 1;
            return Ok(());
        }

        let depth = self.stack.find_first(value).expect("trying to push missing");
        let total_to_spill = depth - u16::from(self.config.max_dup_depth);
        for _ in 0..total_to_spill {
            self.spill_top();
        }
        self.stack.dup(self.config.max_dup_depth);
        self.head += 1;

        Err(GoBackToProgressStart)
    }

    fn spill_top(&mut self) {
        let value = self.stack.top().expect("spilling on empty stack");
        if self.stack.get_spilled(value).is_some() {
            self.stack.pop();
        } else {
            self.stack.spill_top();
        }

        let mut shrinking_tail = true;
        if self.head > 0 && self.target.contains(&value) {
            match self.to_preserve.iter().position(|&v| v == value) {
                Some(pi) => {
                    self.to_preserve.swap_remove(pi);
                }
                None => {
                    self.to_push.push(value);
                    self.head -= 1;
                    shrinking_tail = false;
                }
            }
        }

        if shrinking_tail && self.head > 0 {
            let head_end = usize::from(self.head);
            let promoted = self.stack.fifo()[head_end - 1];

            if !self.last_uses.contains(&promoted) && self.target.contains(&promoted) {
                self.to_preserve.push(promoted);
            }
        }
    }

    fn target_head_top(&self) -> ValueNodeId {
        self.target[self.target.len() - usize::from(self.head)]
    }
}
