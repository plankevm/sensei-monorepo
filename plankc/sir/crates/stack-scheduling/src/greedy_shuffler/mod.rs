use crate::{
    op_graph::*,
    stack::{ShuffleConfig, StackOps, TrackedStack},
};
use indices::*;
use plank_core::{IncIterable, LoopLimit, Span, span::ToUsize};
use smallvec::SmallVec;

mod indices;

#[cfg(test)]
mod tests;

pub struct GreedyShuffler<'a, Sink: FnMut(StackOps)> {
    complete_at_bottom: usize,
    current: &'a mut TrackedStack<Sink>,
    target: &'a [ValueNodeId],
    max_swap_depth: FromTop<CurrentStack>,
    max_dup_depth: FromTop<CurrentStack>,
    exchange_destination_top_down: bool,
    exchange_source_top_down: bool,
    exchange_scramble: Option<u32>,
    remove_extra_first: bool,
    push_first: bool,
}

pub fn shuffle<Sink: FnMut(StackOps)>(
    config: ShuffleConfig,
    current: &mut TrackedStack<Sink>,
    graph: &OpGraph,
) {
    let target = graph.output_values_fifo();
    let needs_early_push =
        target.iter().enumerate().any(|(position, value)| target[position + 1..].contains(value));
    let mut best: Option<(u64, Vec<StackOps>)> = None;
    for exchange_top_down in [false, true] {
        for remove_extra_first in [false, true] {
            for push_first in [false, true].into_iter().take(1 + usize::from(needs_early_push)) {
                let mut candidate_ops = Vec::new();
                let mut candidate = current.clone_with(|op| candidate_ops.push(op));
                GreedyShuffler::run_with_orders(
                    config,
                    &mut candidate,
                    target,
                    exchange_top_down,
                    exchange_top_down,
                    None,
                    remove_extra_first,
                    push_first,
                );
                let candidate_cost = crate::stack::gas_cost(&candidate_ops, config);
                if best.as_ref().is_none_or(|(best_cost, _)| candidate_cost < *best_cost) {
                    best = Some((candidate_cost, candidate_ops));
                }
            }
        }
    }
    if graph.total_ops() == 0 {
        for seed in 1_u32..32 {
            let mut candidate_ops = Vec::new();
            let mut candidate = current.clone_with(|op| candidate_ops.push(op));
            GreedyShuffler::run_with_orders(
                config,
                &mut candidate,
                target,
                true,
                true,
                Some(seed.wrapping_mul(0x9e37_79b9)),
                seed & 1 != 0,
                false,
            );
            let candidate_cost = crate::stack::gas_cost(&candidate_ops, config);
            if best.as_ref().is_none_or(|(best_cost, _)| candidate_cost < *best_cost) {
                best = Some((candidate_cost, candidate_ops));
            }
        }
    }
    let (_, best_ops) = best.expect("shuffler must evaluate at least one strategy");
    for op in best_ops {
        match op {
            StackOps::Pop => current.pop(),
            StackOps::Swap(depth) => current.swap(depth),
            StackOps::Dup(depth) => current.dup(depth),
            StackOps::Store(expected) => assert_eq!(current.spill_top(), expected),
            StackOps::Load(allocation) => current.load(allocation),
            StackOps::Exchange(_, _)
            | StackOps::Op(_)
            | StackOps::Flipped(_)
            | StackOps::CallRetPush(_) => {
                unreachable!("shuffler produced an unsupported operation")
            }
        }
    }
}

const LIMIT: u32 = 100_000;

impl<'a, Sink: FnMut(StackOps)> GreedyShuffler<'a, Sink> {
    #[cfg(test)]
    fn run_with_exchange_order(
        config: ShuffleConfig,
        current: &'a mut TrackedStack<Sink>,
        target: &'a [ValueNodeId],
        exchange_top_down: bool,
    ) {
        Self::run_with_orders(
            config,
            current,
            target,
            exchange_top_down,
            exchange_top_down,
            None,
            false,
            false,
        );
    }

    fn run_with_orders(
        config: ShuffleConfig,
        current: &'a mut TrackedStack<Sink>,
        target: &'a [ValueNodeId],
        exchange_destination_top_down: bool,
        exchange_source_top_down: bool,
        exchange_scramble: Option<u32>,
        remove_extra_first: bool,
        push_first: bool,
    ) {
        let mut this = Self {
            complete_at_bottom: 0,
            current,
            target,
            max_swap_depth: FromTop::new(config.max_swap_depth.into()),
            max_dup_depth: FromTop::new(config.max_dup_depth.into()),
            exchange_destination_top_down,
            exchange_source_top_down,
            exchange_scramble,
            remove_extra_first,
            push_first,
        };

        this.update_complete_at_bottom();
        this.shrink();
        this.grow();
        this.cleanup_unneeded_top();
    }

    fn cleanup_unneeded_top(&mut self) {
        while self.current.len().to_usize() > self.target.len() {
            self.current.pop();
        }
    }

    #[track_caller]
    fn swap(&mut self, i: FromTop<CurrentStack>) {
        if i == FromTop::new(0) {
            return;
        }
        assert!(i <= self.max_swap_depth, "invalid swap depth");
        self.current.swap(i.0.try_into().expect("overflow despite assert"));
    }

    #[track_caller]
    fn dup(&mut self, i: FromTop<CurrentStack>) {
        assert!(i <= self.max_dup_depth, "invalid dup depth");
        self.current.dup(i.0.try_into().expect("overflow despite assert"));
    }

    #[track_caller]
    fn target_to(&self, i: FromTop<TargetStack>) -> FromBottom {
        FromBottom(self.target.len() - i.0 - 1)
    }

    #[track_caller]
    fn current_to(&self, i: FromTop<CurrentStack>) -> FromBottom {
        FromBottom(self.current.fifo().len() - i.0 - 1)
    }

    #[track_caller]
    fn to_current(&self, i: FromBottom) -> FromTop<CurrentStack> {
        FromTop::new(self.current.fifo().len() - i.0 - 1)
    }

    fn current_len(&self) -> FromTop<CurrentStack> {
        FromTop::new(self.current.len().into())
    }

    #[track_caller]
    fn target<I: StackIndex<TargetStack>>(&self, index: I) -> I::Output<'_> {
        index.index(self.target)
    }

    #[track_caller]
    fn current<I: StackIndex<CurrentStack>>(&self, index: I) -> I::Output<'_> {
        index.index(self.current.fifo())
    }

    fn update_complete_at_bottom(&mut self) {
        let mut newly_complete = 0;
        // If `0` complete we want all values including the bottom most (`..=FromBottom(0)`), if
        // `1` is complete we want to skip the bottom most value, giving us the range
        // `..=FromBottom(1)` and so on.
        for (current, target, i) in self.iter_pairwise(FromBottom(self.complete_at_bottom)) {
            if current != target {
                break;
            }

            let needed_further_up = self.target(..i).contains(&target);
            if needed_further_up {
                // Determining whether it's worth retrieving a needed value by unspilling is
                // deferred to the rest of the algorithm which is why spilled is not checked.
                let another_copy_exists_further_up = self.current(..i).contains(&target);
                if !another_copy_exists_further_up {
                    break;
                }
            }

            newly_complete += 1;
        }

        self.complete_at_bottom += newly_complete;
    }

    fn shrink(&mut self) {
        let mut limit = LoopLimit::max(LIMIT);

        let can_access_length = self.max_swap_depth + 1;
        while {
            let need_access_length = self.current_len() - self.complete_at_bottom;
            can_access_length < need_access_length
        } {
            limit.tick();
            let stepped = self.pop_unneeded()
                || (self.remove_extra_first
                    && (self.pop_extra() || self.swap_and_pop_extra() || self.pop_duplicate()))
                || self.swap_to_correct_position()
                || self.pop_extra()
                || self.swap_and_pop_extra()
                || self.pop_duplicate();
            if !stepped {
                self.current.spill_top();
            }
            self.update_complete_at_bottom();
        }
    }

    fn grow(&mut self) {
        let mut limit = LoopLimit::max(LIMIT);
        while self.complete_at_bottom < self.target.len() {
            limit.tick();
            let current_incomplete = self.current.len().to_usize() > self.complete_at_bottom;
            let pushed = self.push_first
                && self.can_push()
                && (self.unspill_unavailable_horizon()
                    || self.dup_needed()
                    || self.unspill_needed());
            let stepped = pushed
                || if current_incomplete {
                    self.pop_unneeded()
                        || self.swap_to_correct_position()
                        || self.exchange_via_top()
                        || self.pop_extra()
                } else {
                    false
                };
            if !stepped {
                if self.can_push() {
                    assert!(
                        self.unspill_unavailable_horizon()
                            || self.dup_needed()
                            || self.unspill_needed()
                    );
                } else {
                    self.current.spill_top();
                }
            }
            self.update_complete_at_bottom();
        }
    }

    fn is_unneeded(&self, value: ValueNodeId) -> bool {
        if self.target.len() == self.complete_at_bottom {
            return true;
        }
        !self.target(..=FromBottom(self.complete_at_bottom)).contains(&value)
    }

    fn pop_unneeded(&mut self) -> bool {
        let top = self.current(FromTop::new(0));
        if self.is_unneeded(top) {
            self.current.pop();
            true
        } else {
            false
        }
    }

    #[track_caller]
    fn iter_pairwise<'s>(
        &'s self,
        mut bottom_up_start: FromBottom,
    ) -> impl Iterator<Item = (ValueNodeId, ValueNodeId, FromBottom)> + 's {
        let current = if self.current.is_empty() || {
            let highest_from_bottom = self.current_to(FromTop::new(0));
            highest_from_bottom < bottom_up_start
        } {
            &[]
        } else {
            self.current(..=bottom_up_start)
        };
        let target = if self.target.is_empty() || {
            let highest_from_bottom = self.target_to(FromTop::new(0));
            highest_from_bottom < bottom_up_start
        } {
            &[]
        } else {
            self.target(..=bottom_up_start)
        };

        current.iter().rev().zip(target.iter().rev()).map(move |(&current_value, &target_value)| {
            (current_value, target_value, bottom_up_start.get_and_inc())
        })
    }

    fn swap_to_correct_position(&mut self) -> bool {
        if self.current.len().to_usize() <= self.complete_at_bottom {
            return false;
        }

        let top = self.current(FromTop::new(0));

        let max_search_depth = self
            .max_swap_depth
            .min(self.to_current(FromBottom(self.complete_at_bottom)))
            .min(self.current_len() - 1);

        let swap_idx = self
            .iter_pairwise(self.current_to(max_search_depth))
            .find_map(|(current, target, i)| (current != top && target == top).then_some(i));

        if let Some(idx) = swap_idx {
            self.swap(self.to_current(idx));
            return true;
        }

        false
    }

    fn is_extra(&self, value: ValueNodeId) -> bool {
        let first_incorrect_from_bottom = FromBottom(self.complete_at_bottom);
        let target_count =
            self.target(..=first_incorrect_from_bottom).iter().filter(|&&v| v == value).count();
        let current_count =
            self.current(..=first_incorrect_from_bottom).iter().filter(|&&v| v == value).count();
        current_count > target_count
    }

    fn pop_extra(&mut self) -> bool {
        let top = self.current(FromTop::new(0));
        if self.is_extra(top) {
            self.current.pop();
            true
        } else {
            false
        }
    }

    fn swap_and_pop_extra(&mut self) -> bool {
        if self.current.is_empty() {
            return false;
        }

        let max_search_depth = self
            .max_swap_depth
            .min(self.to_current(FromBottom(self.complete_at_bottom)))
            .min(self.current_len() - 1);
        let mut idx = self.current_to(max_search_depth);

        let swap_idx = self
            .current(..=idx)
            .iter()
            .rev()
            .find_map(|&value| self.is_extra(value).then_some(idx.get_and_inc()));

        if let Some(swap_idx) = swap_idx {
            self.swap(self.to_current(swap_idx));
            self.current.pop();
            return true;
        }

        false
    }

    fn is_duplicate(&self, value: ValueNodeId) -> bool {
        let current_count = self
            .current(..=FromBottom(self.complete_at_bottom))
            .iter()
            .filter(|&&v| v == value)
            .count();
        current_count >= 2
    }

    fn pop_duplicate(&mut self) -> bool {
        let top = self.current(FromTop::new(0));
        if self.is_duplicate(top) {
            self.current.pop();
            true
        } else {
            false
        }
    }

    fn exchange_via_top(&mut self) -> bool {
        if self.current.is_empty() {
            return false;
        }

        if self.exchange_scramble.is_none() && !self.exchange_destination_top_down {
            let max_swap_depth = self.current_to(
                self.max_swap_depth
                    .min(self.to_current(FromBottom(self.complete_at_bottom)))
                    .min(self.current_len() - 1),
            );
            let exchange =
                self.iter_pairwise(max_swap_depth).find_map(|(current, target, destination)| {
                    if current == target {
                        return None;
                    }
                    let source = self.iter_pairwise(max_swap_depth).find_map(
                        |(source, target_at_source, source_index)| {
                            (source != target_at_source && source == target).then_some(source_index)
                        },
                    )?;
                    Some((source, destination))
                });
            if let Some((source, destination)) = exchange {
                self.swap(self.to_current(source));
                self.swap(self.to_current(destination));
                return true;
            }
            return false;
        }

        let max_swap_depth = self
            .max_swap_depth
            .min(self.to_current(FromBottom(self.complete_at_bottom)))
            .min(self.current_len() - 1);
        if self.exchange_scramble.is_none() {
            for destination_depth in 1..=max_swap_depth.0 {
                let destination_depth = FromTop::new(destination_depth);
                let destination = self.current_to(destination_depth);
                if destination.0 >= self.target.len() {
                    continue;
                }
                let current = self.current(destination);
                let target = self.target(destination);
                if current == target {
                    continue;
                }
                for source_depth in 0..=max_swap_depth.0 {
                    let source_depth = FromTop::new(source_depth);
                    let source = self.current_to(source_depth);
                    let source_is_incorrect = source.0 >= self.target.len()
                        || self.current(source) != self.target(source);
                    if self.current(source) == target && source_is_incorrect {
                        self.swap(source_depth);
                        self.swap(destination_depth);
                        return true;
                    }
                }
            }
            return false;
        }

        let mut destination_depths = (0..=max_swap_depth.0).collect::<SmallVec<[_; 17]>>();
        let mut source_depths = destination_depths.clone();
        if !self.exchange_destination_top_down {
            destination_depths.reverse();
        }
        if !self.exchange_source_top_down {
            source_depths.reverse();
        }
        let mut exchanges = SmallVec::<[(usize, usize); 64]>::new();
        for destination_depth in destination_depths {
            let destination = self.current_to(FromTop::new(destination_depth));
            if destination.0 >= self.target.len() {
                continue;
            }
            let current = self.current(destination);
            let target = self.target(destination);
            if current == target {
                continue;
            }
            for &source_depth in &source_depths {
                let source = self.current_to(FromTop::new(source_depth));
                let source_is_incorrect =
                    source.0 >= self.target.len() || self.current(source) != self.target(source);
                if self.current(source) == target && source_is_incorrect {
                    if self.exchange_scramble.is_none() {
                        self.swap(FromTop::new(source_depth));
                        self.swap(FromTop::new(destination_depth));
                        return true;
                    }
                    exchanges.push((source_depth, destination_depth));
                }
            }
        }
        let exchange = if let Some(seed) = &mut self.exchange_scramble {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 17;
            *seed ^= *seed << 5;
            exchanges.get((*seed as usize) % exchanges.len().max(1)).copied()
        } else {
            exchanges.first().copied()
        };
        if let Some((source, destination)) = exchange {
            self.swap(FromTop::new(source));
            self.swap(FromTop::new(destination));
            return true;
        }

        false
    }

    fn can_push(&self) -> bool {
        if self.current_len() <= self.max_swap_depth {
            // Can grow because bottom will remain accessible if grown by 1.
            return true;
        }

        let horizon_idx = self.current_to(self.max_swap_depth);
        let value = self.target(horizon_idx);
        let current = self.current(horizon_idx);

        if current != value {
            return false;
        }

        let needed_further_up = self.target(..horizon_idx).contains(&value);
        if needed_further_up {
            let another_copy_accessible = self.current(..horizon_idx).contains(&value)
                || self.current.get_spilled(value).is_some();
            if !another_copy_accessible {
                return false;
            }
        }

        true
    }

    fn unspill_unavailable_horizon(&mut self) -> bool {
        if self.current_len() < self.max_swap_depth {
            // We could push at least 2 values and the horizon would still remain accessible
            // via swaps.
            return false;
        }

        let horizon_idx = self.current_to(self.max_swap_depth - 1);
        let target = self.target(horizon_idx);
        let current = self.current(horizon_idx);
        if target != current && !self.current(..self.max_swap_depth).contains(&target) {
            self.current.unspill(target);
            return true;
        }

        false
    }

    fn dup_needed(&mut self) -> bool {
        if self.current.is_empty() {
            return false;
        }

        let max_dup_depth = self.max_dup_depth.min(self.current_len() - 1);

        let search_depth = self.current_to(max_dup_depth);
        let dup_idx = self.iter_pairwise(search_depth).find_map(|(_current, target, _i)| {
            let required_copies =
                self.target(..=search_depth).iter().filter(|&&v| v == target).count();

            let mut available_copies = 0;
            let mut dup_idx = None;
            for i in Span::new(FromTop::new(0), self.to_current(search_depth) + 1).iter() {
                if self.current(i) == target {
                    available_copies += 1;
                    dup_idx = dup_idx.or(Some(i));
                }
            }
            dup_idx.filter(|_| available_copies < required_copies)
        });

        if let Some(dup_idx) = dup_idx {
            self.dup(dup_idx);
            return true;
        }

        false
    }

    fn unspill_needed(&mut self) -> bool {
        let max_dup_depth_exclusive = (self.max_dup_depth + 1).min(self.current_len());
        for &value in self.target(..=FromBottom(self.complete_at_bottom)).iter().rev() {
            if !self.current(..max_dup_depth_exclusive).contains(&value) {
                self.current.unspill(value);
                return true;
            }
        }

        false
    }
}
