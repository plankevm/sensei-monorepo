//! Inspired by the "Treegraph-based Instruction Scheduling for Stack-based Virtual Machines" by J.
//! Park, J. Park, W. Song et. al.
//!
//! Adapted to take effects into account, as well as taking advantage of flippable operations.

use crate::{
    op_graph::{
        OpGraph, OpGraphBuilder, OpNodeId, OpNodeKind, ValueNodeId, builder::AddingGraphOps,
    },
    stack::StackOps,
};
use plank_core::{DenseIndexMap, DenseIndexSet, IndexVec};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TreeStep {
    pub operation: OpNodeId,
    pub flipped: bool,
}

#[derive(Debug)]
pub struct TreeGraph {
    pub graph: OpGraph,
    flipped: DenseIndexSet<OpNodeId>,
    trees: IndexVec<OpNodeId, Vec<OpNodeId>>,
}

impl TreeGraph {
    pub fn original_operations(&self, operation: OpNodeId) -> impl Iterator<Item = TreeStep> {
        self.trees[operation]
            .iter()
            .map(|&operation| TreeStep { operation, flipped: self.flipped.contains(operation) })
    }

    pub(crate) fn expand_schedule(
        &self,
        original: &OpGraph,
        schedule: &[StackOps],
    ) -> Box<[StackOps]> {
        let mut operations = DenseIndexMap::with_capacity(self.graph.total_ops() as usize);
        let mut return_dest_pushes = DenseIndexMap::with_capacity(self.graph.total_ops() as usize);
        for tree_operation in self.graph.op_ids() {
            match self.graph.get_op(tree_operation).kind {
                OpNodeKind::Flippable(operation) | OpNodeKind::Normal(operation) => {
                    operations.insert_no_prev(operation, tree_operation);
                }
                OpNodeKind::RetDestPush(operation) => {
                    return_dest_pushes.insert_no_prev(operation, tree_operation);
                }
            }
        }

        let mut expanded = Vec::with_capacity(original.total_ops() as usize + schedule.len());
        for &scheduled in schedule {
            let (tree_operation, externally_flipped) = match scheduled {
                StackOps::Op(operation) => (operations.get(operation).copied(), false),
                StackOps::Flipped(operation) => (operations.get(operation).copied(), true),
                StackOps::CallRetPush(operation) => {
                    (return_dest_pushes.get(operation).copied(), false)
                }
                operation => {
                    expanded.push(operation);
                    continue;
                }
            };
            let tree_operation =
                tree_operation.expect("scheduled operation missing from tree graph");
            if externally_flipped {
                assert!(matches!(self.graph.get_op(tree_operation).kind, OpNodeKind::Flippable(_)));
            }
            let root = *self.trees[tree_operation].last().expect("empty tree");
            expanded.extend(self.original_operations(tree_operation).map(|step| {
                let flipped = step.flipped ^ (externally_flipped && step.operation == root);
                match original.get_op(step.operation).kind {
                    OpNodeKind::Flippable(operation) if flipped => StackOps::Flipped(operation),
                    OpNodeKind::Flippable(operation) | OpNodeKind::Normal(operation) => {
                        StackOps::Op(operation)
                    }
                    OpNodeKind::RetDestPush(operation) => StackOps::CallRetPush(operation),
                }
            }));
        }
        expanded.into_boxed_slice()
    }
}

pub fn build_tree_graph(original: &OpGraph) -> TreeGraph {
    let total_ops = original.total_ops() as usize;
    let total_values = original.total_values() as usize;
    let mut original_to_value = DenseIndexMap::with_capacity(total_values);
    let mut builder = OpGraphBuilder::with_capacity(total_ops, total_values);
    for input in original.input_values_fifo() {
        original_to_value.insert_no_prev(input, builder.push_input_value());
    }

    TreeGraphBuilder {
        original,
        original_to_root: DenseIndexMap::with_capacity(total_ops),
        completed: DenseIndexMap::with_capacity(total_ops),
        materialization_order: Vec::with_capacity(total_ops),
        builder: builder.end_inputs_begin_ops(),
        original_to_value,
        trees: IndexVec::with_capacity(total_ops),
        flipped: DenseIndexSet::with_capacity_in_bits(total_ops),
        emitted: DenseIndexMap::with_capacity(total_ops),
        emitting: DenseIndexSet::with_capacity_in_bits(total_ops),
    }
    .build_trees()
    .into_graph()
}

struct TreeGraphBuilder<'graph> {
    original: &'graph OpGraph,
    original_to_root: DenseIndexMap<OpNodeId, OpNodeId>,
    completed: DenseIndexMap<OpNodeId, Vec<OpNodeId>>,
    materialization_order: Vec<OpNodeId>,
    builder: OpGraphBuilder<AddingGraphOps>,
    original_to_value: DenseIndexMap<ValueNodeId, ValueNodeId>,
    trees: IndexVec<OpNodeId, Vec<OpNodeId>>,
    flipped: DenseIndexSet<OpNodeId>,
    emitted: DenseIndexMap<OpNodeId, OpNodeId>,
    emitting: DenseIndexSet<OpNodeId>,
}

impl TreeGraphBuilder<'_> {
    fn fold_consumer(&self, operation: OpNodeId) -> Option<OpNodeId> {
        let [output] = self.original.get_op(operation).outputs_fifo else {
            return None;
        };
        if self.original.output_values_fifo().contains(output) {
            return None;
        }

        let consumers = self.original.get_consumers(*output);
        if consumers.count_members() != 1 {
            return None;
        }
        let consumer = consumers.iter().next().expect("single consumer disappeared");
        (self
            .original
            .get_op(consumer)
            .inputs_fifo
            .iter()
            .filter(|&&input| input == *output)
            .count()
            == 1)
            .then_some(consumer)
    }

    fn build_operand(&mut self, consumer: OpNodeId, input: ValueNodeId) -> Option<Vec<OpNodeId>> {
        let producer = self.original.get_producer(input)?;
        if self.fold_consumer(producer) == Some(consumer) {
            assert!(
                self.original_to_root.get(producer).is_none(),
                "foldable producer was already built"
            );
            Some(self.build_pending(producer))
        } else {
            self.ensure_materialized(producer);
            None
        }
    }

    fn ensure_inputs_materialized(&mut self, operation: OpNodeId, start: usize) {
        let input_count = self.original.get_op(operation).inputs_fifo.len();
        for position in start..input_count {
            let input = self.original.get_op(operation).inputs_fifo[position];
            if let Some(producer) = self.original.get_producer(input) {
                self.ensure_materialized(producer);
            }
        }
    }

    fn build_pending(&mut self, root: OpNodeId) -> Vec<OpNodeId> {
        assert!(self.original_to_root.get(root).is_none(), "built an operation twice");
        let op = self.original.get_op(root);
        if matches!(op.kind, OpNodeKind::Flippable(_)) && op.inputs_fifo.len() >= 2 {
            self.build_flippable(root)
        } else {
            self.fold_deeper_operands(root, vec![root], 0, false)
        }
    }

    fn build_flippable(&mut self, root: OpNodeId) -> Vec<OpNodeId> {
        let first_input = self.original.get_op(root).inputs_fifo[0];
        let second_input = self.original.get_op(root).inputs_fifo[1];
        let first = self.build_operand(root, first_input);
        let second = self.build_operand(root, second_input);

        let selection = match (first.as_deref(), second.as_deref()) {
            (Some(first), Some(second)) => self
                .leading_tree(root, second, Some(first), false)
                .map(|tree| (tree, true, false))
                .or_else(|| {
                    self.leading_tree(root, first, Some(second), true)
                        .map(|tree| (tree, true, true))
                })
                .or_else(|| {
                    self.leading_tree(root, first, None, false).map(|tree| (tree, false, false))
                })
                .or_else(|| {
                    self.leading_tree(root, second, None, true).map(|tree| (tree, false, true))
                }),
            (Some(first), None) => {
                self.leading_tree(root, first, None, false).map(|tree| (tree, false, false))
            }
            (None, Some(second)) => {
                self.leading_tree(root, second, None, true).map(|tree| (tree, false, true))
            }
            (None, None) => None,
        };
        let (mut tree, folded_both, root_flipped) =
            selection.unwrap_or_else(|| (vec![root], false, false));

        for operand in [first, second].into_iter().flatten() {
            let operand_root = *operand.last().expect("empty operand tree");
            if !tree.contains(&operand_root) {
                self.materialize(operand);
            }
        }

        if folded_both {
            tree = self.fold_deeper_operands(root, tree, 2, root_flipped);
        } else {
            self.ensure_inputs_materialized(root, 2);
        }
        if root_flipped {
            assert!(self.flipped.add(root));
        }
        tree
    }

    fn leading_tree(
        &self,
        root: OpNodeId,
        earliest: &[OpNodeId],
        later: Option<&[OpNodeId]>,
        root_flipped: bool,
    ) -> Option<Vec<OpNodeId>> {
        let later_len = later.map_or(0, <[OpNodeId]>::len);
        let mut tree = Vec::with_capacity(earliest.len() + later_len + 1);
        tree.extend_from_slice(earliest);
        if let Some(later) = later {
            tree.extend_from_slice(later);
        }
        tree.push(root);
        self.is_valid_tree(&tree, root_flipped).then_some(tree)
    }

    fn fold_deeper_operands(
        &mut self,
        root: OpNodeId,
        mut tree: Vec<OpNodeId>,
        start: usize,
        root_flipped: bool,
    ) -> Vec<OpNodeId> {
        let input_count = self.original.get_op(root).inputs_fifo.len();
        for position in start..input_count {
            let input = self.original.get_op(root).inputs_fifo[position];
            let Some(mut operand) = self.build_operand(root, input) else {
                self.ensure_inputs_materialized(root, position + 1);
                break;
            };

            let operand_len = operand.len();
            operand.append(&mut tree);
            if self.is_valid_tree(&operand, root_flipped) {
                tree = operand;
            } else {
                tree = operand.split_off(operand_len);
                self.materialize(operand);
                self.ensure_inputs_materialized(root, position + 1);
                break;
            }
        }
        tree
    }

    fn is_valid_tree(&self, steps: &[OpNodeId], root_flipped: bool) -> bool {
        let mut operations =
            DenseIndexSet::with_capacity_in_bits(self.original.total_ops() as usize);
        for &operation in steps {
            assert!(operations.add(operation), "operation appears twice in a tree");
        }

        let mut seen = DenseIndexSet::with_capacity_in_bits(self.original.total_ops() as usize);
        let mut external = Vec::new();
        for &operation in steps {
            for predecessor in self.original.get_predecessors(operation).iter() {
                if operations.contains(predecessor) {
                    if !seen.contains(predecessor) {
                        return false;
                    }
                } else {
                    external.push(predecessor);
                }
            }
            seen.add(operation);
        }

        // Original-graph reachability alone misses cycles introduced by earlier contractions.
        // Every member of an existing tree must move together with its root.
        seen.clear();
        while let Some(predecessor) = external.pop() {
            if operations.contains(predecessor) {
                return false;
            }
            if !seen.add(predecessor) {
                continue;
            }
            external.extend(self.original.get_predecessors(predecessor).iter());
            if let Some(&root) = self.original_to_root.get(predecessor) {
                external.extend(self.completed[root].iter().copied());
            }
        }

        self.tree_inputs(steps, root_flipped).is_some()
    }

    fn tree_inputs(&self, steps: &[OpNodeId], root_flipped: bool) -> Option<Vec<ValueNodeId>> {
        let mut stack = Vec::new();
        let mut inputs_fifo = Vec::new();
        for (step_position, &step) in steps.iter().enumerate() {
            let op = self.original.get_op(step);
            let flipped =
                self.flipped.contains(step) || (root_flipped && step_position == steps.len() - 1);
            for position in 0..op.inputs_fifo.len() {
                let position = if flipped && position < 2 { 1 - position } else { position };
                let input = op.inputs_fifo[position];
                match stack.last() {
                    Some(&actual) if actual == input => {
                        stack.pop();
                    }
                    Some(_) => return None,
                    None => inputs_fifo.push(input),
                }
            }
            stack.extend(op.outputs_fifo.iter().rev().copied());
        }
        Some(inputs_fifo)
    }

    fn materialize(&mut self, tree: Vec<OpNodeId>) -> OpNodeId {
        let root = *tree.last().expect("empty tree");
        for &operation in &tree {
            self.original_to_root.insert_no_prev(operation, root);
        }
        self.completed.insert_no_prev(root, tree);
        self.materialization_order.push(root);
        root
    }

    fn ensure_materialized(&mut self, operation: OpNodeId) -> OpNodeId {
        match self.original_to_root.get(operation).copied() {
            Some(root) => root,
            None => {
                let tree = self.build_pending(operation);
                self.materialize(tree)
            }
        }
    }

    fn build_trees(mut self) -> Self {
        let original = self.original;
        for operation in original.op_ids() {
            if self.fold_consumer(operation).is_none() {
                self.ensure_materialized(operation);
            }
        }
        assert_eq!(self.original_to_root.iter().count(), self.original.total_ops() as usize);
        self
    }

    fn tree_root(&self, operation: OpNodeId) -> OpNodeId {
        self.original_to_root[operation]
    }

    fn emit_tree(&mut self, root: OpNodeId) -> OpNodeId {
        if let Some(&operation) = self.emitted.get(root) {
            return operation;
        }
        assert!(self.emitting.add(root), "cycle in tree graph");

        let mut predecessors =
            DenseIndexSet::with_capacity_in_bits(self.original.total_ops() as usize);
        for &operation in &self.completed[root] {
            for predecessor in self.original.get_predecessors(operation).iter() {
                let predecessor_tree = self.tree_root(predecessor);
                if predecessor_tree != root {
                    predecessors.add(predecessor_tree);
                }
            }
        }
        for predecessor in &predecessors {
            self.emit_tree(predecessor);
        }

        let tree = self.completed.remove(root).expect("tree disappeared before emission");
        let inputs_fifo = self.tree_inputs(&tree, false).expect("materialized an invalid tree");
        let original_root = self.original.get_op(root);
        let leading_operand_is_folded = original_root.inputs_fifo.iter().take(2).any(|&input| {
            self.original
                .get_producer(input)
                .is_some_and(|producer| self.tree_root(producer) == root)
        });
        let kind = match original_root.kind {
            // Folding either leading operand fixes its position inside the tree, so the virtual
            // operation can no longer exchange those operands when it is scheduled.
            OpNodeKind::Flippable(operation) if leading_operand_is_folded => {
                OpNodeKind::Normal(operation)
            }
            kind => kind,
        };
        let mut operation = self.builder.begin_op(kind);
        let new_id = operation.id();
        for predecessor in &predecessors {
            operation.add_predecessor(self.emitted[predecessor]);
        }
        for input in inputs_fifo {
            operation.add_input(self.original_to_value[input]);
        }
        let mut operation = operation.end_inputs_begin_outputs();
        for &output in original_root.outputs_fifo {
            let mapped = operation.add_output();
            self.original_to_value.insert_no_prev(output, mapped);
        }

        assert_eq!(self.trees.push(tree), new_id);
        self.emitted.insert_no_prev(root, new_id);
        assert!(self.emitting.remove(root));
        new_id
    }

    fn into_graph(mut self) -> TreeGraph {
        for root in std::mem::take(&mut self.materialization_order) {
            self.emit_tree(root);
        }

        let mut builder = self.builder.end_ops_begin_end_stack();
        for &original in self.original.output_values_fifo() {
            builder.push_end_stack_value(self.original_to_value[original]);
        }

        TreeGraph { graph: builder.finish(), flipped: self.flipped, trees: self.trees }
    }
}

#[cfg(test)]
mod schedule_tests;
#[cfg(test)]
mod tests;
