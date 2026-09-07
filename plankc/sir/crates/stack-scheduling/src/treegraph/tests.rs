use plank_core::Idx;
use plank_test_utils::dedent_preserve_blank_lines;
use pretty_assertions::assert_str_eq;
use sir_data::OperationIdx;

use super::{TreeGraph, build_tree_graph};
use crate::op_graph::{OpGraph, OpGraphBuilder, OpNodeKind};

fn assert_snapshot(input: &OpGraph, trees: &TreeGraph, expected: &str) {
    let expected = dedent_preserve_blank_lines(expected);
    assert_str_eq!(format_snapshot(input, trees).trim(), expected.trim());
}

fn format_snapshot(input: &OpGraph, trees: &TreeGraph) -> String {
    let input = crate::display::graph(input);
    let tree = crate::display::graph_with_annotations(&trees.graph, |operation| {
        let operations = trees
            .original_operations(operation)
            .map(|step| {
                if step.flipped {
                    format!("flipped(op{})", step.operation.get())
                } else {
                    format!("op{}", step.operation.get())
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        Some(format!("tree: [{operations}]"))
    });
    format!("input graph:\n{input}\n\ntree graph:\n{tree}")
}

fn partial_binary_tree() -> OpGraph {
    let mut builder = OpGraphBuilder::with_capacity(3, 4);
    let external = builder.push_input_value();
    let mut builder = builder.end_inputs_begin_ops();

    let high = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let deep = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(deep);
        op.add_input(external);
        op.end_inputs_begin_outputs().add_output()
    };

    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    builder.finish()
}

#[test]
fn constructs_partial_binary_tree_in_depth_first_order() {
    let input = partial_binary_tree();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: [v0]
            v1 = op0()
            v2 = op1()
            v3 = op2(v1, v2, v0)
            outputs: [v3]

            tree graph:
            inputs: [v0]
            v1 = op0(v0) ; tree: [op1, op0, op2]
            outputs: [v1]
        "#,
    );
}

fn three_operand_tree() -> OpGraph {
    let builder = OpGraphBuilder::with_capacity(4, 4);
    let mut builder = builder.end_inputs_begin_ops();
    let high = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let middle = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let deep = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(middle);
        op.add_input(deep);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    builder.finish()
}

#[test]
fn constructs_three_operand_tree_in_depth_first_order() {
    let input = three_operand_tree();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            v1 = op1()
            v2 = op2()
            v3 = op3(v0, v1, v2)
            outputs: [v3]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op2, op1, op0, op3]
            outputs: [v0]
        "#,
    );
}

fn multi_use_tree_edge() -> OpGraph {
    let builder = OpGraphBuilder::with_capacity(3, 3);
    let mut builder = builder.end_inputs_begin_ops();
    let shared = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let first = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_input(shared);
        op.end_inputs_begin_outputs().add_output()
    };
    let second = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_input(shared);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(first);
    builder.push_end_stack_value(second);
    builder.finish()
}

#[test]
fn materializes_multi_use_operand_as_its_own_virtual_operation() {
    let input = multi_use_tree_edge();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            v1 = op1(v0)
            v2 = op2(v0)
            outputs: [v1, v2]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op0]
            v1 = op1(v0) ; tree: [op1]
            v2 = op2(v0) ; tree: [op2]
            outputs: [v1, v2]
        "#,
    );
}

fn final_output_tree_edge() -> OpGraph {
    let builder = OpGraphBuilder::with_capacity(2, 2);
    let mut builder = builder.end_inputs_begin_ops();
    let preserved = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let consumed = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_input(preserved);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(preserved);
    builder.push_end_stack_value(consumed);
    builder.finish()
}

#[test]
fn materializes_an_operand_that_is_also_a_final_output() {
    let input = final_output_tree_edge();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            v1 = op1(v0)
            outputs: [v0, v1]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op0]
            v1 = op1(v0) ; tree: [op1]
            outputs: [v0, v1]
        "#,
    );
}

#[test]
fn preserves_flippability_when_neither_leading_operand_is_folded() {
    let mut builder = OpGraphBuilder::with_capacity(1, 3);
    let high = builder.push_input_value();
    let deep = builder.push_input_value();
    let mut builder = builder.end_inputs_begin_ops();
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Flippable(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(deep);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    let input = builder.finish();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: [v0, v1]
            v2 = op0_f(v0, v1)
            outputs: [v2]

            tree graph:
            inputs: [v0, v1]
            v2 = op0_f(v0, v1) ; tree: [op0]
            outputs: [v2]
        "#,
    );
}

#[test]
fn removes_flippability_when_the_first_leading_operand_is_folded() {
    let mut builder = OpGraphBuilder::with_capacity(2, 3);
    let deep = builder.push_input_value();
    let mut builder = builder.end_inputs_begin_ops();
    let high = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Flippable(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(deep);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    let input = builder.finish();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: [v0]
            v1 = op0()
            v2 = op1_f(v1, v0)
            outputs: [v2]

            tree graph:
            inputs: [v0]
            v1 = op0(v0) ; tree: [op0, op1]
            outputs: [v1]
        "#,
    );
}

#[test]
fn removes_flippability_when_the_second_leading_operand_is_folded() {
    let mut builder = OpGraphBuilder::with_capacity(2, 3);
    let high = builder.push_input_value();
    let mut builder = builder.end_inputs_begin_ops();
    let deep = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.end_inputs_begin_outputs().add_output()
    };
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Flippable(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(deep);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    let input = builder.finish();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: [v0]
            v1 = op0()
            v2 = op1_f(v0, v1)
            outputs: [v2]

            tree graph:
            inputs: [v0]
            v1 = op0(v0) ; tree: [op0, flipped(op1)]
            outputs: [v1]
        "#,
    );
}

#[test]
fn folding_both_leading_operands_removes_flippability_while_preserving_internal_flip() {
    let builder = OpGraphBuilder::with_capacity(3, 3);
    let mut builder = builder.end_inputs_begin_ops();
    let (high_op, high) = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        let id = op.id();
        (id, op.end_inputs_begin_outputs().add_output())
    };
    let deep = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_predecessor(high_op);
        op.end_inputs_begin_outputs().add_output()
    };
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Flippable(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(deep);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    let input = builder.finish();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            v1 = op1() ; after: [op0]
            v2 = op2_f(v0, v1)
            outputs: [v2]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op0, op1, flipped(op2)]
            outputs: [v0]
        "#,
    );
}

#[test]
fn folds_only_the_viable_leading_operand_when_both_orders_are_interposed() {
    let input = {
        let builder = OpGraphBuilder::with_capacity(4, 3);
        let mut builder = builder.end_inputs_begin_ops();
        let (first_operation, first) = {
            let operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            let id = operation.id();
            (id, operation.end_inputs_begin_outputs().add_output())
        };
        let interposed = {
            let mut operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            operation.add_predecessor(first_operation);
            let id = operation.id();
            let _operation = operation.end_inputs_begin_outputs();
            id
        };
        let second = {
            let mut operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            operation.add_predecessor(interposed);
            operation.end_inputs_begin_outputs().add_output()
        };
        let output = {
            let mut operation = builder.begin_op(OpNodeKind::Flippable(OperationIdx::ZERO));
            operation.add_input(first);
            operation.add_input(second);
            operation.end_inputs_begin_outputs().add_output()
        };
        let mut builder = builder.end_ops_begin_end_stack();
        builder.push_end_stack_value(output);
        builder.finish()
    };
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            op1() ; after: [op0]
            v1 = op2() ; after: [op1]
            v2 = op3_f(v0, v1)
            outputs: [v2]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op0]
            op1() ; after: [op0] ; tree: [op1]
            v1 = op2(v0) ; after: [op1] ; tree: [op2, flipped(op3)]
            outputs: [v1]
        "#,
    );
}

fn effect_split_tree() -> OpGraph {
    let builder = OpGraphBuilder::with_capacity(3, 3);
    let mut builder = builder.end_inputs_begin_ops();
    let (high_op, high) = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        let id = op.id();
        (id, op.end_inputs_begin_outputs().add_output())
    };
    let deep = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_predecessor(high_op);
        op.end_inputs_begin_outputs().add_output()
    };
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_input(high);
        op.add_input(deep);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    builder.finish()
}

#[test]
fn splits_non_flippable_effect_conflict() {
    let input = effect_split_tree();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            v1 = op1() ; after: [op0]
            v2 = op2(v0, v1)
            outputs: [v2]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op0]
            v1 = op1() ; after: [op0] ; tree: [op1]
            v2 = op2(v0, v1) ; tree: [op2]
            outputs: [v2]
        "#,
    );
}

fn effect_interposed_tree() -> OpGraph {
    let builder = OpGraphBuilder::with_capacity(3, 2);
    let mut builder = builder.end_inputs_begin_ops();
    let (producer, value) = {
        let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        let id = op.id();
        (id, op.end_inputs_begin_outputs().add_output())
    };
    let interposed = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_predecessor(producer);
        let id = op.id();
        let _op = op.end_inputs_begin_outputs();
        id
    };
    let output = {
        let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
        op.add_predecessor(interposed);
        op.add_input(value);
        op.end_inputs_begin_outputs().add_output()
    };
    let mut builder = builder.end_ops_begin_end_stack();
    builder.push_end_stack_value(output);
    builder.finish()
}

#[test]
fn splits_tree_when_an_effect_is_interposed() {
    let input = effect_interposed_tree();
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            op1() ; after: [op0]
            v1 = op2(v0) ; after: [op1]
            outputs: [v1]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op0]
            op1() ; after: [op0] ; tree: [op1]
            v1 = op2(v0) ; after: [op1] ; tree: [op2]
            outputs: [v1]
        "#,
    );
}

#[test]
fn detects_crossing_dependencies_between_independent_trees() {
    let input = {
        let builder = OpGraphBuilder::with_capacity(4, 4);
        let mut builder = builder.end_inputs_begin_ops();
        let (first_leaf_operation, first_leaf) = {
            let operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            let id = operation.id();
            (id, operation.end_inputs_begin_outputs().add_output())
        };
        let (second_leaf_operation, second_leaf) = {
            let operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            let id = operation.id();
            (id, operation.end_inputs_begin_outputs().add_output())
        };
        let first_root = {
            let mut operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            operation.add_predecessor(second_leaf_operation);
            operation.add_input(first_leaf);
            operation.end_inputs_begin_outputs().add_output()
        };
        let second_root = {
            let mut operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            operation.add_predecessor(first_leaf_operation);
            operation.add_input(second_leaf);
            operation.end_inputs_begin_outputs().add_output()
        };
        let mut builder = builder.end_ops_begin_end_stack();
        builder.push_end_stack_value(first_root);
        builder.push_end_stack_value(second_root);
        builder.finish()
    };
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            v0 = op0()
            v1 = op1()
            v2 = op2(v0) ; after: [op1]
            v3 = op3(v1) ; after: [op0]
            outputs: [v2, v3]

            tree graph:
            inputs: []
            v0 = op0() ; tree: [op1]
            v1 = op1() ; after: [op0] ; tree: [op0, op2]
            v2 = op2(v0) ; after: [op1] ; tree: [op3]
            outputs: [v1, v2]
        "#,
    );
}

#[test]
fn does_not_absorb_multi_output_or_repeated_operands() {
    let input = {
        let builder = OpGraphBuilder::with_capacity(3, 4);
        let mut builder = builder.end_inputs_begin_ops();
        let (first, second) = {
            let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            let mut op = op.end_inputs_begin_outputs();
            (op.add_output(), op.add_output())
        };
        let repeated = {
            let op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            op.end_inputs_begin_outputs().add_output()
        };
        let output = {
            let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            op.add_input(first);
            op.add_input(second);
            op.add_input(repeated);
            op.add_input(repeated);
            op.end_inputs_begin_outputs().add_output()
        };
        let mut builder = builder.end_ops_begin_end_stack();
        builder.push_end_stack_value(output);
        builder.finish()
    };
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            [v0, v1] = op0()
            v2 = op1()
            v3 = op2(v0, v1, v2, v2)
            outputs: [v3]

            tree graph:
            inputs: []
            [v0, v1] = op0() ; tree: [op0]
            v2 = op1() ; tree: [op1]
            v3 = op2(v0, v1, v2, v2) ; tree: [op2]
            outputs: [v3]
        "#,
    );
}

#[test]
fn folds_operands_with_a_common_predecessor() {
    let input = {
        let builder = OpGraphBuilder::with_capacity(4, 3);
        let mut builder = builder.end_inputs_begin_ops();
        let common = {
            let operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            let id = operation.id();
            let _operation = operation.end_inputs_begin_outputs();
            id
        };
        let high = {
            let mut operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            operation.add_predecessor(common);
            operation.end_inputs_begin_outputs().add_output()
        };
        let deep = {
            let mut operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            operation.add_predecessor(common);
            operation.end_inputs_begin_outputs().add_output()
        };
        let output = {
            let mut operation = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            operation.add_input(high);
            operation.add_input(deep);
            operation.end_inputs_begin_outputs().add_output()
        };
        let mut builder = builder.end_ops_begin_end_stack();
        builder.push_end_stack_value(output);
        builder.finish()
    };
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: []
            op0()
            v0 = op1() ; after: [op0]
            v1 = op2() ; after: [op0]
            v2 = op3(v0, v1)
            outputs: [v2]

            tree graph:
            inputs: []
            op0() ; tree: [op0]
            v0 = op1() ; after: [op0] ; tree: [op2, op1, op3]
            outputs: [v0]
        "#,
    );
}

#[test]
fn folds_a_viable_partial_operand_tree() {
    let input = {
        let mut builder = OpGraphBuilder::with_capacity(3, 7);
        let high_left = builder.push_input_value();
        let high_right = builder.push_input_value();
        let deep_left = builder.push_input_value();
        let deep_right = builder.push_input_value();
        let mut builder = builder.end_inputs_begin_ops();
        let high = {
            let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            op.add_input(high_left);
            op.add_input(high_right);
            op.end_inputs_begin_outputs().add_output()
        };
        let deep = {
            let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            op.add_input(deep_left);
            op.add_input(deep_right);
            op.end_inputs_begin_outputs().add_output()
        };
        let output = {
            let mut op = builder.begin_op(OpNodeKind::Normal(OperationIdx::ZERO));
            op.add_input(high);
            op.add_input(deep);
            op.end_inputs_begin_outputs().add_output()
        };
        let mut builder = builder.end_ops_begin_end_stack();
        builder.push_end_stack_value(output);
        builder.finish()
    };
    let trees = build_tree_graph(&input);
    assert_snapshot(
        &input,
        &trees,
        r#"
            input graph:
            inputs: [v0, v1, v2, v3]
            v4 = op0(v0, v1)
            v5 = op1(v2, v3)
            v6 = op2(v4, v5)
            outputs: [v6]

            tree graph:
            inputs: [v0, v1, v2, v3]
            v4 = op0(v2, v3) ; tree: [op1]
            v5 = op1(v0, v1, v4) ; tree: [op0, op2]
            outputs: [v5]
        "#,
    );
}
