use plank_core::Idx;
use plank_test_utils::dedent_preserve_blank_lines;
use sir_data::{BlockView, ControlView, EthIRProgram, Operation, OperationIdx, StaticAllocId};
use sir_parser::EmitConfig;
use sir_passes::AnalysesStore;
use std::{collections::HashSet, fmt::Write};

use super::{
    ScheduledOps,
    layouts::{Layout, LayoutMember},
    op_graph::{OpGraph, ValueNodeId, build_graph_effectful},
    stack::{ShuffleConfig, StackOps},
};

#[track_caller]
fn assert_lowers_to(config: ShuffleConfig, source: &str, expected: &str) {
    let source = dedent_preserve_blank_lines(source);
    let program = sir_parser::parse_or_panic(&source, EmitConfig::init_only());

    let actual = format_scheduled(&program, config);
    let expected = dedent_preserve_blank_lines(expected);

    pretty_assertions::assert_str_eq!(actual.trim(), expected.trim());
}

fn format_scheduled(program: &EthIRProgram, config: ShuffleConfig) -> String {
    let analyses = AnalysesStore::default();
    let (lowered, layouts, next_alloc_id) = crate::schedule(program, &analyses, config);
    assert_spill_alloc_invariants(program, &lowered, next_alloc_id);

    let mut out = String::new();
    for (block_id, ops) in lowered.enumerate_idx() {
        out.push_str(&format_scheduled_block(program, &analyses, &layouts, block_id, ops, config));
    }
    out
}

pub(crate) fn format_scheduled_block(
    program: &EthIRProgram,
    analyses: &AnalysesStore,
    layouts: &super::layouts::LayoutsTracker<'_>,
    block_id: sir_data::BasicBlockId,
    ops: &[StackOps],
    config: ShuffleConfig,
) -> String {
    let Some((input_layout, output_layout)) = layouts.get_input_output(block_id) else {
        return String::new();
    };
    let block = program.block(block_id);
    let graph =
        build_graph_effectful(program, block, layouts, input_layout, output_layout, analyses);
    let mut out = String::new();

    write!(out, "@{block_id} ").unwrap();
    fmt_layout(&mut out, layouts.get_input_layout(block_id), block);
    writeln!(out).unwrap();

    let first_spill = ops
        .iter()
        .find_map(|operation| match operation {
            StackOps::Store(allocation) => Some(*allocation),
            _ => None,
        })
        .unwrap_or(program.next_static_alloc_id);
    let trace = crate::display::trace_with_operation_labels(
        &graph,
        super::BlockFinalization::from_block(block),
        config,
        first_spill,
        ops,
        |operation| format_operation(program, operation),
    );
    assert!(trace.error.is_none(), "{:?}\n{}", trace.error, trace.rendering);
    for line in trace.rendering.lines() {
        writeln!(out, "    {line}").unwrap();
    }

    write!(out, "    => ").unwrap();
    fmt_end_stack_layout(&mut out, program, &graph, layouts.get_input_layout(block_id), block);
    writeln!(out).unwrap();

    write!(out, "    ").unwrap();
    fmt_control(&mut out, block);
    writeln!(out).unwrap();
    out
}

fn assert_spill_alloc_invariants(
    program: &EthIRProgram,
    scheduled: &ScheduledOps,
    next_alloc_id: StaticAllocId,
) {
    let first_spill_alloc_id = program.next_static_alloc_id;
    let mut all_stores = HashSet::new();

    for (_, ops) in scheduled.enumerate_idx() {
        let mut block_stores = HashSet::new();
        for &op in ops {
            match op {
                StackOps::Store(id) => {
                    assert!(id >= first_spill_alloc_id, "spill allocation overlaps IR allocation");
                    assert!(
                        id < next_alloc_id,
                        "spill allocation exceeds returned allocation range"
                    );
                    assert!(all_stores.insert(id), "spill allocation reused across blocks");
                    assert!(block_stores.insert(id));
                }
                StackOps::Load(id) => {
                    assert!(block_stores.contains(&id), "load without preceding block-local store");
                }
                _ => {}
            }
        }
    }

    let total_stores = u32::try_from(all_stores.len()).expect("overflow");
    assert_eq!(first_spill_alloc_id + total_stores, next_alloc_id);
}

fn fmt_layout(out: &mut String, layout: &Layout, block: BlockView<'_>) {
    out.push('[');
    for (idx, &member) in layout.members_fifo().iter().enumerate() {
        if idx != 0 {
            out.push_str(", ");
        }
        fmt_layout_member(out, member, block);
    }
    out.push(']');
}

fn fmt_layout_member(out: &mut String, member: LayoutMember, block: BlockView<'_>) {
    match member {
        LayoutMember::ReturnDest => out.push_str("return_dest"),
        LayoutMember::InputOutput(position) => {
            let local = block.inputs()[position as usize];
            write!(out, "${local}").unwrap();
        }
        LayoutMember::Local(local) => write!(out, "${local}").unwrap(),
    }
}

fn format_operation(program: &EthIRProgram, operation: OperationIdx) -> String {
    match program.operations[operation] {
        Operation::SetSmallConst(data) => format!("const {:#x}", data.value),
        Operation::SetLargeConst(data) => {
            format!("large_const {:#x}", program.large_consts[data.value])
        }
        Operation::InternalCall(_) => format!("icall #{operation}"),
        operation => operation.kind().mnemonic().to_owned(),
    }
}

fn fmt_end_stack_layout(
    out: &mut String,
    program: &EthIRProgram,
    graph: &OpGraph,
    input_layout: &Layout,
    block: BlockView<'_>,
) {
    let terminator_inputs = terminator_input_count(block);

    out.push('[');
    let end_stack_fifo = graph.output_values_fifo();
    for (idx, &value) in end_stack_fifo.iter().enumerate() {
        if terminator_inputs != 0 && idx == terminator_inputs {
            if idx != 0 {
                out.push(' ');
            }
            out.push('|');
            if idx != end_stack_fifo.len() {
                out.push(' ');
            }
        } else if idx != 0 {
            out.push_str(", ");
        }
        fmt_value(out, program, graph, input_layout, block, value);
    }
    if terminator_inputs == end_stack_fifo.len() && terminator_inputs != 0 {
        out.push_str(" | ");
    }
    out.push(']');
}

fn terminator_input_count(block: BlockView<'_>) -> usize {
    match block.control() {
        ControlView::LastOpTerminates => {
            block.operations().last().expect("last op terminates but no last op").inputs().len()
        }
        ControlView::InternalReturn | ControlView::Branches { .. } | ControlView::Switch(_) => 1,
        ControlView::ContinuesTo(_) => 0,
    }
}

fn fmt_value(
    out: &mut String,
    program: &EthIRProgram,
    graph: &OpGraph,
    input_layout: &Layout,
    block: BlockView<'_>,
    value: ValueNodeId,
) {
    if graph.is_input(value) {
        fmt_layout_member(out, input_layout.members_fifo()[value.idx()], block);
        return;
    }

    let (source, output_position) = graph
        .op_ids()
        .find_map(|op_id| {
            graph
                .get_op(op_id)
                .outputs_fifo
                .iter()
                .position(|&output| output == value)
                .map(|output_position| (op_id, output_position))
        })
        .expect("non-input value should have source");
    let op_idx = match graph.get_op(source).kind {
        super::op_graph::OpNodeKind::Flippable(op_idx)
        | super::op_graph::OpNodeKind::Normal(op_idx) => op_idx,
        super::op_graph::OpNodeKind::RetDestPush(_) => {
            panic!("return destination push should not produce local outputs")
        }
    };
    let local = program.operations[op_idx].outputs(program)[output_position];
    write!(out, "${local}").unwrap();
}

fn fmt_control(out: &mut String, block: BlockView<'_>) {
    out.push('(');
    match block.control() {
        ControlView::LastOpTerminates => {
            let terminator = block.operations().last().expect("last op terminates but no last op");
            out.push_str(terminator.op().kind().mnemonic());
        }
        ControlView::InternalReturn => out.push_str("iret"),
        ControlView::ContinuesTo(target) => write!(out, "jmp @{target}").unwrap(),
        ControlView::Branches { non_zero_target, zero_target, .. } => {
            write!(out, "br @{non_zero_target} @{zero_target}").unwrap()
        }
        ControlView::Switch(switch) => write!(out, "switch ${}", switch.condition()).unwrap(),
    }
    out.push(')');
}

#[test]
fn lowers_terminator_inputs() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry {
                one = const 1
                two = const 2
                return one two
            }
        "#,
        r#"
        @0 []
            ; start:         []
            const 0x2      [v1]
            const 0x1  [v0, v1]
            return           []
            => []
            (return)
        "#,
    );
}

#[test]
fn lowers_binary_operation_inputs() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry {
                one = const 1
                two = const 2
                sum = add one two
                stop
            }
        "#,
        r#"
        @0 []
            ; start:         []
            const 0x2      [v1]
            const 0x1  [v0, v1]
            add            [v2]
            stop           [v2]
            => []
            (stop)
        "#,
    );
}

#[test]
fn lowers_memory_hash_and_store() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry {
                zero = const 0
                word = const 32
                two_words = const 64
                one = const 1
                first = calldataload zero
                second = calldataload word
                ptr = malloc two_words
                mstore256 ptr first
                second_ptr = add ptr word
                mstore256 second_ptr second
                hash = keccak256 ptr two_words
                sstore hash one
                stop
            }
        "#,
        r#"
        @0 []
            ; start:                                []
            const 0x1                             [v3]
            const 0x40                        [v2, v3]
            dup1                          [v2, v2, v3]
            malloc                        [v6, v2, v3]
            const 0x20                [v1, v6, v2, v3]
            dup1                  [v1, v1, v6, v2, v3]
            calldataload          [v5, v1, v6, v2, v3]
            const 0x0         [v0, v5, v1, v6, v2, v3]
            calldataload      [v4, v5, v1, v6, v2, v3]
            dup4          [v6, v4, v5, v1, v6, v2, v3]
            mstore                [v5, v1, v6, v2, v3]
            swap1                 [v1, v5, v6, v2, v3]
            dup3              [v6, v1, v5, v6, v2, v3]
            add                   [v7, v5, v6, v2, v3]
            mstore                        [v6, v2, v3]
            keccak256                         [v8, v3]
            sstore                                  []
            stop                                    []
            => []
            (stop)
        "#,
    );
}

#[test]
fn lowers_calldata_sum_loop() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry -> len0 idx0 off0 sum0 {
                zero = const 0
                len0 = calldataload zero
                idx0 = const 0
                off0 = const 32
                sum0 = const 0
                => @loop
            }
            loop len1 idx1 off1 sum1 -> len1 idx1 off1 sum1 {
                keep_going = lt idx1 len1
                => keep_going ? @body : @done
            }
            body len3 idx3 off3 sum3 -> len3 idx4 off4 sum4 {
                value = calldataload off3
                sum4 = add sum3 value
                one = const 1
                idx4 = add idx3 one
                word = const 32
                off4 = add off3 word
                => @loop
            }
            done len5 idx5 off5 sum5 {
                word_out = const 32
                ptr = malloc word_out
                mstore256 ptr sum5
                return ptr word_out
            }
        "#,
        r#"
        @0 []
            ; start:                    []
            const 0x0                 [v4]
            const 0x20            [v3, v4]
            const 0x0         [v2, v3, v4]
            const 0x0     [v0, v2, v3, v4]
            calldataload  [v1, v2, v3, v4]
            => [$1, $2, $3, $4]
            (jmp @1)
        @1 [$5, $6, $7, $8]
            ; start:          [v0, v1, v2, v3]
            dup1          [v0, v0, v1, v2, v3]
            dup3      [v1, v0, v0, v1, v2, v3]
            lt            [v4, v0, v1, v2, v3]
            => [$9 | $5, $6, $7, $8]
            (br @2 @3)
        @2 [$10, $11, $12, $13]
            ; start:               [v0, v1, v2, v3]
            swap3                  [v3, v1, v2, v0]
            dup3               [v2, v3, v1, v2, v0]
            const 0x20     [v8, v2, v3, v1, v2, v0]
            [flipped] add      [v9, v3, v1, v2, v0]
            swap3              [v2, v3, v1, v9, v0]
            calldataload       [v4, v3, v1, v9, v0]
            [flipped] add          [v5, v1, v9, v0]
            swap3                  [v0, v1, v9, v5]
            swap1                  [v1, v0, v9, v5]
            const 0x1          [v6, v1, v0, v9, v5]
            [flipped] add          [v7, v0, v9, v5]
            swap1                  [v0, v7, v9, v5]
            => [$10, $17, $19, $15]
            (jmp @1)
        @3 [$20, $21, $22, $23]
            ; start:                    [v0, v1, v2, v3]
            const 0x20              [v4, v0, v1, v2, v3]
            dup1                [v4, v4, v0, v1, v2, v3]
            malloc              [v5, v4, v0, v1, v2, v3]
            dup6            [v3, v5, v4, v0, v1, v2, v3]
            dup2        [v5, v3, v5, v4, v0, v1, v2, v3]
            mstore              [v5, v4, v0, v1, v2, v3]
            return                      [v0, v1, v2, v3]
            => []
            (return)
        "#,
    );
}

#[test]
fn lowers_branch_layouts() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry -> zero value {
                zero = const 0
                value = const 7
                => @branch
            }
            branch flag carried -> carried {
                => flag ? @left : @right
            }
            left left_value {
                stop
            }
            right right_value {
                invalid
            }
        "#,
        r#"
        @0 []
            ; start:         []
            const 0x0      [v0]
            const 0x7  [v1, v0]
            pop            [v0]
            => [$0]
            (jmp @1)
        @1 [$2]
            ; start:  [v0]
            => [$2 | ]
            (br @2 @3)
        @2 []
            ; start:  []
            stop      []
            => []
            (stop)
        @3 []
            ; start:  []
            invalid   []
            => []
            (invalid)
        "#,
    );
}

#[test]
fn simple_icall() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry {
                value = caller
                other = const 0
                stuff = icall @ident value other
                sstore stuff other
                stop
            }
        fn ident:
            entry x y -> x {
                iret
            }
        "#,
        r#"
        @0 [return_dest, $0]
            ; start:  [v0, v1]
            => [return_dest | $0]
            (iret)
        @1 []
            ; start:                  []
            const 0x0               [v1]
            caller              [v0, v1]
            call_ret_push2  [v2, v0, v1]
            icall #2            [v3, v1]
            sstore                    []
            stop                      []
            => []
            (stop)
        "#,
    );
}

#[test]
fn simple_op_use_spill() {
    assert_lowers_to(
        ShuffleConfig {
            max_swap_depth: 3,
            max_dup_depth: 2,
            max_exchange_range: 3,
            exchange_cost: 9,
        },
        r#"
        fn init:
            entry {
                a = const 1
                b1 = const 0
                b2 = const 0
                b3 = const 0
                b4 = const 0
                x = not a
                stop
            }
        "#,
        r#"
        @0 []
            ; start:                     []
            const 0x0                  [v1]
            const 0x0              [v2, v1]
            const 0x0          [v3, v2, v1]
            const 0x0      [v4, v3, v2, v1]
            const 0x1  [v0, v4, v3, v2, v1]
            not        [v5, v4, v3, v2, v1]
            stop       [v5, v4, v3, v2, v1]
            => []
            (stop)
        "#,
    );
}

#[test]
fn spill_allocations_are_unique_across_internal_calls() {
    assert_lowers_to(
        ShuffleConfig::max_swap_no_exchange(1),
        r#"
        fn init:
            entry {
                arg = const 1
                filler0 = const 2
                caller_live = const 3
                result = icall @callee arg
                combined = add caller_live result
                stop
            }
        fn callee:
            entry input -> output {
                filler0 = const 4
                filler1 = const 5
                output = not input
                iret
            }
        "#,
        r#"
        @0 [return_dest, $0]
            ; start:           [v0, v1]
            swap1              [v1, v0]
            not                [v4, v0]
            const 0x5      [v3, v4, v0]
            const 0x4  [v2, v3, v4, v0]
            pop            [v3, v4, v0]
            pop                [v4, v0]
            swap1              [v0, v4]
            => [return_dest | $3]
            (iret)
        @1 []
            ; start:                  []
            const 0x2               [v1]
            const 0x1           [v0, v1]
            call_ret_push6  [v3, v0, v1]
            icall #6            [v4, v1]
            const 0x3       [v2, v4, v1]
            add                 [v5, v1]
            stop                [v5, v1]
            => []
            (stop)
        "#,
    );
}

#[test]
fn unreachable() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry {
                x = const 3
                stop
            }
            another {
                y = not x
                invalid
            }
        "#,
        r#"
        @0 []
            ; start:     []
            const 0x3  [v0]
            stop       [v0]
            => []
            (stop)
        "#,
    );
}

#[test]
fn repeated_input() {
    assert_lowers_to(
        ShuffleConfig::default(),
        r#"
        fn init:
            entry {
                x = const 3
                y = const 2
                z = addmod x y x
                stop
            }
        "#,
        r#"
        @0 []
            ; start:                    []
            const 0x3                 [v0]
            dup1                  [v0, v0]
            const 0x2         [v1, v0, v0]
            [flipped] addmod          [v2]
            stop                      [v2]
            => []
            (stop)
        "#,
    );
}
