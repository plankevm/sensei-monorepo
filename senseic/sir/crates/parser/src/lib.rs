mod emit;
mod lexer;
mod parser;
use sir_data::EthIRProgram;
use smallvec::SmallVec;

pub use emit::*;
pub use parser::*;

pub fn highlight_span(out: &mut impl std::fmt::Write, source: &str, span: Span, line_range: usize) {
    let mut lines: SmallVec<[usize; 1024]> = SmallVec::new();
    lines.extend(source.char_indices().filter_map(|(i, c)| (c == '\n').then_some(i)));
    lines.push(source.len());

    let line = lines.partition_point(|&idx| idx < span.start);
    let show_start = line.saturating_sub(line_range);
    let show_end = (line + line_range).min(lines.len().saturating_sub(1));

    let dig_width = (show_end + 1).checked_ilog10().unwrap_or(0) + 1;

    for i in show_start..=show_end {
        let line_start = lines.get(i.wrapping_sub(1)).map_or(0, |&idx| idx + 1);
        let line_end = lines[i];

        writeln!(out, "{:>2$} | {}", i + 1, &source[line_start..line_end], dig_width as usize,)
            .expect("write failed");
        if i == line {
            for _ in line_start..span.start + dig_width as usize + 3 {
                write!(out, " ").unwrap();
            }
            for _ in span.start..span.end {
                write!(out, "^").unwrap();
            }
            writeln!(out).unwrap();
        }
    }
}

pub fn parse_or_panic<'a>(source: &str, config: EmitConfig<'a>) -> EthIRProgram {
    use bumpalo::{Bump, collections::String as BString};

    let arena = Bump::with_capacity(8_192);
    let ast = parser::parse(source, &arena).unwrap_or_else(|err| {
        let err = &err[0];
        let mut out = BString::with_capacity_in(200, &arena);
        highlight_span(&mut out, source, err.span().clone(), 2);
        panic!("{}\n{:?}", out, err);
    });

    emit::emit_ir(&arena, &ast, config).unwrap_or_else(|err| {
        let mut out = BString::with_capacity_in(400, &arena);
        for span in err.spans.iter() {
            highlight_span(&mut out, source, span.clone(), 0);
        }
        panic!("{}{}", out, err.reason);
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::emit::EmitConfig;
    use sir_test_utils::assert_trim_strings_eq_with_diff;

    fn parse_and_display<'a>(source: &str, config: EmitConfig<'a>) -> String {
        let ir = parse_or_panic(source, config);

        sir_data::display_program(&ir)
    }

    fn assert_parse_format<'a>(input: &str, expected: &str, config: EmitConfig<'a>) {
        let actual = parse_and_display(input, config);
        assert_trim_strings_eq_with_diff(&actual, expected, "IR snapshot");
    }

    #[test]
    fn test_simple_function1() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn main:
                entry {
                    c0 = const 0
                    c32 = const 32
                    a = calldataload c0
                    b = calldataload c32
                    c = add a b
                    return c0 c32
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 {
        $0 = const 0x0
        $1 = const 0x20
        $2 = calldataload $0
        $3 = calldataload $1
        $4 = add $2 $3
        return $0 $1
    }
"#;

        assert_parse_format(input, expected, EmitConfig::default());
    }

    #[test]
    fn test_all_operation_kinds_snapshot() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn arithmetic_ops:
                entry lhs rhs extra {
                    add_res = add lhs rhs
                    mul_res = mul lhs rhs
                    sub_res = sub lhs rhs
                    div_res = div lhs rhs
                    sdiv_res = sdiv lhs rhs
                    mod_res = mod lhs rhs
                    smod_res = smod lhs rhs
                    addmod_res = addmod lhs rhs extra
                    mulmod_res = mulmod lhs rhs extra
                    exp_res = exp lhs rhs
                    signext_res = signextend lhs rhs
                    lt_res = lt lhs rhs
                    gt_res = gt lhs rhs
                    slt_res = slt lhs rhs
                    sgt_res = sgt lhs rhs
                    eq_res = eq lhs rhs
                    iszero_res = iszero lhs
                    and_res = and lhs rhs
                    or_res = or lhs rhs
                    xor_res = xor lhs rhs
                    not_res = not lhs
                    byte_res = byte lhs rhs
                    shl_res = shl lhs rhs
                    shr_res = shr lhs rhs
                    sar_res = sar lhs rhs
                    hash_res = keccak256 lhs rhs
                    noop
                    stop
                }
            fn environment_ops:
                entry {
                    zero = const 0
                    one = const 1
                    addr = address
                    bal = balance addr
                    orig = origin
                    caller_val = caller
                    call_val = callvalue
                    calldata_word = calldataload zero
                    calldata_size = calldatasize
                    calldatacopy zero zero calldata_size
                    code_size = codesize
                    codecopy zero zero calldata_size
                    gas_price = gasprice
                    extcode_size = extcodesize addr
                    extcodecopy zero addr zero calldata_size
                    returnd_size = returndatasize
                    returndatacopy zero zero returnd_size
                    extcode_hash = extcodehash addr
                    block_hash_val = blockhash zero
                    coin_val = coinbase
                    time = timestamp
                    block_num = number
                    diff = difficulty
                    gas_lim = gaslimit
                    chain = chainid
                    self_bal = selfbalance
                    base_fee = basefee
                    blob_hash_val = blobhash zero
                    blob_fee = blobbasefee
                    gas_left = gas
                    runtime_start = runtime_start_offset
                    init_end = init_end_offset
                    runtime_len = runtime_length
                    stop
                }
            fn memory_ops:
                entry {
                    word_size = const 32
                    wide_size = const 64
                    heap_ptr = malloc word_size
                    heap_any = mallocany wide_size
                    free_ptr = freeptr
                    static_ptr = salloc 96
                    static_any = sallocany 128
                    store_val = const 1
                    mstore256 heap_ptr store_val
                    load_val = mload32 heap_ptr
                    copy_dst = malloc word_size
                    mcopy copy_dst heap_ptr word_size
                    storage_key = const 5
                    sstore storage_key store_val
                    sload_val = sload storage_key
                    tstore storage_key store_val
                    tload_val = tload storage_key
                    log_topic0 = const 0xaa
                    log_topic1 = const 0xbb
                    log_topic2 = const 0xcc
                    log_topic3 = const 0xdd
                    log0 copy_dst word_size
                    log1 copy_dst word_size log_topic0
                    log2 copy_dst word_size log_topic0 log_topic1
                    log3 copy_dst word_size log_topic0 log_topic1 log_topic2
                    log4 copy_dst word_size log_topic0 log_topic1 log_topic2 log_topic3
                    stop
                }
            fn call_ops:
                entry {
                    gas_amount = const 0x5000
                    addr_const = const 0x1234
                    call_value = const 0x100
                    args_offset = const 0
                    args_size = const 32
                    ret_offset = const 64
                    ret_size = const 32
                    salt = const 0xdeadbeef
                    call_result = call gas_amount addr_const call_value args_offset args_size ret_offset ret_size
                    callcode_result = callcode gas_amount addr_const call_value args_offset args_size ret_offset ret_size
                    delegate_result = delegatecall gas_amount addr_const args_offset args_size ret_offset ret_size
                    static_result = staticcall gas_amount addr_const args_offset args_size ret_offset ret_size
                    create_addr = create call_value args_offset args_size
                    create2_addr = create2 call_value args_offset args_size salt
                    stop
                }
            fn icall_callee:
                entry x y -> sum diff {
                    sum = add x y
                    diff = sub x y
                    iret
                }
            fn icall_ops:
                entry a b {
                    sum_out diff_out = icall @icall_callee a b
                    stop
                }
            fn return_op:
                entry {
                    ret_offset = const 0
                    ret_size = const 32
                    return ret_offset ret_size
                }
            fn revert_op:
                entry {
                    rev_offset = const 0
                    rev_size = const 0
                    revert rev_offset rev_size
                }
            fn invalid_op:
                entry {
                    invalid
                }
            fn selfdestruct_op:
                entry {
                    beneficiary = const 1
                    selfdestruct beneficiary
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)
    fn @2 -> entry @2  (outputs: 0)
    fn @3 -> entry @3  (outputs: 0)
    fn @4 -> entry @4  (outputs: 0)
    fn @5 -> entry @5  (outputs: 2)
    fn @6 -> entry @6  (outputs: 0)
    fn @7 -> entry @7  (outputs: 0)
    fn @8 -> entry @8  (outputs: 0)
    fn @9 -> entry @9  (outputs: 0)
    fn @10 -> entry @10  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 $1 $2 {
        $3 = add $0 $1
        $4 = mul $0 $1
        $5 = sub $0 $1
        $6 = div $0 $1
        $7 = sdiv $0 $1
        $8 = mod $0 $1
        $9 = smod $0 $1
        $10 = addmod $0 $1 $2
        $11 = mulmod $0 $1 $2
        $12 = exp $0 $1
        $13 = signextend $0 $1
        $14 = lt $0 $1
        $15 = gt $0 $1
        $16 = slt $0 $1
        $17 = sgt $0 $1
        $18 = eq $0 $1
        $19 = iszero $0
        $20 = and $0 $1
        $21 = or $0 $1
        $22 = xor $0 $1
        $23 = not $0
        $24 = byte $0 $1
        $25 = shl $0 $1
        $26 = shr $0 $1
        $27 = sar $0 $1
        $28 = keccak256 $0 $1
        noop
        stop
    }

    @2 {
        $29 = const 0x0
        $30 = const 0x1
        $31 = address
        $32 = balance $31
        $33 = origin
        $34 = caller
        $35 = callvalue
        $36 = calldataload $29
        $37 = calldatasize
        calldatacopy $29 $29 $37
        $38 = codesize
        codecopy $29 $29 $37
        $39 = gasprice
        $40 = extcodesize $31
        extcodecopy $29 $31 $29 $37
        $41 = returndatasize
        returndatacopy $29 $29 $41
        $42 = extcodehash $31
        $43 = blockhash $29
        $44 = coinbase
        $45 = timestamp
        $46 = number
        $47 = difficulty
        $48 = gaslimit
        $49 = chainid
        $50 = selfbalance
        $51 = basefee
        $52 = blobhash $29
        $53 = blobbasefee
        $54 = gas
        $55 = runtime_start_offset
        $56 = init_end_offset
        $57 = runtime_length
        stop
    }

    @3 {
        $58 = const 0x20
        $59 = const 0x40
        $60 = malloc $58
        $61 = mallocany $59
        $62 = freeptr
        $63 = salloc 96 #0
        $64 = sallocany 128 #1
        $65 = const 0x1
        mstore256 $60 $65
        $66 = mload32 $60
        $67 = malloc $58
        mcopy $67 $60 $58
        $68 = const 0x5
        sstore $68 $65
        $69 = sload $68
        tstore $68 $65
        $70 = tload $68
        $71 = const 0xaa
        $72 = const 0xbb
        $73 = const 0xcc
        $74 = const 0xdd
        log0 $67 $58
        log1 $67 $58 $71
        log2 $67 $58 $71 $72
        log3 $67 $58 $71 $72 $73
        log4 $67 $58 $71 $72 $73 $74
        stop
    }

    @4 {
        $75 = const 0x5000
        $76 = const 0x1234
        $77 = const 0x100
        $78 = const 0x0
        $79 = const 0x20
        $80 = const 0x40
        $81 = const 0x20
        $82 = const 0xdeadbeef
        $83 = call $75 $76 $77 $78 $79 $80 $81
        $84 = callcode $75 $76 $77 $78 $79 $80 $81
        $85 = delegatecall $75 $76 $78 $79 $80 $81
        $86 = staticcall $75 $76 $78 $79 $80 $81
        $87 = create $77 $78 $79
        $88 = create2 $77 $78 $79 $82
        stop
    }

    @5 $89 $90 -> $91 $92 {
        $91 = add $89 $90
        $92 = sub $89 $90
        iret
    }

    @6 $93 $94 {
        $95 $96 = icall @5 $93 $94
        stop
    }

    @7 {
        $97 = const 0x0
        $98 = const 0x20
        return $97 $98
    }

    @8 {
        $99 = const 0x0
        $100 = const 0x0
        revert $99 $100
    }

    @9 {
        invalid
    }

    @10 {
        $101 = const 0x1
        selfdestruct $101
    }
        "#;

        assert_parse_format(input, expected, EmitConfig::init_only());
    }

    #[test]
    fn test_internal_return_and_block_io() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn main:
                entry lhs rhs -> sum_out diff_out {
                    sum_out = add lhs rhs
                    diff_out = sub lhs rhs
                    => @ret
                }
                ret sum_in diff_in -> total {
                    total = add sum_in diff_in
                    iret
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 1)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 $1 -> $2 $3 {
        $2 = add $0 $1
        $3 = sub $0 $1
        => @2
    }

    @2 $4 $5 -> $6 {
        $6 = add $4 $5
        iret
    }
        "#;

        assert_parse_format(input, expected, EmitConfig::init_only());
    }

    #[test]
    fn test_switch_and_branch_control_flow() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn main:
                entry selector -> branch_value_out {
                    branch_value_out = copy selector
                    => @branch
                }
                branch branch_flag_in {
                    => branch_flag_in ? @switch_block : @zero_case
                }
                switch_block branch_value_in {
                    switch branch_value_in {
                        0 => @zero_case
                        1 => @one_case
                        default => @after_switch
                    }
                }
                zero_case {
                    zero_const = const 0
                    => @after_switch
                }
                one_case {
                    one_const = const 1
                    => @after_switch
                }
                after_switch {
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 -> $1 {
        $1 = copy $0
        => @2
    }

    @2 $2 {
        => $2 ? @3 : @4
    }

    @3 $3 {
        switch $3 {
            0 => @4,
            1 => @5,
            else => @6
        }

    }

    @4 {
        $4 = const 0x0
        => @6
    }

    @5 {
        $5 = const 0x1
        => @6
    }

    @6 {
        stop
    }
        "#;

        assert_parse_format(input, expected, EmitConfig::init_only());
    }

    #[test]
    fn test_data_segments_and_offsets() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn main:
                entry {
                    head_ptr = data_offset .greeting
                    payload_ptr = data_offset .payload
                    zero = const 0
                    len = const 64
                    big_val = large_const 0x1234567890abcdef1234567890abcdef
                    return head_ptr len
                }

            data greeting 0x48656c6c6f2c20576f726c6421
            data payload 0xdeadbeef
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 {
        $0 = data_offset .0
        $1 = data_offset .1
        $2 = const 0x0
        $3 = const 0x40
        $4 = large_const 0x1234567890abcdef1234567890abcdef
        return $0 $3
    }


data .0 0x48656c6c6f2c20576f726c6421
data .1 0xdeadbeef
        "#;

        assert_parse_format(input, expected, EmitConfig::init_only());
    }
}
