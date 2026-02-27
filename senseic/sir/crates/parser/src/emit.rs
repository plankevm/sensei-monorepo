use crate::parser::{Ast, ControlFlow, Function, ParamExpr, Span, Spanned};
use alloy_primitives::U256;
use bumpalo::{
    Bump,
    collections::{String as BString, Vec as BVec},
};
use sir_data::{
    BasicBlockId, Branch, Control, DataId, EthIRProgram, FunctionId, LocalId, Operation,
    builder::{BuildError, EthIRBuilder},
    operation::{OpBuildError, OpExtraData},
};
use smallvec::SmallVec;
use std::collections::{HashMap, hash_map::Entry};

const DEFAULT_INIT_ENTRYPOINT_NAME: &str = "init";
const DEFAULT_RUNTIME_ENTRYPOINT_NAME: &str = "main";

type BBox<'arena, T> = &'arena mut T;

#[derive(Debug)]
pub struct SirAstSemaError<'arena> {
    pub spans: BBox<'arena, [Span]>,
    pub reason: BString<'arena>,
}

#[derive(Debug, Clone)]
pub struct EmitConfig<'a> {
    init_name: &'a str,
    run_name: Option<&'a str>,
    pub allow_duplicate_locals: bool,
}

impl<'a> EmitConfig<'a> {
    pub fn init_only() -> Self {
        Self {
            init_name: DEFAULT_INIT_ENTRYPOINT_NAME,
            run_name: None,
            allow_duplicate_locals: false,
        }
    }

    pub fn init_only_with_name(init_name: &'a str) -> Self {
        Self { init_name, run_name: None, allow_duplicate_locals: false }
    }

    pub fn new(init_name: &'a str, main_name: &'a str) -> Self {
        Self { init_name, run_name: Some(main_name), allow_duplicate_locals: false }
    }
}

impl<'a> Default for EmitConfig<'a> {
    fn default() -> Self {
        Self {
            init_name: DEFAULT_INIT_ENTRYPOINT_NAME,
            run_name: Some(DEFAULT_RUNTIME_ENTRYPOINT_NAME),
            allow_duplicate_locals: false,
        }
    }
}

macro_rules! format_in {
    ($arena:ident, $($arg:tt)*) => {
        {
            use core::fmt::Write;
            let mut output = BString::new_in($arena);
            write!(&mut output, $($arg)*).expect("Arena string write failed");
            output
        }
    }
}

fn check_dag_and_topo_sort<'ast, 'arena: 'ast, 'src>(
    arena: &'arena Bump,
    current: Spanned<&'src str>,
    reverse_topo_sort: &mut BVec<'arena, &'src str>,
    visited_trace: &mut BVec<'arena, Spanned<&'src str>>,
    functions: &'ast [Function<'arena, 'src>],
) -> Result<(), SirAstSemaError<'arena>> {
    if let Some(visited_index) = visited_trace.iter().position(|name| name.inner == current.inner) {
        use std::fmt::Write;
        let mut reason = BString::with_capacity_in(200, arena);
        write!(&mut reason, "Recursion is not supported. Call trace: ").unwrap();
        for visited in visited_trace[visited_index..].iter() {
            write!(&mut reason, "{} -> ", visited.inner).unwrap();
        }
        write!(&mut reason, "{}", current.inner).unwrap();
        return Err(SirAstSemaError { spans: arena.alloc([current.span()]), reason });
    }

    visited_trace.push(current.clone());

    let func = functions.iter().find(|func| func.name.inner == current.inner).ok_or_else(|| {
        SirAstSemaError {
            spans: arena.alloc([current.span()]),
            reason: format_in!(arena, "Function {:?} not found", current.inner),
        }
    })?;

    let basic_blocks = func.basic_blocks.iter();
    let statements = basic_blocks.flat_map(|bb| bb.stmts.iter());
    let params = statements.flat_map(|stmt| stmt.params.iter());
    let func_refs = params.filter_map(|p| match p {
        ParamExpr::FuncRef(func_ref) => Some(func_ref),
        _ => None,
    });
    for neighbour_ref in func_refs {
        check_dag_and_topo_sort(
            arena,
            neighbour_ref.clone(),
            reverse_topo_sort,
            visited_trace,
            functions,
        )?;
    }

    if !reverse_topo_sort.contains(&current) {
        reverse_topo_sort.push(current.inner);
    }
    visited_trace.pop().unwrap();

    Ok(())
}

/// Emits IR from
pub fn emit_ir<'ast, 'arena: 'ast, 'src: 'arena>(
    arena: &'arena Bump,
    ast: &'ast Ast<'arena, 'src>,
    config: EmitConfig<'_>,
) -> Result<EthIRProgram, SirAstSemaError<'arena>> {
    let mut ir_builder = EthIRBuilder::new();

    let mut data_names: HashMap<&'src str, Spanned<DataId>> =
        HashMap::with_capacity(ast.data_segments.len());
    for data_def in &ast.data_segments {
        let name = data_def.name.inner;
        let id = ir_builder.push_data_bytes(&data_def.data);
        if let Some(other) = data_names.insert(name, Spanned::new(id, data_def.name.span())) {
            BString::new_in(arena);
            return Err(SirAstSemaError {
                spans: arena.alloc([data_def.name.span(), other.span()]),
                reason: format_in!(arena, "Duplicate data definition: {:?}", name),
            });
        }
    }

    let mut funcs_to_spans: HashMap<&'src str, Span> = HashMap::new();
    for func in ast.functions.iter() {
        let name = &func.name;
        if let Some(duplicate) = funcs_to_spans.insert(name, name.span()) {
            return Err(SirAstSemaError {
                spans: arena.alloc([duplicate, name.span()]),
                reason: format_in!(arena, "Duplicate function {:?}", name.inner),
            });
        }
    }

    let mut reverse_topo_sort = BVec::with_capacity_in(ast.functions.len(), arena);
    let mut visited_trace = BVec::with_capacity_in(10, arena);
    for func in ast.functions.iter() {
        check_dag_and_topo_sort(
            arena,
            func.name.clone(),
            &mut reverse_topo_sort,
            &mut visited_trace,
            &ast.functions,
        )?;
    }

    let mut func_ids: HashMap<&'src str, FunctionId> = HashMap::with_capacity(ast.functions.len());
    let mut bb_ids: HashMap<&'src str, Spanned<BasicBlockId>> = HashMap::new();
    let mut local_name_to_id: HashMap<&'src str, Spanned<LocalId>> = HashMap::with_capacity(100);
    let mut locals_buffer: SmallVec<[LocalId; 32]> = SmallVec::new();

    for &func_name in reverse_topo_sort.iter() {
        let func = ast
            .functions
            .iter()
            .find(|func| func.name.inner == func_name)
            .expect("topo sort didn't catch undef func");
        // Assign ID to identifiers in function.
        local_name_to_id.clear();
        for bb in func.basic_blocks.iter() {
            let bb_inputs = bb.inputs.iter();
            let bb_stmt_assigns = bb.stmts.iter().map(|stmt| stmt.assigns.iter());
            for input in bb_inputs.chain(bb_stmt_assigns.flatten()) {
                match local_name_to_id.entry(input.inner) {
                    Entry::Occupied(_) if config.allow_duplicate_locals => {}
                    Entry::Occupied(e) => {
                        return Err(SirAstSemaError {
                            spans: arena.alloc([e.get().span(), input.span()]),
                            reason: format_in!(
                                arena,
                                "Locals are required to be unique within a function, {:?} not unique",
                                input.inner
                            ),
                        });
                    }
                    Entry::Vacant(e) => {
                        let new_local_id = ir_builder.new_local();
                        e.insert(Spanned::new(new_local_id, input.span()));
                    }
                }
            }
        }

        let mut func_builder = ir_builder.begin_function();
        bb_ids.clear();
        bb_ids.reserve(func.basic_blocks.len());

        // Emit basic blocks.
        let mut entry_bb_id = None;
        for (bb_index, bb) in func.basic_blocks.iter().enumerate() {
            let mut bb_builder = func_builder.begin_basic_block();

            locals_buffer.clear();
            for input in bb.inputs.iter() {
                let input = local_name_to_id.get(input.inner).ok_or_else(|| SirAstSemaError {
                    spans: arena.alloc([input.span()]),
                    reason: format_in!(
                        arena,
                        "Undefined input local {:?} in basic block {:?}",
                        input.inner,
                        bb.name.inner
                    ),
                })?;
                locals_buffer.push(input.inner);
            }
            bb_builder.set_inputs(&locals_buffer);

            locals_buffer.clear();
            for output in bb.outputs.iter() {
                let output = local_name_to_id.get(output.inner).ok_or_else(|| SirAstSemaError {
                    spans: arena.alloc([output.span()]),
                    reason: format_in!(
                        arena,
                        "Undefined output local {:?} in basic block {:?}",
                        output.inner,
                        bb.name.inner
                    ),
                })?;
                locals_buffer.push(output.inner);
            }
            bb_builder.set_outputs(&locals_buffer);

            // Operations
            for stmt in bb.stmts.iter() {
                let name = stmt.op.inner;

                let (maybe_mem_size, op_name) =
                    if let Some(mstore_suffix) = name.strip_prefix("mstore") {
                        (Some(mstore_suffix), "mstore")
                    } else if let Some(mload_suffix) = name.strip_prefix("mload") {
                        (Some(mload_suffix), "mload")
                    } else {
                        (None, name)
                    };
                let memory_size_extra = maybe_mem_size
                    .map(|unparsed_mem_size| match unparsed_mem_size.parse::<u32>() {
                        Ok(size_as_bits) if (1..=32).any(|size| size * 8 == size_as_bits) => {
                            Ok(Spanned::new(
                                OpExtraData::Num(U256::from(size_as_bits / 8)),
                                stmt.op.span(),
                            ))
                        }
                        _ => Err(SirAstSemaError {
                            spans: arena.alloc([stmt.op.span()]),
                            reason: format_in!(
                                arena,
                                "Unsuported memory op ({:?}), expected mstore8-256/mload8-256 (multiple of 8)",
                                name
                            ),
                        }),
                    })
                    .transpose()?;

                let kind = op_name.parse().map_err(|_| SirAstSemaError {
                    spans: arena.alloc([stmt.op.span()]),
                    reason: format_in!(arena, "Unknown operation {:?}", stmt.op.inner),
                })?;

                locals_buffer.clear();
                for param in stmt.params.iter() {
                    let ParamExpr::NameRef(name) = param else { continue };
                    let id = local_name_to_id.get(name.inner).ok_or_else(|| SirAstSemaError {
                        spans: arena.alloc([name.span()]),
                        reason: format_in!(arena, "Local {:?} not defined in function", name.inner),
                    })?;
                    locals_buffer.push(id.inner);
                }
                let ins_end_outs_start = locals_buffer.len();
                for output in stmt.assigns.iter() {
                    let id = local_name_to_id.get(output.inner).expect("BB stmt assign unchecked");
                    locals_buffer.push(id.inner);
                }

                let mut extras = memory_size_extra.map(Ok).into_iter().chain(
                    stmt.params.iter().filter_map(|param| match param {
                        ParamExpr::FuncRef(func_ref) => Some(
                            func_ids
                                .get(func_ref.inner)
                                .map(|func_id| {
                                    Spanned::new(OpExtraData::FuncId(*func_id), func_ref.span())
                                })
                                .ok_or_else(|| SirAstSemaError {
                                    spans: arena.alloc([func_ref.span()]),
                                    reason: format_in!(
                                        arena,
                                        "Undefined function {:?}",
                                        func_ref.inner
                                    ),
                                }),
                        ),
                        ParamExpr::DataRef(data_ref) => Some(
                            data_names
                                .get(data_ref.inner)
                                .map(|data_id| {
                                    Spanned::new(
                                        OpExtraData::DataId(data_id.inner),
                                        data_ref.span(),
                                    )
                                })
                                .ok_or_else(|| SirAstSemaError {
                                    spans: arena.alloc([data_ref.span()]),
                                    reason: format_in!(
                                        arena,
                                        "Undefined data {:?}",
                                        data_ref.inner
                                    ),
                                }),
                        ),
                        ParamExpr::Num(num) => {
                            Some(Ok(Spanned::new(OpExtraData::Num(num.inner), num.span())))
                        }
                        ParamExpr::NameRef(_) => None,
                    }),
                );
                let extra = extras.next().transpose()?.map_or(OpExtraData::Empty, |e| e.inner);
                if let Some(another_extra) = extras.next().transpose()? {
                    return Err(SirAstSemaError {
                        spans: arena.alloc([another_extra.span()]),
                        reason: format_in!(arena, "Max one @func/.data/<num> per op accepted"),
                    });
                }

                let operation = Operation::try_build(
                    kind,
                    &locals_buffer[..ins_end_outs_start],
                    &locals_buffer[ins_end_outs_start..],
                    extra,
                    bb_builder.as_mut(),
                )
                .map_err(|err| match err {
                    OpBuildError::NumTooLarge { too_large, valid_lower, valid_upper } => {
                        SirAstSemaError {
                            spans: arena.alloc([stmt.op.span()]),
                            reason: format_in!(
                                arena,
                                "Number {} for op {:?} not in valid range [{}; {}]",
                                too_large,
                                stmt.op.inner,
                                valid_lower,
                                valid_upper
                            ),
                        }
                    }
                    OpBuildError::UnexpectedExtraData { received, expected } => SirAstSemaError {
                        spans: arena.alloc([stmt.op.span()]),
                        reason: format_in!(
                            arena,
                            "Operation {:?} expects extra ={}, got: {:?}",
                            stmt.op.inner,
                            expected,
                            received
                        ),
                    },
                    OpBuildError::WrongInputCount { expected, received } => SirAstSemaError {
                        spans: arena.alloc([stmt.op.span()]),
                        reason: format_in!(
                            arena,
                            "Operation {:?} expects {} inputs, got: {}",
                            stmt.op.inner,
                            expected,
                            received
                        ),
                    },
                    OpBuildError::WrongOutputCount { expected, received } => SirAstSemaError {
                        spans: arena.alloc([stmt.op.span()]),
                        reason: format_in!(
                            arena,
                            "Operation {:?} assigns {} outputs, assigning {}",
                            stmt.op.inner,
                            expected,
                            received
                        ),
                    },
                    OpBuildError::UndefinedFunction(_) => unreachable!("checked further up?"),
                })?;
                bb_builder.add_operation(operation);
            }

            // Placeholder control to get overriden later.
            let bb_id =
                bb_builder.finish(Control::LastOpTerminates).unwrap_or_else(|err| match err {
                    BuildError::ConflictingFunctionOutputs { .. } => {
                        unreachable!("we just set a default last op terminates, shouldn't error")
                    }
                });
            if bb_index == 0 {
                entry_bb_id = Some(bb_id);
            }
            if let Some(existing) =
                bb_ids.insert(bb.name.inner, Spanned::new(bb_id, bb.name.span()))
            {
                return Err(SirAstSemaError {
                    spans: arena.alloc([existing.span(), bb.name.span()]),
                    reason: format_in!(
                        arena,
                        "Basic blocks with duplicate names {:?}",
                        bb.name.inner
                    ),
                });
            }
        }

        let mut other_iret = None;
        for bb in func.basic_blocks.iter() {
            let bb_id = bb_ids.get(bb.name.inner).expect("missing bb");
            let ctrl = match bb.control_flow.as_ref() {
                None => Control::LastOpTerminates,
                Some(ControlFlow::InternalReturn) => Control::InternalReturn,
                Some(ControlFlow::UnconditionalTo(to)) => {
                    let Some(id_to) = bb_ids.get(to.inner) else {
                        return Err(SirAstSemaError {
                            spans: arena.alloc([to.span()]),
                            reason: format_in!(arena, "Undefined dest. basic block {:?}", to.inner),
                        });
                    };
                    Control::ContinuesTo(id_to.inner)
                }
                Some(ControlFlow::Conditional { condition, non_zero_to, zero_to }) => {
                    let Some(id_non_zero_to) = bb_ids.get(non_zero_to.inner) else {
                        return Err(SirAstSemaError {
                            spans: arena.alloc([non_zero_to.span()]),
                            reason: format_in!(
                                arena,
                                "Undefined !=0 dest. basic block {:?}",
                                non_zero_to.inner
                            ),
                        });
                    };
                    let Some(id_zero_to) = bb_ids.get(zero_to.inner) else {
                        return Err(SirAstSemaError {
                            spans: arena.alloc([zero_to.span()]),
                            reason: format_in!(
                                arena,
                                "Undefined =0 dest. basic block {:?}",
                                zero_to.inner
                            ),
                        });
                    };
                    let Some(condition_local) = local_name_to_id.get(condition.inner) else {
                        return Err(SirAstSemaError {
                            spans: arena.alloc([condition.span()]),
                            reason: format_in!(
                                arena,
                                "Condition local {:?} not found in function",
                                condition.inner
                            ),
                        });
                    };
                    Control::Branches(Branch {
                        condition: condition_local.inner,
                        non_zero_target: id_non_zero_to.inner,
                        zero_target: id_zero_to.inner,
                    })
                }
                Some(ControlFlow::Switch(switch)) => {
                    let mut switch_builder = func_builder.begin_switch();
                    for case in switch.cases.iter() {
                        let Some(id_to) = bb_ids.get(case.to.inner) else {
                            return Err(SirAstSemaError {
                                spans: arena.alloc([case.to.span()]),
                                reason: format_in!(
                                    arena,
                                    "Undefined case dest. basic block {:?}",
                                    case.to.inner
                                ),
                            });
                        };
                        switch_builder.push_case(case.match_value, id_to.inner);
                    }
                    let Some(condition) = local_name_to_id.get(switch.value_ref.inner) else {
                        return Err(SirAstSemaError {
                            spans: arena.alloc([switch.value_ref.span()]),
                            reason: format_in!(
                                arena,
                                "Case local {:?} not found in function",
                                switch.value_ref.inner
                            ),
                        });
                    };
                    let fallback = match switch.fallback.as_ref() {
                        None => None,
                        Some(fallback_to) => {
                            let Some(fallback_id) = bb_ids.get(fallback_to.inner) else {
                                return Err(SirAstSemaError {
                                    spans: arena.alloc([fallback_to.span()]),
                                    reason: format_in!(
                                        arena,
                                        "Undefined fallback dest. basic block {:?}",
                                        fallback_to.inner
                                    ),
                                });
                            };
                            Some(fallback_id.inner)
                        }
                    };
                    Control::Switch(switch_builder.finish(condition.inner, fallback))
                }
            };
            let prev_iret = if let Control::InternalReturn = ctrl {
                other_iret.replace(bb_id.span())
            } else {
                None
            };

            func_builder.set_control(bb_id.inner, ctrl).map_err(|err| match err {
                BuildError::ConflictingFunctionOutputs { set_outputs, implied_out } => {
                    SirAstSemaError {
                        spans: arena.alloc([
                            prev_iret.expect("conflicting outputs without another iret?"),
                            bb_id.span(),
                        ]),
                        reason: format_in!(
                            arena,
                            "Separate irets imply different outputs for function {:?} ({} vs. {})",
                            func.name.inner,
                            set_outputs,
                            implied_out
                        ),
                    }
                }
            })?;
        }

        let func_id = func_builder.finish(entry_bb_id.expect("function didn't have at least 1 bb"));
        func_ids.insert(func.name.inner, func_id);
    }

    let Some(&init_entry) = func_ids.get(config.init_name) else {
        return Err(SirAstSemaError {
            spans: &mut [],
            reason: format_in!(arena, "Initcode entry point {:?} not found", config.init_name),
        });
    };
    let init_func = ir_builder.get_func(init_entry).expect("func with ID not in builder");
    let init_func_inputs = init_func.get_inputs(ir_builder.view_bb_backing());
    if init_func.get_outputs() != 0 || init_func_inputs != 0 {
        let ast_func_node = ast
            .functions
            .iter()
            .find(|func| func.name.inner == config.init_name)
            .expect("func not found despite mapped to ID");
        return Err(SirAstSemaError {
            spans: arena.alloc([ast_func_node.name.span()]),
            reason: format_in!(
                arena,
                "Entry points are expected to have 0 inputs & outputs, got: {} inputs, {} outputs",
                init_func.get_outputs(),
                init_func_inputs
            ),
        });
    }

    let main_entry = if let Some(run_name) = config.run_name {
        let Some(&run_entry) = func_ids.get(run_name) else {
            return Err(SirAstSemaError {
                spans: &mut [],
                reason: format_in!(arena, "Runtime entry point {:?} not found", config.init_name),
            });
        };
        let run_func = ir_builder.get_func(run_entry).expect("func with ID not in builder");
        let run_func_inputs = run_func.get_inputs(ir_builder.view_bb_backing());
        if run_func.get_outputs() != 0 || run_func_inputs != 0 {
            let ast_func_node = ast
                .functions
                .iter()
                .find(|func| func.name.inner == config.init_name)
                .expect("func not found despite mapped to ID");
            return Err(SirAstSemaError {
                spans: arena.alloc([ast_func_node.name.span()]),
                reason: format_in!(
                    arena,
                    "Entry points are expected to have 0 inputs & outputs, got: {} inputs, {} outputs",
                    run_func_inputs,
                    run_func.get_outputs(),
                ),
            });
        }
        Some(run_entry)
    } else {
        None
    };

    Ok(ir_builder.build(init_entry, main_entry))
}
