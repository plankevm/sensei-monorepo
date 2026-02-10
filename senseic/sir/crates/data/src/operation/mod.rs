pub mod op_data;
mod op_fmt;

use crate::{EthIRProgram, builder::EthIRBuilder, index::LocalId};
pub use op_data::*;
use op_fmt::OpFormatter;
use std::fmt;

macro_rules! define_operations {
    (
        $($name:ident($data:ty) $mnemonic:literal),+ $(,)?
    ) => {
        #[derive(Debug, Clone)]
        #[repr(u8)]
        pub enum Operation {
            $($name($data),)+
        }

        impl Operation {
            pub const fn kind(&self) -> OperationKind {
                match self {
                    $(Self::$name(_) => OperationKind::$name,)+
                }
            }

            pub fn visit_data<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
                match self {
                    $(Self::$name(data) => data.get_visited(visitor),)+
                }
            }

            pub fn visit_data_mut<'d, O, V: OpVisitorMut<'d, O>>(&'d mut self, visitor: &mut V) -> O {
                match self {
                    $(Self::$name(data) => data.get_visited_mut(visitor),)+
                }
            }

            pub fn op_fmt(&self, f: &mut impl fmt::Write, ir: &EthIRProgram) -> fmt::Result {
                let mnemonic = self.kind().mnemonic();
                let mut formatter = OpFormatter {
                    ir,
                    write: f,
                    mnemonic,
                };
                self.visit_data(&mut formatter)
            }

            pub fn try_build(kind: OperationKind, ins: &[LocalId], outs: &[LocalId], extra: OpExtraData, builder: &mut EthIRBuilder) -> Result<Self, OpBuildError> {
                let op = match kind {
                    $(OperationKind::$name => Self::$name(<$data>::try_build_op(ins, outs, extra, builder)?),)+
                };
                Ok(op)
            }
        }

        pub const OPERATION_KINDS: usize = [$(const { let _ = $mnemonic; 1 }),+].len();
        pub const OP_MNEMONICS: [&'static str; OPERATION_KINDS] = [
            $($mnemonic,)+
        ];

        #[cfg(test)]
        fn verify_kind_maps_to_mnemonic() {
            $(
                assert_eq!(OperationKind::$name.mnemonic(), $mnemonic);
            )+
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #[repr(u8)]
        pub enum OperationKind {
            $($name,)+
        }

        impl OperationKind {
            pub fn mnemonic(&self) -> &'static str {
                OP_MNEMONICS[*self as usize]
            }
        }

        #[derive(Debug, Clone, thiserror::Error)]
        #[error("Failed to parse into OperationKind")]
        pub struct OperationKindParseErr;

        impl core::str::FromStr for OperationKind {
            type Err = OperationKindParseErr;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                let kind = match s {
                    $($mnemonic => Self::$name,)+
                    _ => { return Err(OperationKindParseErr); }
                };
                Ok(kind)
            }
        }

    };
}

const _OPERATION_SIZE_CHECK: () = const {
    assert!(std::mem::size_of::<Operation>() == 16, "Desired Operation size not achieved");
    assert!(std::mem::align_of::<Operation>() == 4, "Desired Operation alignment not achieved");
};

define_operations! {
    // ========== EVM Arithmetic ==========
    Add(InlineOperands<2, 1>) "add",
    Mul(InlineOperands<2, 1>) "mul",
    Sub(InlineOperands<2, 1>) "sub",
    Div(InlineOperands<2, 1>) "div",
    SDiv(InlineOperands<2, 1>) "sdiv",
    Mod(InlineOperands<2, 1>) "mod",
    SMod(InlineOperands<2, 1>) "smod",
    AddMod(AllocatedIns<3, 1>) "addmod",
    MulMod(AllocatedIns<3, 1>) "mulmod",
    Exp(InlineOperands<2, 1>) "exp",
    SignExtend(InlineOperands<2, 1>) "signextend",

    // ========== EVM Comparison & Bitwise Logic ==========
    Lt(InlineOperands<2, 1>) "lt",
    Gt(InlineOperands<2, 1>) "gt",
    SLt(InlineOperands<2, 1>) "slt",
    SGt(InlineOperands<2, 1>) "sgt",
    Eq(InlineOperands<2, 1>) "eq",
    IsZero(InlineOperands<1, 1>) "iszero",
    And(InlineOperands<2, 1>) "and",
    Or(InlineOperands<2, 1>) "or",
    Xor(InlineOperands<2, 1>) "xor",
    Not(InlineOperands<1, 1>) "not",
    Byte(InlineOperands<2, 1>) "byte",
    Shl(InlineOperands<2, 1>) "shl",
    Shr(InlineOperands<2, 1>) "shr",
    Sar(InlineOperands<2, 1>) "sar",

    // ========== EVM Keccak-256 ==========
    Keccak256(InlineOperands<2, 1>) "keccak256",

    // ========== EVM Environment Information ==========
    Address(InlineOperands<0, 1>) "address",
    Balance(InlineOperands<1, 1>) "balance",
    Origin(InlineOperands<0, 1>) "origin",
    Caller(InlineOperands<0, 1>) "caller",
    CallValue(InlineOperands<0, 1>) "callvalue",
    CallDataLoad(InlineOperands<1, 1>) "calldataload",
    CallDataSize(InlineOperands<0, 1>) "calldatasize",
    CallDataCopy(InlineOperands<3, 0>) "calldatacopy",
    CodeSize(InlineOperands<0, 1>) "codesize",
    CodeCopy(InlineOperands<3, 0>) "codecopy",
    GasPrice(InlineOperands<0, 1>) "gasprice",
    ExtCodeSize(InlineOperands<1, 1>) "extcodesize",
    ExtCodeCopy(AllocatedIns<4, 0>) "extcodecopy",
    ReturnDataSize(InlineOperands<0, 1>) "returndatasize",
    ReturnDataCopy(InlineOperands<3, 0>) "returndatacopy",
    ExtCodeHash(InlineOperands<1, 1>) "extcodehash",
    Gas(InlineOperands<0, 1>) "gas",

    // ========== EVM Block Information ==========
    BlockHash(InlineOperands<1, 1>) "blockhash",
    Coinbase(InlineOperands<0, 1>) "coinbase",
    Timestamp(InlineOperands<0, 1>) "timestamp",
    Number(InlineOperands<0, 1>) "number",
    Difficulty(InlineOperands<0, 1>) "difficulty",
    GasLimit(InlineOperands<0, 1>) "gaslimit",
    ChainId(InlineOperands<0, 1>) "chainid",
    SelfBalance(InlineOperands<0, 1>) "selfbalance",
    BaseFee(InlineOperands<0, 1>) "basefee",
    BlobHash(InlineOperands<1, 1>) "blobhash",
    BlobBaseFee(InlineOperands<0, 1>) "blobbasefee",

    // ========== EVM State Manipulation ==========
    SLoad(InlineOperands<1, 1>) "sload",
    SStore(InlineOperands<2, 0>) "sstore",
    TLoad(InlineOperands<1, 1>) "tload",
    TStore(InlineOperands<2, 0>) "tstore",

    // ========== EVM Logging Operations ==========
    Log0(InlineOperands<2, 0>) "log0",
    Log1(InlineOperands<3, 0>) "log1",
    Log2(AllocatedIns<4, 0>) "log2",
    Log3(AllocatedIns<5, 0>) "log3",
    Log4(AllocatedIns<6, 0>) "log4",

    // ========== EVM System Calls ==========
    Create(AllocatedIns<3, 1>) "create",
    Create2(AllocatedIns<4, 1>) "create2",
    Call(AllocatedIns<7, 1>) "call",
    CallCode(AllocatedIns<7, 1>) "callcode",
    DelegateCall(AllocatedIns<6, 1>) "delegatecall",
    StaticCall(AllocatedIns<6, 1>) "staticcall",
    Return(InlineOperands<2, 0>) "return",
    Stop(()) "stop",
    Revert(InlineOperands<2, 0>) "revert",
    Invalid(()) "invalid",
    SelfDestruct(InlineOperands<1, 0>) "selfdestruct",

    // ========== IR Memory Primitives ==========
    DynamicAllocZeroed(InlineOperands<1, 1>) "malloc",
    DynamicAllocAnyBytes(InlineOperands<1, 1>) "mallocany",
    AcquireFreePointer(InlineOperands<0, 1>) "freeptr",
    StaticAllocZeroed(StaticAllocData) "salloc",
    StaticAllocAnyBytes(StaticAllocData) "sallocany",

    // ========== Memory Manipulation ==========
    MemoryCopy(InlineOperands<3, 0>) "mcopy",
    MemoryLoad(MemoryLoadData) "mload",
    MemoryStore(MemoryStoreData) "mstore",

    // ========== Simple Statements ==========
    SetCopy(InlineOperands<1, 1>) "copy",
    SetSmallConst(SetSmallConstData) "const",
    SetLargeConst(SetLargeConstData) "large_const",
    SetDataOffset(SetDataOffsetData) "data_offset",
    Noop(()) "noop",

    // ========== Internal Call ==========
    InternalCall(InternalCallData) "icall",

    // ========== Bytecode Introspection ==========
    RuntimeStartOffset(InlineOperands<0, 1>) "runtime_start_offset",
    InitEndOffset(InlineOperands<0, 1>) "init_end_offset",
    RuntimeLength(InlineOperands<0, 1>) "runtime_length",
}

use op_data::{AllocatedSpansGetter, InputsGetter, OutputsGetter, ReferencedResourceGetter};

impl Operation {
    pub fn inputs<'a>(&'a self, ir: &'a EthIRProgram) -> &'a [LocalId] {
        self.visit_data(&mut InputsGetter { ir })
    }

    pub fn outputs<'a>(&'a self, ir: &'a EthIRProgram) -> &'a [LocalId] {
        self.visit_data(&mut OutputsGetter { ir })
    }

    pub fn allocated_spans(&self, ir: &EthIRProgram) -> AllocatedSpans {
        self.visit_data(&mut AllocatedSpansGetter { ir })
    }

    pub fn referenced_resources(&self) -> ReferencedResources {
        self.visit_data(&mut ReferencedResourceGetter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kind_maps_to_mnemonic() {
        verify_kind_maps_to_mnemonic();
    }
}
