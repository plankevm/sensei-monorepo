// SPDX-License-Identifier: MIT
pragma solidity =0.8.30;

contract ConstProp {
    fallback() external payable {
        assembly ("memory-safe") {
            let cond := calldataload(0)
            let offset := 20
            if cond { offset := 10 }
            let result := add(add(1, 1), offset)
            mstore(0, result)
            return(0, 32)
        }
    }
}
