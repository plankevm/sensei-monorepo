// SPDX-License-Identifier: MIT
pragma solidity =0.8.30;

contract CopyPropBranch {
    fallback() external payable {
        assembly ("memory-safe") {
            let x := calldataload(0)
            let y := calldataload(32)
            if x {
                mstore(0, x)
                return(0, 32)
            }
            mstore(0, y)
            return(0, 32)
        }
    }
}
