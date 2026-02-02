// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {BaseTest} from "./BaseTest.sol";
import {ConstProp} from "src/ConstProp.sol";

contract ConstantPropagationTest is BaseTest {
    function test_constantPropagation() public {
        ConstProp solRef = new ConstProp();
        bytes memory sirCode = sir(abi.encode("src/const_prop.sir", "--init-only", "--constant-propagation"));
        address sirImpl = makeAddr("sir-const-prop");
        vm.etch(sirImpl, sirCode);

        bytes memory input0 = abi.encode(uint256(0));
        (, bytes memory refOut0) = address(solRef).call(input0);
        (, bytes memory sirOut0) = sirImpl.call(input0);
        assertEq(refOut0, sirOut0, "const prop: branch_b mismatch");

        bytes memory input1 = abi.encode(uint256(1));
        (, bytes memory refOut1) = address(solRef).call(input1);
        (, bytes memory sirOut1) = sirImpl.call(input1);
        assertEq(refOut1, sirOut1, "const prop: branch_a mismatch");
    }
}
