// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {BaseTest} from "./BaseTest.sol";
import {CopyPropBranch} from "src/CopyPropBranch.sol";
import {CopyPropSwitch} from "src/CopyPropSwitch.sol";

contract CopyPropagationTest is BaseTest {
    function test_copyPropagation_noCopies_doesNotBreak() public {
        bytes memory codeWithout = sir(abi.encode("src/simple_add.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/simple_add.sir", "--init-only", "-O", "c"));

        address implWithout = makeAddr("without-opt");
        address implWith = makeAddr("with-opt");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(42), uint256(58));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);

        assertEq(outWithout, outWith, "optimization changed behavior");
    }

    function test_copyPropagation_branch_withChain() public {
        CopyPropBranch solRef = new CopyPropBranch();
        bytes memory sirCode = sir(abi.encode("src/copy_prop_branch.sir", "--init-only", "-O", "c"));
        address sirImpl = makeAddr("sir-branch");
        vm.etch(sirImpl, sirCode);

        bytes memory input1 = abi.encode(uint256(10), uint256(20));
        (, bytes memory refOut1) = address(solRef).call(input1);
        (, bytes memory sirOut1) = sirImpl.call(input1);
        assertEq(refOut1, sirOut1, "branch: nonzero case mismatch");

        bytes memory input2 = abi.encode(uint256(0), uint256(0));
        (, bytes memory refOut2) = address(solRef).call(input2);
        (, bytes memory sirOut2) = sirImpl.call(input2);
        assertEq(refOut2, sirOut2, "branch: zero case mismatch");
    }

    function test_copyPropagation_switch_withOutput() public {
        CopyPropSwitch solRef = new CopyPropSwitch();
        bytes memory sirCode = sir(abi.encode("src/copy_prop_switch.sir", "--init-only", "-O", "c"));
        address sirImpl = makeAddr("sir-switch");
        vm.etch(sirImpl, sirCode);

        uint256 x = 100;
        uint256 y = 200;

        bytes memory input0 = abi.encode(uint256(0), x, y);
        (, bytes memory refOut0) = address(solRef).call(input0);
        (, bytes memory sirOut0) = sirImpl.call(input0);
        assertEq(refOut0, sirOut0, "switch: case 0 mismatch");

        bytes memory input1 = abi.encode(uint256(1), x, y);
        (, bytes memory refOut1) = address(solRef).call(input1);
        (, bytes memory sirOut1) = sirImpl.call(input1);
        assertEq(refOut1, sirOut1, "switch: case 1 mismatch");

        bytes memory input2 = abi.encode(uint256(2), x, y);
        (, bytes memory refOut2) = address(solRef).call(input2);
        (, bytes memory sirOut2) = sirImpl.call(input2);
        assertEq(refOut2, sirOut2, "switch: default case mismatch");
    }
}
