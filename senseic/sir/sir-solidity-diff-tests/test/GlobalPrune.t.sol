// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {BaseTest} from "./BaseTest.sol";

contract GlobalPruneTest is BaseTest {
    function test_globalPrune_simpleAdd() public {
        bytes memory codeWithout = sir(abi.encode("src/simple_add.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/simple_add.sir", "--init-only", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(42), uint256(58));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "simple_add: pruning changed behavior");
    }

    function test_globalPrune_arithmeticLogic() public {
        bytes memory initWithout = sir(abi.encode("src/arithmetic_logic.sir"));
        bytes memory initWith = sir(abi.encode("src/arithmetic_logic.sir", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        (bool s1,) = deployCodeTo(implWithout, initWithout);
        (bool s2,) = deployCodeTo(implWith, initWith);
        assertTrue(s1 && s2, "init failed");

        bytes memory input = abi.encodeWithSelector(bytes4(0xd1cbf1c5), uint256(3), uint256(5));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "arithmetic_logic: pruning changed behavior");
    }

    function test_globalPrune_followTheList() public {
        bytes memory codeWithout = sir(abi.encode("src/follow_the_list.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/follow_the_list.sir", "--init-only", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        uint256[] memory nums = new uint256[](2);
        nums[0] = 1;
        nums[1] = 2;
        bytes memory input = abi.encode(nums);
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "follow_the_list: pruning changed behavior");
    }

    function test_globalPrune_switchBug() public {
        bytes memory codeWithout = sir(abi.encode("src/switch_bug.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/switch_bug.sir", "--init-only", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(100), uint256(50));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "switch_bug: pruning changed behavior");
    }

    function test_globalPrune_simpleDataRet() public {
        bytes memory initWithout = sir(abi.encode("src/simple_data_ret.sir"));
        bytes memory initWith = sir(abi.encode("src/simple_data_ret.sir", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        deployCodeTo(implWithout, initWithout);
        deployCodeTo(implWith, initWith);

        (, bytes memory outWithout) = implWithout.call("");
        (, bytes memory outWith) = implWith.call("");
        assertEq(outWithout, outWith, "simple_data_ret: pruning changed behavior");
    }

    function test_globalPrune_copyPropBranch() public {
        bytes memory codeWithout = sir(abi.encode("src/copy_prop_branch.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/copy_prop_branch.sir", "--init-only", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(10), uint256(20));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "copy_prop_branch: pruning changed behavior");
    }

    function test_globalPrune_copyPropSwitch() public {
        bytes memory codeWithout = sir(abi.encode("src/copy_prop_switch.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/copy_prop_switch.sir", "--init-only", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(0), uint256(100), uint256(200));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "copy_prop_switch: pruning changed behavior");
    }

    function test_globalPrune_constProp() public {
        bytes memory codeWithout = sir(abi.encode("src/const_prop.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/const_prop.sir", "--init-only", "--global-prune"));

        address implWithout = makeAddr("without-prune");
        address implWith = makeAddr("with-prune");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(1));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "const_prop: pruning changed behavior");
    }

    function test_globalPrune_deadCodeElimination() public {
        bytes memory codeUnpruned = sir(abi.encode("src/global_prune_dead_code.sir", "--init-only"));
        bytes memory codePruned = sir(abi.encode("src/global_prune_dead_code.sir", "--init-only", "--global-prune"));

        assertEq(codeUnpruned.length - codePruned.length, 64, "pruning should remove exactly 64 bytes of dead data");

        address implUnpruned = makeAddr("unpruned-impl");
        address implPruned = makeAddr("pruned-impl");
        vm.etch(implUnpruned, codeUnpruned);
        vm.etch(implPruned, codePruned);

        bytes memory input = abi.encode(uint256(42), uint256(58));
        (, bytes memory outUnpruned) = implUnpruned.call(input);
        (, bytes memory outPruned) = implPruned.call(input);
        assertEq(outUnpruned, outPruned, "pruned and unpruned should produce identical output");
        assertEq(outPruned, abi.encode(uint256(100)), "should return correct sum");
    }
}
