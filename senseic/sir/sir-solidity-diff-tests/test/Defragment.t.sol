// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {BaseTest} from "./BaseTest.sol";

contract DefragmentTest is BaseTest {
    function test_defragment_simpleAdd() public {
        bytes memory codeWithout = sir(abi.encode("src/simple_add.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/simple_add.sir", "--init-only", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(42), uint256(58));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "simple_add: defragmentation changed behavior");
    }

    function test_defragment_arithmeticLogic() public {
        bytes memory initWithout = sir(abi.encode("src/arithmetic_logic.sir"));
        bytes memory initWith = sir(abi.encode("src/arithmetic_logic.sir", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        (bool s1,) = deployCodeTo(implWithout, initWithout);
        (bool s2,) = deployCodeTo(implWith, initWith);
        assertTrue(s1 && s2, "init failed");

        bytes memory input = abi.encodeWithSelector(bytes4(0xd1cbf1c5), uint256(3), uint256(5));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "arithmetic_logic: defragmentation changed behavior");
    }

    function test_defragment_followTheList() public {
        bytes memory codeWithout = sir(abi.encode("src/follow_the_list.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/follow_the_list.sir", "--init-only", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        uint256[] memory nums = new uint256[](2);
        nums[0] = 1;
        nums[1] = 2;
        bytes memory input = abi.encode(nums);
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "follow_the_list: defragmentation changed behavior");
    }

    function test_defragment_switchBug() public {
        bytes memory codeWithout = sir(abi.encode("src/switch_bug.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/switch_bug.sir", "--init-only", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(100), uint256(50));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "switch_bug: defragmentation changed behavior");
    }

    function test_defragment_simpleDataRet() public {
        bytes memory initWithout = sir(abi.encode("src/simple_data_ret.sir"));
        bytes memory initWith = sir(abi.encode("src/simple_data_ret.sir", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        deployCodeTo(implWithout, initWithout);
        deployCodeTo(implWith, initWith);

        (, bytes memory outWithout) = implWithout.call("");
        (, bytes memory outWith) = implWith.call("");
        assertEq(outWithout, outWith, "simple_data_ret: defragmentation changed behavior");
    }

    function test_defragment_copyPropBranch() public {
        bytes memory codeWithout = sir(abi.encode("src/copy_prop_branch.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/copy_prop_branch.sir", "--init-only", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(10), uint256(20));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "copy_prop_branch: defragmentation changed behavior");
    }

    function test_defragment_copyPropSwitch() public {
        bytes memory codeWithout = sir(abi.encode("src/copy_prop_switch.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/copy_prop_switch.sir", "--init-only", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(0), uint256(100), uint256(200));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "copy_prop_switch: defragmentation changed behavior");
    }

    function test_defragment_constProp() public {
        bytes memory codeWithout = sir(abi.encode("src/const_prop.sir", "--init-only"));
        bytes memory codeWith = sir(abi.encode("src/const_prop.sir", "--init-only", "--defragment"));

        address implWithout = makeAddr("without-defrag");
        address implWith = makeAddr("with-defrag");
        vm.etch(implWithout, codeWithout);
        vm.etch(implWith, codeWith);

        bytes memory input = abi.encode(uint256(1));
        (, bytes memory outWithout) = implWithout.call(input);
        (, bytes memory outWith) = implWith.call(input);
        assertEq(outWithout, outWith, "const_prop: defragmentation changed behavior");
    }

    function test_defragment_deadCodeElimination() public {
        bytes memory codeBefore = sir(abi.encode("src/defragment_dead_code.sir", "--init-only"));
        bytes memory codeAfter = sir(abi.encode("src/defragment_dead_code.sir", "--init-only", "--defragment"));

        assertEq(
            codeBefore.length - codeAfter.length, 64, "defragmentation should remove exactly 64 bytes of dead data"
        );

        address implBefore = makeAddr("before-defrag");
        address implAfter = makeAddr("after-defrag");
        vm.etch(implBefore, codeBefore);
        vm.etch(implAfter, codeAfter);

        bytes memory input = abi.encode(uint256(42), uint256(58));
        (, bytes memory outBefore) = implBefore.call(input);
        (, bytes memory outAfter) = implAfter.call(input);
        assertEq(outBefore, outAfter, "defragmented and non-defragmented should produce identical output");
        assertEq(outAfter, abi.encode(uint256(100)), "should return correct sum");
    }
}
