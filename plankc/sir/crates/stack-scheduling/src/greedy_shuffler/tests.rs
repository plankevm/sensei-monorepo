use super::GreedyShuffler;
use crate::{
    op_graph::ValueNodeId,
    stack::{EvmStack, ShuffleConfig, StackOps, TrackedStack},
};
use StackOps::{Dup, Pop, Swap};
use plank_core::Idx;
use proptest::prelude::*;
use sir_data::StaticAllocId;
use std::collections::HashSet;

fn assert_shuffle_exists(
    config: ShuffleConfig,
    start_stack: impl AsRef<[u32]>,
    target_stack: impl AsRef<[u32]>,
) -> Vec<StackOps> {
    assert_shuffle_exists_with_exchange_order(
        config,
        start_stack.as_ref(),
        target_stack.as_ref(),
        false,
    )
}

fn assert_shuffle_exists_with_exchange_order(
    config: ShuffleConfig,
    start_stack: &[u32],
    target_stack: &[u32],
    exchange_top_down: bool,
) -> Vec<StackOps> {
    let mut evm_stack = EvmStack::new();
    for &v in start_stack.iter().rev() {
        evm_stack.push(ValueNodeId::new(v));
    }

    let target = target_stack.iter().map(|v| ValueNodeId::new(*v)).collect::<Vec<_>>();

    let inputs = evm_stack.fifo().iter().copied().collect::<HashSet<_>>();
    let outputs = target.iter().copied().collect::<HashSet<_>>();
    assert!(inputs.is_superset(&outputs), "impossible start/target configuration");

    let mut ops = Vec::new();

    let mut stack =
        TrackedStack::new_from_evm(StaticAllocId::ZERO, |op| ops.push(op), evm_stack, 8);
    GreedyShuffler::run_with_exchange_order(config, &mut stack, &target, exchange_top_down);

    assert_eq!(stack.stack().fifo(), target, "end != target");

    for &op in &ops {
        assert!(op.is_valid(config));
    }

    ops
}

fn assert_shuffle(
    config: ShuffleConfig,
    start_stack: impl AsRef<[u32]>,
    target_stack: impl AsRef<[u32]>,
    expected_ops: impl AsRef<[StackOps]>,
) {
    let ops = assert_shuffle_exists(config, start_stack, target_stack);
    assert_eq!(ops, expected_ops.as_ref());
}

const fn store(id: u32) -> StackOps {
    StackOps::Store(StaticAllocId::new(id))
}

const fn load(id: u32) -> StackOps {
    StackOps::Load(StaticAllocId::new(id))
}

#[test]
fn noop_smoke() {
    assert_shuffle(ShuffleConfig::default(), [1, 2, 3], [1, 2, 3], []);
}

#[test]
fn pops_unneeded() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [4, 2, 3, 1],
        [1, 2, 3],
        [Pop, Swap(1), Swap(2)],
    );
}

#[test]
fn swaps_top_to_correct_position() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [1, 9, 3, 4],
        [3, 1, 4, 3],
        [Swap(1), Pop, Swap(1), Swap(2), Swap(1), store(0), Dup(1), load(0), Swap(1)],
    );
}

#[test]
fn pops_extra_top_value_single() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [1, 1, 2, 3],
        [1, 2, 3, 2],
        [Pop, Swap(1), Swap(2), Swap(1), store(0), Dup(1), load(0)],
    );
}

#[test]
fn swaps_and_pops_extra_value() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [2, 1, 1, 3],
        [2, 1, 3, 2],
        [Swap(2), Pop, Swap(1), Swap(2), Swap(1), store(0), Dup(1), load(0), Swap(1)],
    );
}

#[test]
fn pops_duplicate_top_value() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [1, 1, 2, 4],
        [1, 1, 4, 2],
        [Pop, Swap(1), Swap(2), Swap(1), Dup(0)],
    );
}

#[test]
fn spills_when_no_shrink_step_applies() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [1, 2, 3, 4],
        [1, 2, 4, 3],
        [store(0), Swap(1), Swap(2), Swap(1), load(0)],
    );
}

#[test]
fn repeatedly_pops_extra_top_values() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [1, 1, 1, 2, 3],
        [1, 2, 3, 2, 3],
        [Pop, Pop, store(0), Dup(1), Dup(1), load(0)],
    );
}

#[test]
fn repeatedly_swaps_and_pops_extra_values() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(2),
        [2, 1, 1, 3, 3],
        [2, 1, 3, 2, 2],
        [
            Swap(2),
            Pop,
            Swap(2),
            Pop,
            Swap(2),
            store(0),
            Dup(1),
            Swap(1),
            Dup(1),
            Swap(1),
            load(0),
            Swap(2),
        ],
    );
}

#[test]
fn simple_swap_only() {
    assert_shuffle(
        ShuffleConfig::default(),
        [5, 1, 2, 3, 4],
        [1, 2, 3, 4, 5],
        [Swap(4), Swap(3), Swap(2), Swap(1)],
    );
}

#[test]
fn needs_unspill() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(3),
        [1, 2, 3, 4, 5, 6],
        [1, 6, 3, 4, 5, 6],
        [Swap(1), Pop, store(0), store(1), Dup(2), load(1), Swap(1), load(0)],
    );
}

#[test]
fn current_is_already_correct_prefix() {
    assert_shuffle(ShuffleConfig::max_swap_no_exchange(2), [1, 0], [0], [Pop]);
}

#[test]
fn correct_after_swap_but_trash_top() {
    assert_shuffle(ShuffleConfig::default(), [1, 3, 2], [1, 2], [Swap(1), Pop]);
}

#[test]
fn empty_to_empty() {
    assert_shuffle(ShuffleConfig::default(), [], [], []);
}

#[test]
fn pop_once() {
    assert_shuffle(ShuffleConfig::max_swap_no_exchange(1), [1], [], [Pop]);
}

#[test]
fn pop_thrice() {
    assert_shuffle(ShuffleConfig::max_swap_no_exchange(1), [0, 0, 0], [], [Pop, Pop, Pop]);
}

#[test]
fn pop_lower2() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(1),
        [0, 1, 2],
        [0],
        [Swap(1), Pop, Swap(1), Pop],
    );
}

#[test]
fn unspill_horizon_before_dup_top1() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(1),
        [0, 1],
        [1, 1, 0, 1],
        [store(0), Dup(0), load(0), Swap(1), Dup(0)],
    );
}

#[test]
fn unspill_horizon_before_dup_top2() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(1),
        [0, 1],
        [0, 0, 1, 1, 0],
        [Swap(1), store(0), Dup(0), load(0), Swap(1), load(0), Swap(1), Dup(0)],
    );
}

#[test]
fn intricate_spill_dup_swap() {
    assert_shuffle(
        ShuffleConfig::max_swap_no_exchange(3),
        [10, 17, 2],
        [10, 2, 2, 10, 17, 17],
        [Dup(1), Swap(3), Dup(1), Dup(1), Swap(1)],
    );
}

#[test]
fn monster_shuffle() {
    assert_shuffle_exists(
        ShuffleConfig::max_swap_no_exchange(1),
        (0..1024).into_iter().collect::<Vec<u32>>(),
        [
            691, 537, 875, 169, 242, 330, 147, 481, 301, 749, 629, 791, 623, 112, 517, 7, 1014,
            559, 478, 711, 473, 181, 1006, 588, 257, 191, 338, 539, 689, 529, 198, 681, 992, 799,
            5, 326, 150, 295, 909, 572, 100, 460, 879, 213, 62, 156, 550, 521, 626, 204, 723, 982,
            342, 30, 878, 41, 329, 25, 65, 498, 989, 162, 325, 87, 786, 456, 955, 930, 90, 783,
            424, 499, 631, 638, 594, 862, 273, 603, 234, 495, 419, 785, 228, 582, 682, 734, 891,
            360, 334, 173, 542, 730, 543, 105, 448, 24, 23, 942, 423, 101, 483, 290, 1008, 570,
            767, 772, 21, 55, 107, 552, 519, 348, 102, 836, 125, 434, 443, 462, 353, 172, 311, 461,
            1007, 1009, 77, 964, 188, 763, 450, 391, 745, 132, 737, 501, 718, 547, 444, 196, 64,
            1015, 624, 975, 742, 625, 840, 806, 190, 385, 349, 489, 831, 123, 630, 1016, 76, 425,
            346, 104, 452, 739, 790, 470, 972, 778, 368, 672, 833, 128, 409, 562, 53, 587, 946,
            643, 177, 633, 733, 838, 490, 707, 990, 948, 57, 61, 873, 187, 901, 577, 697, 67, 530,
            593, 981, 98, 943, 696, 887, 658, 787, 351, 195, 280, 224, 913, 218, 82, 308, 207, 632,
            336, 729, 571, 48, 315, 666, 235, 695, 776, 18, 534, 289, 466, 421, 471, 54, 642, 709,
            144, 818, 904, 1010, 238, 971, 432, 1003, 805, 579, 435, 477, 612, 563, 842, 597, 333,
            771, 15, 2, 777, 726, 155, 139, 27, 131, 165, 3, 167, 291, 253, 566, 319, 807, 860,
            781, 986, 79, 809, 482, 240, 205, 398, 164, 367, 727, 160, 811, 380, 659, 898, 906,
            794, 72, 1000, 141, 728, 998, 720, 260, 170, 628, 438, 74, 527, 912, 839, 837, 846,
            383, 934, 497, 178, 441, 933, 266, 598, 667, 741, 259, 226, 408, 606, 370, 70, 813,
            1002, 221, 735, 225, 404, 538, 586, 365, 306, 715, 663, 140, 220, 468, 485, 59, 999,
            686, 343, 951, 673, 429, 40, 465, 717, 978, 455, 760, 712, 746, 782, 863, 313, 868, 28,
            770, 174, 262, 522, 189, 502, 355, 843, 114, 614, 844, 900, 751, 969, 420, 479, 755,
            525, 756, 743, 135, 161, 427, 649, 232, 14, 653, 546, 764, 1021, 405, 803, 373, 719,
            389, 773, 505, 536, 788, 927, 936, 1019, 401, 233, 402, 436, 914, 413, 823, 558, 12,
            919, 406, 184, 400, 337, 384, 362, 938, 440, 254, 724, 710, 510, 549, 166, 245, 431,
            980, 576, 561, 810, 556, 396, 447, 544, 393, 369, 371, 722, 303, 203, 399, 899, 796,
            870, 970, 602, 34, 286, 31, 858, 38, 627, 961, 252, 81, 817, 591, 615, 620, 417, 428,
            364, 983, 897, 366, 835, 136, 871, 168, 551, 85, 889, 26, 117, 148, 159, 96, 47, 183,
            856, 555, 716, 318, 358, 449, 640, 533, 896, 565, 222, 442, 816, 1, 146, 1005, 175,
            229, 73, 557, 740, 857, 217, 43, 120, 580, 814, 596, 694, 647, 798, 883, 486, 296, 322,
            804, 759, 845, 824, 974, 248, 754, 822, 800, 68, 861, 484, 830, 609, 651, 216, 320,
            644, 275, 535, 241, 491, 249, 916, 381, 376, 416, 503, 966, 922, 925, 115, 122, 958,
            850, 293, 476, 138, 512, 957, 744, 802, 119, 307, 950, 652, 323, 890, 581, 237, 693,
            573, 316, 874, 819, 685, 988, 605, 276, 892, 206, 540, 731, 662, 433, 271, 702, 176,
            932, 611, 488, 768, 388, 635, 692, 700, 750, 412, 397, 865, 110, 616, 19, 214, 58, 387,
            674, 246, 361, 403, 89, 111, 171, 321, 854, 775, 779, 4, 29, 215, 454, 75, 1011, 294,
            905, 841, 944, 940, 569, 828, 599, 864, 780, 270, 127, 515, 426, 94, 103, 158, 622,
            1001, 86, 713, 784, 152, 921, 309, 829, 192, 618, 690, 493, 589, 453, 22, 340, 1017,
            282, 33, 600, 91, 179, 752, 895, 613, 650, 808, 882, 947, 574, 269, 267, 706, 208, 474,
            793, 886, 212, 251, 984, 186, 987, 1020, 374, 129, 145, 182, 585, 578, 305, 979, 962,
            675, 645, 422, 109, 797, 250, 475, 410, 327, 285, 244, 472, 567, 965, 747, 648, 963,
            243, 884, 762, 664, 996, 180, 274, 937, 908, 920, 655, 956, 553, 341, 88, 610, 621,
            639, 407, 765, 299, 985, 71, 418, 869, 50, 847, 11, 825, 945, 44, 708, 545, 701, 732,
            137, 359, 97, 227, 508, 35, 575, 84, 494, 363, 414, 92, 893, 657, 1012, 378, 607, 698,
            193, 284, 1018, 758, 995, 852, 1023, 851, 531, 500, 928, 265, 411, 297, 202, 352, 46,
            885, 121, 789, 17, 292, 676, 931, 332, 458, 910, 223, 197, 953, 507, 283, 56, 328, 894,
            973, 832, 255, 903, 812, 457, 339, 354, 345, 821, 918, 130, 20, 469, 939, 738, 124,
            665, 636, 317, 93, 595, 911, 492, 149, 63, 935, 859, 923, 907, 382, 78, 210, 0, 725,
            699, 310, 230, 994, 867, 126, 513, 548, 679, 133, 437, 617, 300, 108, 219, 211, 312,
            16, 656, 256, 231, 347, 200, 201, 209, 523, 774, 671, 560, 954, 687, 646, 95, 445, 116,
            917, 526, 592, 277, 194, 32, 678, 143, 703, 641, 1022, 748, 6, 601, 350, 684, 118, 968,
            69, 820, 524, 153, 261, 584, 736, 446, 66, 199, 392, 304, 590, 795, 661, 654, 877, 514,
            415, 853, 637, 959, 761, 583, 997, 302, 660, 151, 298, 9, 532, 949, 670, 504, 876, 792,
            509, 154, 13, 395, 714, 753, 480, 379, 680, 451, 766, 49, 272, 705, 331, 37, 721, 855,
            872, 976, 496, 924, 541, 247, 278, 264, 848, 1004, 669, 993, 80, 926, 881, 163, 390,
            113, 518, 634, 236, 288, 866, 967, 769, 51, 801, 941, 467, 608, 619, 36, 157, 888, 324,
            1013, 52, 268, 506, 394, 134, 564, 849, 528, 83, 39, 281, 258, 827, 344, 386, 683, 688,
            335, 357, 279, 826, 554, 8, 604, 463, 45, 757, 377, 516, 263, 375, 430, 960, 106, 677,
            815, 880, 10, 952, 185, 915, 287, 60, 929, 511, 372, 834, 459, 668, 142, 356, 902, 991,
            487, 520, 977, 99, 704, 464, 439, 314, 42, 568, 239,
        ],
    );
}

fn shuffle_case() -> impl Strategy<Value = (ShuffleConfig, Vec<u32>, Vec<u32>)> {
    (1u8..=6, prop::collection::vec(0u32..30, 1..=20)).prop_flat_map(|(max_swap, start)| {
        let values = start.clone();
        let target = prop::collection::vec(prop::sample::select(values), 0..=20);

        (Just(ShuffleConfig::max_swap_no_exchange(max_swap)), Just(start), target)
    })
}

proptest! {
    #[test]
    fn successfully_shuffles((config, start, target) in shuffle_case()) {
        assert_shuffle_exists(config, &start, &target);
        assert_shuffle_exists_with_exchange_order(config, &start, &target, true);
    }
}
