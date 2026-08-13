#!/usr/bin/env python3
"""Exact integer/rational checker for the optimized M2 certificate."""

import argparse
from fractions import Fraction as Q


def check(name: str, condition: bool, detail: str) -> None:
    if not condition:
        raise SystemExit(f"FIRST FAILED INEQUALITY: {name}\n{detail}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-budget", type=int, default=440_000)
    parser.add_argument("--scale", type=int, default=881_019)
    args = parser.parse_args()

    k = args.source_budget
    scale = args.scale
    quarter_exponent = 2500 * (scale + 1)
    log_exponent = 4 * quarter_exponent

    check("positive source budget", k > 0, f"K = {k}")
    check("ten-thousand-block source budget", k % 10_000 == 0,
          f"K = {k} is not divisible by 10,000")
    check("positive scale", scale > 0, f"scale = {scale}")
    check("tiny-root divisibility", log_exponent % 100_000 == 0,
          f"log exponent {log_exponent} is not divisible by 100,000")
    tiny_root_exponent = log_exponent // 100_000

    # Bernoulli gives (1 + 3/10000)^100 >= 103/100.  Raising to the
    # hundredth power gives the exact 10,000-block lower bound 19.
    check("source hundred-block base",
          103**100 >= 19 * 100**100,
          "(103/100)^100 < 19")
    source_blocks = k // 10_000
    check("source centered-tail budget",
          19**source_blocks >= 8 * 3**98 * 22_225_557,
          f"19^{source_blocks} < 8*3^98*22225557")

    # Exact fixed-constant exponents proved in OptimizedLowerBound.lean.
    source_error_exponent = 2 * k + 12
    source_bulk_exponent = 2 * k + 1000
    source_transition_with_front = 2 * k + 1019
    mixed_main_moving_exponent = 2 * k + 360
    mixed_error_exponent = 2 * k + 200
    mixed_transition_main_exponent = 2 * k + 170
    mixed_transition_error_exponent = 2 * k + 20

    check("source scheduled-error reserve",
          source_error_exponent <= scale,
          f"2K+12 = {source_error_exponent} > scale = {scale}")
    check("source bulk reserve",
          source_bulk_exponent + 23 <= log_exponent // 10,
          f"2K+1023 = {source_bulk_exponent + 23} > E/10 = {log_exponent // 10}")
    check("source transition reserve",
          source_transition_with_front <= log_exponent // 10_000,
          f"2K+1019 = {source_transition_with_front} > E/10000 = {log_exponent // 10_000}")

    fixed_capacity = scale - 26
    for name, exponent in (
        ("mixed moving main", mixed_main_moving_exponent),
        ("mixed bulk error", mixed_error_exponent),
        ("mixed transition main", mixed_transition_main_exponent),
        ("mixed transition error", mixed_transition_error_exponent),
    ):
        check(name, exponent <= fixed_capacity,
              f"constant exponent {exponent} > scale-26 = {fixed_capacity}")

    check("sieve square-root start", quarter_exponent >= 768,
          f"quarter exponent = {quarter_exponent}")
    check("tiny logarithm domain", log_exponent >= 150_000,
          f"log exponent = {log_exponent}")
    check("tiny root lower bound", tiny_root_exponent >= 128,
          f"tiny-root exponent = {tiny_root_exponent}")
    check("tiny root dominates log exponent",
          log_exponent.bit_length() - 1 <= tiny_root_exponent,
          f"E = {log_exponent} > 2^{tiny_root_exponent}")

    odd_budget_slope = Q(33912, 10000)
    log_odd_tail_lower = Q(29494314, 100000000)
    log_qo_upper = Q(29481657, 100000000)
    log_qb_upper = Q(912014, 1000000)
    log_two_lower = Q(6931471803, 10_000_000_000)
    source_slope = Q(10003, 10000)
    source_x = Q(3, 10000)
    odd_slope = Q(116312, 100000)
    qb = Q(248933, 100000)
    qo = Q(134288, 100000)
    absorption = Q(1, 10000)

    source_exponent_margin = Q(3, 2) - source_slope * Q(7, 5)
    source_centered_d_lower = (
        (1 + source_x) * (2 * source_x / (source_x + 2)) - source_x
    )
    source_centered_ratio_gap = (
        source_centered_d_lower / (1 + source_centered_d_lower)
    )

    odd_deletion_gap = odd_budget_slope * log_odd_tail_lower - 1
    mixed_bulk_gap = 1 - odd_budget_slope * log_qo_upper - absorption
    mixed_error_gap = (
        source_slope * log_two_lower
        + (odd_slope - odd_budget_slope) * log_qo_upper
    )
    cross_exponent_upper = (
        source_slope * log_qb_upper
        + odd_slope * log_qo_upper
        + 1 / qb + 1 / qo + 2 / (qb * qo) - 4
    )
    cross_tail_gap = -(cross_exponent_upper + absorption + 1)

    check("source exponent", source_exponent_margin > 0,
          f"certified upper-bound margin = {source_exponent_margin}")
    check("source centered d", source_centered_d_lower >= Q(1, 22_225_556),
          f"certified lower bound = {source_centered_d_lower}")
    check("source centered-tail ratio gap",
          source_centered_ratio_gap >= Q(1, 22_225_557),
          f"certified lower bound = {source_centered_ratio_gap}")
    check("odd deletion gap", odd_deletion_gap >= Q(1, 5000),
          f"margin = {odd_deletion_gap}")
    check("mixed bulk gap", mixed_bulk_gap >= Q(1, 10000),
          f"margin = {mixed_bulk_gap}")
    check("mixed error gap", mixed_error_gap >= Q(1, 10000),
          f"margin = {mixed_error_gap}")
    check("mixed cross-tail gap", cross_tail_gap >= Q(1, 30000),
          f"margin = {cross_tail_gap}")
    terminal_absorption = (cross_tail_gap + absorption) / 2
    check("mixed terminal absorption", terminal_absorption >= Q(1, 25000),
          f"margin = {terminal_absorption}")

    coefficient = 128 * 6561
    binary_difficulty = log_exponent + 20
    check("strict baseline improvement", log_exponent < 2 * 10**30,
          f"optimized exponent {log_exponent} is not below 2*10^30")
    check("binary-difficulty lower side", coefficient > 2**19,
          f"{coefficient} <= 2^19")
    check("binary-difficulty upper side",
          log_exponent >= 5
          and 4 * coefficient <= (2**20 - coefficient) * 2**5,
          "839808*(2^E+4) may exceed 2^(E+20)")
    check("M2", binary_difficulty <= 10**10,
          f"B = {binary_difficulty} > 10^10")

    print("OPTIMIZED EXACT PARAMETER CHECKS: PASS")
    print(f"source budget K = {k}")
    print(f"scale = {scale}")
    print(f"explicitLogExponent = {log_exponent}")
    print(f"J = 2^{log_exponent}")
    print("L = 8*2^J+1")
    print(f"epsilon = 1/(839808*(2^{log_exponent}+4))")
    print(f"binary difficulty B = {binary_difficulty}")
    print(f"source exponent margin lower bound = {source_exponent_margin}")
    print(f"source centered d lower bound = {source_centered_d_lower}")
    print(f"source centered ratio-gap lower bound = {source_centered_ratio_gap}")
    print(f"odd deletion margin lower bound = {odd_deletion_gap}")
    print(f"mixed bulk margin lower bound = {mixed_bulk_gap}")
    print(f"mixed error margin lower bound = {mixed_error_gap}")
    print(f"mixed cross-tail margin lower bound = {cross_tail_gap}")
    print(f"mixed terminal absorption = {terminal_absorption}")
    print("best milestone = M2")


if __name__ == "__main__":
    main()
