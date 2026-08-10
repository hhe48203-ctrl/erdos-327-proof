#!/usr/bin/env python3
"""Exact arithmetic checks for the explicit Erdős 327 parameters."""

from fractions import Fraction as Q


def main() -> None:
    scale = 10**26
    quarter_exponent = 5000 * scale
    log_exponent = 4 * quarter_exponent
    tiny_root_exponent = 2 * 10**25

    assert log_exponent == 2 * 10**30
    assert log_exponent == 100000 * tiny_root_exponent
    assert 800000360 <= scale // 2
    assert 8192 * 6561 <= 2**26

    odd_budget_slope = Q(33912, 10000)
    log_odd_tail_lower = Q(29494314, 100000000)
    log_qo_upper = Q(29481657, 100000000)
    log_qb_upper = Q(912014, 1000000)
    log_two_lower = Q(6931471803, 10_000_000_000)
    source_slope = Q(1000001, 1000000)
    odd_slope = Q(116312, 100000)
    qb = Q(248933, 100000)
    qo = Q(134288, 100000)
    absorption = Q(1, 10000)

    odd_deletion_gap = odd_budget_slope * log_odd_tail_lower - 1
    mixed_bulk_gap = 1 - odd_budget_slope * log_qo_upper - absorption
    mixed_error_gap = (
        source_slope * log_two_lower
        + (odd_slope - odd_budget_slope) * log_qo_upper
    )
    cross_exponent_upper = (
        source_slope * log_qb_upper
        + odd_slope * log_qo_upper
        + 1 / qb
        + 1 / qo
        + 2 / (qb * qo)
        - 4
    )
    cross_tail_gap = -(cross_exponent_upper + absorption + 1)

    assert odd_deletion_gap >= Q(1, 5000)
    assert mixed_bulk_gap >= Q(1, 10000)
    assert mixed_error_gap >= Q(1, 10000)
    assert cross_tail_gap >= Q(1, 5000)
    assert 128 * 6561 == 839808

    print("EXACT PARAMETER CHECKS: PASS")
    print(f"explicitLogExponent = {log_exponent}")
    print("J = 2^(2*10^30)")
    print("L = 8*2^J+1")
    print("epsilon = 1/(839808*(J+4))")
    print(f"mixed bulk margin lower bound = {mixed_bulk_gap}")
    print(f"mixed cross-tail margin lower bound = {cross_tail_gap}")


if __name__ == "__main__":
    main()
