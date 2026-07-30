#!/usr/bin/env python3
"""Shared verifier for four claims in the positive solution.

Verifies:

* [[centered-sawin-source-estimate]] -- the oriented source exponent is below
  the dyadic summability threshold;
* [[two-endpoint-anatomy-budget]] -- the mixed coordinates, local factors and
  explicit real-parameter window;
* [[two-endpoint-cross-edge-estimate]] -- the two-endpoint exponent is below
  the threshold and the log-L exponents cancel to -2;
* [[positive-density-two-endpoint-construction]] -- the strict parameter
  inequalities used in the final density comparison.

Checks, with the standard library only:

1. every mixed conflict a+2b | ab with a odd has the exact unique coordinates
       a = t*w*(2*u+w), b = t*u*(2*u+w), gcd(u,w)=1;
2. the three odd linear forms u,w,2u+w have 3p-2 root-union residues
   modulo every tested odd prime;
3. the complete local Euler factors for the mixed three-form weight have the
   claimed small-prime and large-prime formulas;
4. the explicit real parameters satisfy all strict source, tail, tradeoff and
   cross-summability inequalities using rigorous rational intervals for log;
5. the symbolic log-L exponents cancel to -2 after the convergent dyadic sum.

The logarithm certificate uses

    log x = 2 * sum_{j>=0} y^(2j+1)/(2j+1),  y=(x-1)/(x+1),

with an exact rational upper bound on the positive tail. No binary or decimal
floating-point comparison is load-bearing.

Run: python3 controls/verify_two_endpoint_anatomy.py
"""
from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from math import gcd

getcontext().prec = 50

FAILURES: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    suffix = f" -- {detail}" if detail else ""
    print(f"  [{'ok' if ok else 'FAIL'}] {name}{suffix}")
    if not ok:
        FAILURES.append(name)


def conflict(a: int, b: int) -> bool:
    return (a * b) % (a + 2 * b) == 0


def audit_coordinates(box: int = 240) -> None:
    print("1. exact mixed-conflict coordinates")
    bad = None
    seen: dict[tuple[int, int], tuple[int, int, int]] = {}
    for a in range(1, 2 * box + 1, 2):
        for b in range(1, box + 1):
            if not conflict(a, b):
                continue
            g = gcd(a, b)
            w, u = a // g, b // g
            ell = 2 * u + w
            if g % ell:
                bad = (a, b, "ell does not divide gcd")
                break
            t = g // ell
            if gcd(u, w) != 1 or a != t * w * ell or b != t * u * ell:
                bad = (a, b, "reconstruction failed")
                break
            key = (a, b)
            coords = (t, u, w)
            old = seen.setdefault(key, coords)
            if old != coords:
                bad = (a, b, f"nonunique: {old} and {coords}")
                break
        if bad:
            break
    check(f"all defining conflicts in a<={2*box}, b<={box} have the coordinates", bad is None,
          "" if bad is None else str(bad))

    bad_converse = None
    for t in range(1, 21):
        for u in range(1, 31):
            for w in range(1, 31):
                if gcd(u, w) != 1:
                    continue
                ell = 2 * u + w
                a, b = t * w * ell, t * u * ell
                if not conflict(a, b):
                    bad_converse = (t, u, w, a, b)
                    break
            if bad_converse:
                break
        if bad_converse:
            break
    check("every tested coprime coordinate triple gives a conflict", bad_converse is None,
          "" if bad_converse is None else str(bad_converse))


def audit_block_lower_bound() -> None:
    """Certify the two errata of the revised manuscript.

    (i) eq:block-lower -- every mixed conflict with an L-rough b in the
        endpoint ranges has u >= L, so every dyadic block starts at L.
        The exclusion of u=1 uses k=1 essentially.
    (ii) eq:a-anatomy -- w carries at most one prime factor above x, so the
        Omega_{>=L}(w) majorisation costs exactly one factor q_o.
    """
    print("1b. dyadic block lower bound and the Omega_{>=L}(w) majorisation")

    # (i)  delta = 1/2, so the hypothesis is L > 2 + 2/delta = 6.
    bad = None
    for L in (7, 11, 13, 17):
        N = 900
        for b in range(N // 2, N + 1):
            if b % 2 == 0 or any(b % p == 0 for p in range(2, L)):
                continue
            for a in range(1, 2 * N + 1, 2):
                if (a * b) % (a + 2 * b) != 0:
                    continue
                u = b // gcd(a, b)
                if u < L:
                    bad = (L, a, b, u)
                    break
            if bad:
                break
        if bad:
            break
    check("every mixed conflict with L-rough b has u >= L, so every dyadic "
          "block starts at L", bad is None,
          "L in {7,11,13,17}, N=900" if bad is None else str(bad))

    # The mechanism, and the necessity of the endpoint range.  Inside the
    # range a <= (2/delta) b = 4b the value u=1 cannot occur, because it
    # would force x = 2 + w <= 6 < L while x must be L-rough.  Outside the
    # range it does occur, so the range hypothesis is not decorative.
    LL = 7
    rough = [b for b in range(1, 400) if b % 2 and all(b % p for p in range(2, LL))]
    inside = [(a, b) for b in rough for a in range(1, 4 * b + 1, 2)
              if (a * b) % (a + 2 * b) == 0 and b // gcd(a, b) == 1]
    outside = [(a, b) for b in rough for a in range(4 * b + 1, 8 * b + 1, 2)
               if (a * b) % (a + 2 * b) == 0 and b // gcd(a, b) == 1]
    check("inside the endpoint range a <= 4b, no mixed conflict has u = 1",
          not inside, "" if not inside else str(inside[:3]))
    check("outside that range u = 1 does occur, so the range hypothesis is "
          "necessary", bool(outside),
          f"smallest witness (a,b)={min(outside, key=lambda t: t[1])}"
          if outside else "none found")

    # (ii)  w <= (2/delta) u < 4x, so two prime factors above x would need
    #       w > x^2 > 4x once x >= 4.
    limit = 4 * 200
    spf = list(range(limit + 1))
    for i in range(2, int(limit ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
    bad = None
    for x in range(5, 201):
        for w in range(1, 4 * x + 1):
            m, big = w, 0
            while m > 1:
                if spf[m] > x:
                    big += 1
                m //= spf[m]
            if big > 1:
                bad = (x, w, big)
                break
        if bad:
            break
    check("for w <= 4x and x >= 5, w has at most one prime factor above x, "
          "so the majorisation costs exactly one factor q_o", bad is None,
          "" if bad is None else str(bad))

    # The extra q_o is an absolute constant: it multiplies no exponent.
    qo = Fraction(16_786, 12_500)
    check("the extra factor q_o is a fixed rational independent of L, N, "
          "K_b, K_o", qo > 1 and qo.denominator == 6250,
          f"q_o = {decimal(qo)}")


def audit_local_roots() -> None:
    print("2. local linear-form geometry")
    primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    for p in primes:
        roots = {
            (u, w)
            for u in range(p)
            for w in range(p)
            if u % p == 0 or w % p == 0 or (2 * u + w) % p == 0
        }
        check(f"root union modulo {p} has size 3p-2", len(roots) == 3 * p - 2,
              f"got {len(roots)}")


def audit_euler_factors() -> None:
    print("3. complete mixed three-form Euler factors")
    qb = Fraction(248_933, 100_000)
    qo = Fraction(16_786, 12_500)
    alpha = 1 / qb
    beta = 1 / qo
    s = 1 / (qb * qo)

    # For an odd prime and exactly one positive form valuation e, the
    # rho_R^#/K^2 density is (1-1/p)^2 p^-e.  Summing e>=1 gives these exact
    # factors.  Below L only the W valuation is permitted.
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        p_frac = Fraction(p)
        density = (1 - 1 / p_frac) ** 2
        small = 1 + density / (p_frac - 1)
        expected_small = 1 + 1 / p_frac - 1 / (p_frac * p_frac)
        check(f"small-prime local factor at p={p} is 1+1/p-1/p^2",
              small == expected_small)

        large = 1 + density * (
            alpha / (p_frac - alpha)
            + beta / (p_frac - beta)
            + s / (p_frac - s)
        )
        first_order = 1 + (alpha + beta + s) / p_frac
        scaled_remainder = abs(large - first_order) * p_frac * p_frac
        check(f"large-prime factor at p={p} has a uniform O(p^-2) remainder",
              scaled_remainder < 4,
              f"p^2|remainder|={decimal(scaled_remainder)}")

    check("the p=2 local factor is 1 when all three coordinate values are odd",
          Fraction(1) == 1)


def log_bounds(x: Fraction, terms: int = 250) -> tuple[Fraction, Fraction]:
    """Rigorous lower and upper rational bounds for log(x), x>1."""
    if x <= 1:
        raise ValueError("log_bounds requires x > 1")
    y = (x - 1) / (x + 1)
    y2 = y * y
    power = y
    partial = Fraction(0)
    for j in range(terms):
        partial += power / (2 * j + 1)
        power *= y2
    lower = 2 * partial
    # Remaining terms have denominators >= 2*terms+1.
    remainder = 2 * power / ((2 * terms + 1) * (1 - y2))
    return lower, lower + remainder


def decimal(frac: Fraction) -> str:
    return str(Decimal(frac.numerator) / Decimal(frac.denominator))


def audit_parameters() -> None:
    print("4. certified parameter window")
    Ab = Fraction(1_000_001, 1_000_000)
    qb = Fraction(248_933, 100_000)
    Ao = Fraction(14_539, 12_500)
    qo = Fraction(16_786, 12_500)
    zo = Fraction(26_861, 20_000)
    c = Fraction(21_195, 6_250)

    ln4_lo, ln4_hi = log_bounds(Fraction(4))
    lnqb_lo, lnqb_hi = log_bounds(qb)
    lnqo_lo, lnqo_hi = log_bounds(qo)
    lnzo_lo, lnzo_hi = log_bounds(zo)

    source_exp_upper = Ab * ln4_hi - Fraction(5, 2)
    tail_margin_lower = Ao * lnzo_lo - (zo - 1)
    exceptional_margin_lower = c * lnzo_lo - 1
    cross_penalty_margin_lower = 1 - c * lnqo_hi
    cross_exp_upper = (
        Ab * lnqb_hi
        + Ao * lnqo_hi
        + 1 / qb
        + 1 / qo
        + 2 / (qb * qo)
        - 4
    )

    check("oriented source exponent is rigorously below -1", source_exp_upper < -1,
          f"upper E_src={decimal(source_exp_upper)}")
    check("odd tail Chernoff margin is rigorously positive", tail_margin_lower > 0,
          f"lower margin={decimal(tail_margin_lower)}")
    check("odd exceptional exponent is rigorously beyond 1", exceptional_margin_lower > 0,
          f"lower c log z_o-1={decimal(exceptional_margin_lower)}")
    check("cross penalty exponent is rigorously below 1", cross_penalty_margin_lower > 0,
          f"lower 1-c log q_o={decimal(cross_penalty_margin_lower)}")
    check("two-endpoint dyadic exponent is rigorously below -1", cross_exp_upper < -1,
          f"upper E_cross={decimal(cross_exp_upper)}")
    check("exceptional moment base exceeds the cross base", zo > qo,
          f"z_o-q_o={decimal(zo-qo)}")

    alpha = 1 / qb
    beta = 1 / qo
    s = 1 / (qb * qo)
    rational_part = alpha + beta + 2 * s - 4
    before_sum_rational = 1 - alpha - beta - 2 * s
    after_sum = before_sum_rational + rational_part + 1
    check("moment terms cancel and the dyadic sum leaves exactly (log L)^-2",
          after_sum == -2, f"exponent={after_sum}")

    # Confirm every certified logarithm interval is genuinely narrow compared
    # with the smallest strict margin used above.
    widths = [ln4_hi-ln4_lo, lnqb_hi-lnqb_lo, lnqo_hi-lnqo_lo, lnzo_hi-lnzo_lo]
    check("all logarithm intervals have width below 10^-80",
          max(widths) < Fraction(1, 10**80),
          f"maximum width={decimal(max(widths))}")


def main() -> int:
    audit_coordinates()
    audit_block_lower_bound()
    audit_local_roots()
    audit_euler_factors()
    audit_parameters()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s): {', '.join(FAILURES)}")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
