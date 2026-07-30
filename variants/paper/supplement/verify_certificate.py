#!/usr/bin/env python3
"""Standalone exact verifier for the k-admissibility variants of Erdos 327.

Verifies, with the Python standard library only and with no load-bearing
floating-point comparison:

1. [[periodic-benchmark]] the explicit universal periodic witness.  For every
   k and every residue class r mod M for which the manuscript asserts a
   conflict, the closed-form pair (a,b) really is a conflicting pair inside
   that class; and for odd k the odd classes modulo an even modulus contain
   no conflict at all.  This pins down the correct benchmark density for each
   k -- 1/2 for odd k, and no periodic set whatsoever for even k.
2. [[conflict-criterion]] a+b | k a b  <=>  x/(x,k) | g, where g=(a,b) and
   x=(a+b)/g.
3. [[two-adic-restriction]] for odd a,b a conflict forces v_2(a+b) <= v_2(k);
   in particular for k=2 the conflict graph on the odd numbers has no edge
   between 1 mod 4 and 3 mod 4.
4. [[source-coordinates]] the generalised Sawin coordinates for the modulus m
   source problem, including u >= L and the exact L-smooth part m.
5. [[mixed-coordinates]] the two-endpoint coordinates for odd k with the
   dilation lambda(k) = least power of two >= max(2,k), including
   kappa = (x,k) = the L-smooth part of x, x/kappa | g, and the exclusion
   u >= L of the small-u families.  A negative control records why the naive
   dilation 2 is fatal for 3 | k and 5 | k.
6. [[local-geometry]] the root unions of both linear-form triples have size
   3p-2 at odd primes, and the p=2 factor of the mixed triple is 1.
7. [[euler-factors]] the complete small-prime and large-prime local factors
   for both triples, including the modified factors at the finitely many
   primes dividing the multiplier, with an explicit uniform ratio bound.
8. [[parameter-window]] the five strict real-parameter inequalities, using
   rigorous rational interval bounds for every logarithm, together with the
   symbolic cancellation of the log L exponents in both dyadic summations.
   The window contains no k: the same numbers work for every odd k.
9. [[large-prime-fibration]] the corrected form of the largest-prime-factor
   observation, and its contraction constant log 2 < 1.
10. [[assembly]] that the assembled two-layer set of Theorem 6.2 really is
   k-admissible, in a finite box.  This checks the combinatorics of the
   assembly only; the density gain is asymptotic and cannot be exhibited in
   a box, since it needs L and N chosen in the legal order.

These checks certify the arithmetic, the local densities and the numerical
window.  They are not evidence for the two analytic mean-value inputs, which
enter only through the cited theorems.

Run: python3 paper/supplement/verify_certificate.py
"""
from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from math import gcd

getcontext().prec = 60

FAILURES: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    suffix = f" -- {detail}" if detail else ""
    print(f"  [{'ok' if ok else 'FAIL'}] {name}{suffix}")
    if not ok:
        FAILURES.append(name)


def decimal(frac: Fraction) -> str:
    return str(Decimal(frac.numerator) / Decimal(frac.denominator))


# --------------------------------------------------------------------------
# elementary helpers
# --------------------------------------------------------------------------

def conflict(a: int, b: int, k: int) -> bool:
    """a + b divides k*a*b."""
    return (k * a * b) % (a + b) == 0


def v2(n: int) -> int:
    e = 0
    while n % 2 == 0:
        n //= 2
        e += 1
    return e


def big_omega(n: int) -> int:
    c, d = 0, 2
    while d * d <= n:
        while n % d == 0:
            n //= d
            c += 1
        d += 1
    if n > 1:
        c += 1
    return c


def smooth_part(n: int, L: int) -> int:
    """Product of the prime powers p^v || n with p < L."""
    s, d, m = 1, 2, n
    while d * d <= m:
        if m % d == 0:
            v = 0
            while m % d == 0:
                m //= d
                v += 1
            if d < L:
                s *= d ** v
        d += 1
    if 1 < m < L:
        s *= m
    return s


def is_rough(n: int, L: int) -> bool:
    return smooth_part(n, L) == 1


def primes_upto(n: int) -> list[int]:
    sieve = [True] * (n + 1)
    sieve[0:2] = [False, False]
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            for j in range(i * i, n + 1, i):
                sieve[j] = False
    return [i for i, t in enumerate(sieve) if t]


# --------------------------------------------------------------------------
# 1.  the periodic benchmark
# --------------------------------------------------------------------------

def periodic_witness(k: int, M: int, r: int):
    """Closed-form conflicting pair inside the class r mod M, or None.

    Manuscript recipe: u = 1, v = 1 + 2M, x = u + v = 2 + 2M,
    y = x/(x,k); a conflict exists in the class as soon as (y,M) | r,
    and then g is any positive solution of g == r (mod M), g == 0 (mod y).
    """
    v = 1 + 2 * M
    x = 2 + 2 * M
    y = x // gcd(x, k)
    if r % gcd(y, M) != 0:
        return None
    step = y
    g = y
    for _ in range(4 * M + 4):
        if g % M == r % M:
            return g, g * v
        g += step
    return None


def audit_periodic_benchmark() -> None:
    print("1. periodic benchmark (the correct density to beat, for each k)")

    bad_even = None
    bad_odd = None
    bad_pair = None
    covered_even = 0
    covered_odd = 0
    for k in range(1, 21):
        for M in range(1, 41):
            for r in range(M):
                wt = periodic_witness(k, M, r)
                must_exist = (k % 2 == 0) or (M % 2 == 1) or (r % 2 == 0)
                if wt is None:
                    if must_exist:
                        (bad_even if k % 2 == 0 else bad_odd) or None
                        if k % 2 == 0:
                            bad_even = (k, M, r)
                        else:
                            bad_odd = (k, M, r)
                    continue
                a, b = wt
                if a == b or a % M != r % M or b % M != r % M \
                        or not conflict(a, b, k):
                    bad_pair = (k, M, r, a, b)
                if k % 2 == 0:
                    covered_even += 1
                else:
                    covered_odd += 1

    check("every class mod M<=40 has an explicit conflict when k is even",
          bad_even is None, "" if bad_even is None else str(bad_even))
    check("every class mod M<=40 with M odd or r even has an explicit "
          "conflict when k is odd",
          bad_odd is None, "" if bad_odd is None else str(bad_odd))
    check("every produced witness is a genuine conflicting pair in its class",
          bad_pair is None,
          f"{covered_even + covered_odd} witnesses verified"
          if bad_pair is None else str(bad_pair))

    # The complementary half: for odd k the surviving classes are exactly the
    # odd classes modulo an even modulus, and those are genuinely admissible.
    bad = None
    for k in (1, 3, 5, 7, 9, 15, 21, 25):
        for M in (2, 4, 6, 8, 10, 12, 14, 16):
            for r in range(1, M, 2):
                vals = list(range(r, 4000, M))
                for i in range(len(vals)):
                    for j in range(i + 1, len(vals)):
                        if conflict(vals[i], vals[j], k):
                            bad = (k, M, r, vals[i], vals[j])
                            break
                    if bad:
                        break
                if bad:
                    break
            if bad:
                break
        if bad:
            break
    check("for odd k the odd classes modulo an even modulus have no conflict "
          "below 4000", bad is None, "" if bad is None else str(bad))

    # The odd numbers themselves: admissible exactly for odd k.
    wrong = []
    for k in range(1, 25):
        witness = None
        for a in range(1, 2400, 2):
            if witness:
                break
            for b in range(a + 2, 2400, 2):
                if conflict(a, b, k):
                    witness = (a, b)
                    break
        admissible = witness is None
        if admissible != (k % 2 == 1):
            wrong.append((k, witness))
    check("the odd numbers are k-admissible precisely for odd k (k<=24)",
          not wrong, "" if not wrong else str(wrong))

    # Consequence: the largest density of a union of classes mod M that the
    # witness construction fails to kill.  This is the benchmark density.
    worst_odd = []
    worst_even = []
    for k in (1, 2, 3, 4, 5, 6, 7, 9, 15):
        best = Fraction(0)
        for M in range(1, 41):
            survivors = sum(1 for r in range(M)
                            if periodic_witness(k, M, r) is None)
            best = max(best, Fraction(survivors, M))
        (worst_odd if k % 2 else worst_even).append((k, best))
    check("for odd k the best surviving periodic density is exactly 1/2",
          all(d == Fraction(1, 2) for _, d in worst_odd), str(worst_odd))
    check("for even k no residue class survives at all: benchmark density 0",
          all(d == 0 for _, d in worst_even), str(worst_even))


# --------------------------------------------------------------------------
# 2.  the conflict criterion
# --------------------------------------------------------------------------

def audit_conflict_criterion() -> None:
    print("2. conflict criterion  a+b | kab  <=>  x/(x,k) | g")
    bad = None
    tested = 0
    for k in range(1, 13):
        for a in range(1, 220):
            for b in range(a + 1, 220):
                g = gcd(a, b)
                x = (a + b) // g
                lhs = conflict(a, b, k)
                rhs = g % (x // gcd(x, k)) == 0
                tested += 1
                if lhs != rhs:
                    bad = (k, a, b)
    check("criterion holds for all 1<=k<=12 and all a<b<220", bad is None,
          f"{tested} pairs" if bad is None else str(bad))


# --------------------------------------------------------------------------
# 3.  the 2-adic restriction
# --------------------------------------------------------------------------

def audit_two_adic() -> None:
    print("3. two-adic restriction on odd conflicts")
    bad = None
    for k in range(1, 25):
        e = v2(k)
        for a in range(1, 500, 2):
            for b in range(a + 2, 500, 2):
                if conflict(a, b, k) and v2(a + b) > e:
                    bad = (k, a, b)
    check("odd a,b with a+b | kab always have v_2(a+b) <= v_2(k)",
          bad is None, "" if bad is None else str(bad))

    bad = None
    for a in range(1, 2600, 2):
        for b in range(a + 2, 2600, 2):
            if a % 4 != b % 4 and conflict(a, b, 2):
                bad = (a, b)
    check("k=2: no conflict between 1 mod 4 and 3 mod 4 below 2600",
          bad is None, "" if bad is None else str(bad))

    # ... while conflicts do occur inside each of the two classes.
    inside = []
    for cls in (1, 3):
        found = None
        for a in range(cls, 2600, 4):
            if found:
                break
            for b in range(a + 4, 2600, 4):
                if conflict(a, b, 2):
                    found = (a, b)
                    break
        inside.append(found)
    check("k=2: both classes 1 mod 4 and 3 mod 4 do contain conflicts",
          all(x is not None for x in inside), str(inside))


# --------------------------------------------------------------------------
# 4.  source coordinates for a general modulus
# --------------------------------------------------------------------------

def audit_source_coordinates() -> None:
    print("4. generalised source coordinates for the modulus m problem")
    bad = None
    seen = 0
    for m in range(1, 13):
        L = m + 1
        for b in range(1, 360):
            if not is_rough(b, L):
                continue
            for c in range(1, 360):
                if c == b or not conflict(b, c, m):
                    continue
                if big_omega(c) > big_omega(b):
                    continue
                g = gcd(b, c)
                u, v = b // g, c // g
                x = u + v
                seen += 1
                if gcd(u, v) != 1:
                    bad = ("u,v not coprime", m, b, c)
                elif (m * b) % (u * x) != 0:
                    bad = ("u(u+v) does not divide m*b", m, b, c)
                elif not is_rough(u, L):
                    bad = ("u is not L-rough", m, b, c)
                elif u == 1:
                    bad = ("u=1 was not excluded by the orientation", m, b, c)
                elif u < L:
                    bad = ("u < L", m, b, c)
                elif x <= L:
                    bad = ("x <= L", m, b, c)
                else:
                    d = (m * b) // (u * x)
                    if smooth_part(u * x * d, L) != m:
                        bad = ("L-smooth part of u*x*d is not m", m, b, c,
                               smooth_part(u * x * d, L))
                if bad:
                    break
            if bad:
                break
        if bad:
            break
    check("oriented source conflicts have the stated coordinates, u>=L, x>L, "
          "and L-smooth part exactly m", bad is None,
          f"{seen} oriented conflicts" if bad is None else str(bad))


# --------------------------------------------------------------------------
# 5.  mixed coordinates for odd k
# --------------------------------------------------------------------------

def dilation(k: int) -> int:
    """lambda(k): the least power of two that is at least max(2, k)."""
    lam = 2
    while lam < k:
        lam *= 2
    return lam


def audit_mixed_coordinates() -> None:
    print("5. two-endpoint mixed coordinates for odd k")

    # --- 5a.  NEGATIVE CONTROL.  The bug that the dilation 2 hides. ---
    # With lambda = 2 the families u = 1 survive whenever 3 | k or 5 | k,
    # and they are fatal: they force the deletion of a positive proportion
    # of the odd host.  This check exists so that a regression to lambda = 2
    # cannot pass silently.
    diag3 = all(conflict(n, 2 * n, k) for k in (3, 9, 15, 21)
                for n in range(1, 300, 2))
    diag5 = all(conflict(3 * n, 2 * n, k) for k in (5, 15, 25)
                for n in range(1, 300, 2) if gcd(n, 15) == 1)
    check("NEGATIVE CONTROL: for 3|k the pair {n,2n} always conflicts, so the "
          "dilation 2 is fatal", diag3, "checked odd n < 300")
    check("NEGATIVE CONTROL: for 5|k the pair {2n,3n} always conflicts",
          diag5, "checked odd n < 300 coprime to 15")

    # --- 5b.  The repair: with lambda >= k the u = 1 families vanish. ---
    bad = None
    for k in range(1, 22, 2):
        lam = dilation(k)
        L = 2 * lam + lam * 2 + 1        # any L > lambda(1 + 1/delta), delta=1/2
        L = max(L, 31)
        N = 420
        for b in range(N // 2, N + 1):
            if b % 2 == 0 or not is_rough(b, L):
                continue
            for a in range(1, lam * N + 1, 2):
                if (k * lam * a * b) % (a + lam * b) != 0:
                    continue
                u = b // gcd(a, b)
                if u < L:
                    bad = (k, lam, L, a, b, f"u={u} < L={L}")
                    break
            if bad:
                break
        if bad:
            break
    check("REPAIR: with lambda = least power of two >= k, every mixed "
          "conflict has u >= L, so every dyadic block has X >= L",
          bad is None, "odd k <= 21" if bad is None else str(bad))

    # --- 5c.  The coordinates themselves, for the repaired dilation. ---
    bad = None
    seen = 0
    for k in (1, 3, 5, 7, 9, 15, 21, 25):
        lam = dilation(k)
        L = k + 1
        for b in range(1, 260):
            if b % 2 == 0 or not is_rough(b, L):
                continue
            for a in range(1, 520, 2):
                if (k * lam * a * b) % (a + lam * b) != 0:
                    continue
                seen += 1
                g = gcd(a, b)
                w, u = a // g, b // g
                x = lam * u + w
                kappa = gcd(x, k)
                xp = x // kappa
                if gcd(u, w) != 1:
                    bad = ("u,w not coprime", k, a, b)
                elif g % xp != 0:
                    bad = ("x/(x,k) does not divide g", k, a, b, x, kappa, g)
                elif a != (g // xp) * xp * w or b != (g // xp) * xp * u:
                    bad = ("reconstruction failed", k, a, b)
                elif smooth_part(x, L) != kappa:
                    bad = ("kappa is not the L-smooth part of x", k, a, b, x,
                           kappa, smooth_part(x, L))
                elif k % kappa != 0:
                    bad = ("kappa does not divide k", k, a, b)
                elif not (is_rough(xp, L) and is_rough(u, L)
                          and is_rough(g // xp, L)):
                    bad = ("t, u or x' is not L-rough", k, a, b)
                elif x % 2 == 0 or w % 2 == 0 or u % 2 == 0:
                    bad = ("t,u,w,x are not all odd", k, a, b)
                if bad:
                    break
            if bad:
                break
        if bad:
            break
    check("every mixed conflict with L-rough odd b has the stated "
          "coordinates", bad is None,
          f"{seen} conflicts" if bad is None else str(bad))

    bad = None
    for k in (1, 3, 5, 7, 9):
        lam = dilation(k)
        for t in range(1, 11):
            for u in range(1, 25, 2):
                for w in range(1, 25, 2):
                    if gcd(u, w) != 1:
                        continue
                    x = lam * u + w
                    xp = x // gcd(x, k)
                    a, b = t * xp * w, t * xp * u
                    if (k * lam * a * b) % (a + lam * b) != 0:
                        bad = (k, t, u, w, a, b)
    check("every coordinate tuple gives back a mixed conflict", bad is None,
          "" if bad is None else str(bad))

    # The one place where the source presentation is loose: w can carry at
    # most one prime factor above x, so Omega_{>=L}(w) - Omega_L(w,x) <= 1.
    # In the repaired construction the range is w <= c*x with
    # c = lambda/delta = 2*lambda, so we test the largest c we ever use.
    C = 64                                  # 2*lambda for lambda = 32, k <= 32
    XHI = 130
    limit = C * XHI
    spf = list(range(limit + 1))
    for i in range(2, int(limit ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
    factors = [[] for _ in range(limit + 1)]
    for n in range(2, limit + 1):
        m = n
        while m > 1:
            factors[n].append(spf[m])
            m //= spf[m]
    bad = None
    for x in range(C, XHI + 1):
        for w in range(1, C * x + 1):
            if sum(1 for p in factors[w] if p > x) > 1:
                bad = (x, w)
                break
        if bad:
            break
    check(f"for w <= {C}x and x >= {C}, w has at most one prime factor above "
          "x (so the Omega_{>=L}(w) majorisation costs one factor q_o)",
          bad is None, "" if bad is None else str(bad))


# --------------------------------------------------------------------------
# 6.  local linear-form geometry
# --------------------------------------------------------------------------

def audit_local_roots() -> None:
    print("6. local linear-form geometry")
    primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    ok_mixed = ok_source = True
    for p in primes:
        mixed = {(u, w) for u in range(p) for w in range(p)
                 if u % p == 0 or w % p == 0 or (2 * u + w) % p == 0}
        source = {(u, v) for u in range(p) for v in range(p)
                  if u % p == 0 or v % p == 0 or (u + v) % p == 0}
        ok_mixed &= len(mixed) == 3 * p - 2
        ok_source &= len(source) == 3 * p - 2
    check("mixed triple (U, W, 2U+W) has 3p-2 root residues at every tested "
          "odd prime", ok_mixed, f"primes {primes[0]}..{primes[-1]}")
    check("source triple (U, V, U+V) has 3p-2 root residues at every tested "
          "odd prime", ok_source, f"primes {primes[0]}..{primes[-1]}")

    # p = 2.  Mixed: u, w, 2u+w all odd, so the local factor is 1.
    two_mixed = {(u, w) for u in range(2) for w in range(2)
                 if u % 2 and w % 2 and (2 * u + w) % 2}
    check("at p=2 the mixed triple forces all three values odd",
          two_mixed == {(1, 1)}, str(sorted(two_mixed)))

    # The source triple, unlike the mixed one, also has 3p-2 roots at p=2,
    # which is why the manuscript may say "at every prime" there.
    two_source = {(u, v) for u in range(2) for v in range(2)
                  if u % 2 == 0 or v % 2 == 0 or (u + v) % 2 == 0}
    two_mixed_roots = {(u, w) for u in range(2) for w in range(2)
                       if u % 2 == 0 or w % 2 == 0 or (2 * u + w) % 2 == 0}
    check("source triple has 3p-2 = 4 root residues at p=2 as well",
          len(two_source) == 4, f"got {len(two_source)}")
    check("mixed triple has only 3 root residues at p=2, so 3p-2 is claimed "
          "for odd p only there", len(two_mixed_roots) == 3,
          f"got {len(two_mixed_roots)}")


# --------------------------------------------------------------------------
# 7.  Euler factors
# --------------------------------------------------------------------------

QB = Fraction(248_933, 100_000)
QO = Fraction(16_786, 12_500)


def audit_euler_factors() -> None:
    print("7. complete local Euler factors for both triples")
    alpha = 1 / QB
    beta = 1 / QO
    s = 1 / (QB * QO)
    primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)

    ok_small = ok_large = True
    worst_large = Fraction(0)
    for p in primes:
        pf = Fraction(p)
        dens = (1 - 1 / pf) ** 2
        # Mixed, 2 < p < L, p does not divide k: only the W-axis, and below L
        # the W-weight is 1 because g_{2,L} uses Omega_{>=L}.
        small = 1 + dens / (pf - 1)
        ok_small &= small == 1 + 1 / pf - 1 / (pf * pf)
        # Mixed, p >= L: all three axes with their own weights.
        large = 1 + dens * (alpha / (pf - alpha) + beta / (pf - beta)
                            + s / (pf - s))
        rem = abs(large - (1 + (alpha + beta + s) / pf)) * pf * pf
        ok_large &= rem < 4
        worst_large = max(worst_large, rem)
    check("mixed small-prime factor equals 1 + 1/p - 1/p^2", ok_small)
    check("mixed large-prime factor is 1 + (alpha+beta+s)/p + O(p^-2)",
          ok_large, f"max p^2|remainder| = {decimal(worst_large)}")

    # Source triple: weights 1/2, 1/2, 1/4.
    ok_small = ok_large = True
    worst = Fraction(0)
    for p in primes:
        pf = Fraction(p)
        dens = (1 - 1 / pf) ** 2
        half, quarter = Fraction(1, 2), Fraction(1, 4)
        small = 1 + dens * half / (pf - half)
        ok_small &= small == 1 + dens / (2 * pf - 1)
        large = 1 + dens * (2 * half / (pf - half) + quarter / (pf - quarter))
        rem = abs(large - (1 + Fraction(5, 4) / pf)) * pf * pf
        ok_large &= rem < 4
        worst = max(worst, rem)
    check("source small-prime factor is 1 + 1/(2p) + O(p^-2) (only the V-axis)",
          ok_small)
    check("source large-prime factor is 1 + (5/4)/p + O(p^-2)", ok_large,
          f"max p^2|remainder| = {decimal(worst)}")

    # The finitely many primes dividing the multiplier: the extra axis
    # contributes a bounded factor, uniformly in the cutoff.
    ok = True
    worst_ratio = Fraction(0)
    for p in primes:
        pf = Fraction(p)
        dens = (1 - 1 / pf) ** 2
        base = 1 + dens / (pf - 1)
        for vp in range(1, 7):
            extra = sum(s ** e / pf ** e for e in range(1, vp + 1))
            modified = base + dens * extra
            ratio = modified / base
            worst_ratio = max(worst_ratio, ratio)
            ok &= ratio < Fraction(3, 2)
    check("at primes dividing the multiplier the modified mixed factor "
          "exceeds the generic one by a bounded ratio", ok,
          f"max ratio = {decimal(worst_ratio)} < 3/2")


# --------------------------------------------------------------------------
# 8.  the certified parameter window
# --------------------------------------------------------------------------

def log_bounds(x: Fraction, terms: int = 250) -> tuple[Fraction, Fraction]:
    """Rigorous rational lower and upper bounds for log(x), x > 1."""
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
    remainder = 2 * power / ((2 * terms + 1) * (1 - y2))
    return lower, lower + remainder


def audit_parameters() -> None:
    print("8. certified parameter window (identical for every odd k)")
    Ab = Fraction(1_000_001, 1_000_000)
    Ao = Fraction(14_539, 12_500)
    zo = Fraction(26_861, 20_000)
    c = Fraction(21_195, 6_250)
    qb, qo = QB, QO

    ln4_lo, ln4_hi = log_bounds(Fraction(4))
    lnqb_lo, lnqb_hi = log_bounds(qb)
    lnqo_lo, lnqo_hi = log_bounds(qo)
    lnzo_lo, lnzo_hi = log_bounds(zo)

    source_exp_upper = Ab * ln4_hi - Fraction(5, 2)
    tail_margin_lower = Ao * lnzo_lo - (zo - 1)
    exceptional_lower = c * lnzo_lo - 1
    penalty_lower = 1 - c * lnqo_hi
    cross_exp_upper = (Ab * lnqb_hi + Ao * lnqo_hi
                       + 1 / qb + 1 / qo + 2 / (qb * qo) - 4)

    check("source dyadic exponent M-5/2 is rigorously below -1",
          source_exp_upper < -1, f"upper = {decimal(source_exp_upper)}")
    check("odd-host Chernoff margin A_o log z_o - (z_o - 1) is positive",
          tail_margin_lower > 0, f"lower = {decimal(tail_margin_lower)}")
    check("odd exceptional exponent c log z_o exceeds 1",
          exceptional_lower > 0, f"lower = {decimal(exceptional_lower)}")
    check("cross penalty exponent c log q_o is below 1", penalty_lower > 0,
          f"lower = {decimal(penalty_lower)}")
    check("two-endpoint dyadic exponent E is rigorously below -1",
          cross_exp_upper < -1, f"upper = {decimal(cross_exp_upper)}")
    check("exceptional moment base exceeds the cross base", zo > qo,
          f"z_o - q_o = {decimal(zo - qo)}")

    alpha, beta = 1 / qb, 1 / qo
    s = 1 / (qb * qo)

    # ---- symbolic dyadic bookkeeping ----
    # Exponents are tracked as formal linear combinations of the symbols
    # M, alpha, beta, s and 1, so that the cancellations below are exact
    # identities rather than numerical coincidences.
    def lin(**kw) -> dict:
        return {key: Fraction(val) for key, val in kw.items() if val}

    def add(*terms) -> dict:
        out: dict = {}
        for t in terms:
            for key, val in t.items():
                out[key] = out.get(key, Fraction(0)) + val
        return {key: val for key, val in out.items() if val}

    # Source: indicator (log x/log L)^M, three-form
    # (log X)^-7/4 (log L)^-3/4, residual (log x)^-3/4 (log L)^-1/4, and
    # division by rho_L which is asymptotic to 1/log L.
    src_logX = add(lin(M=1), lin(one=Fraction(-7, 4)), lin(one=Fraction(-3, 4)))
    src_logL = add(lin(M=-1), lin(one=Fraction(-3, 4)),
                   lin(one=Fraction(-1, 4)), lin(one=1))
    src_total = add(src_logL, src_logX, lin(one=1))
    check("source block exponent in log X is exactly M - 5/2",
          src_logX == lin(M=1, one=Fraction(-5, 2)), str(src_logX))
    check("source dyadic sum cancels M and leaves exactly (log L)^-3/2",
          src_total == lin(one=Fraction(-3, 2)), str(src_total))

    # Mixed: indicator (log x/log L)^M, three-form
    # (log X)^(alpha+beta+s-3) (log L)^(1-alpha-beta-s), residual
    # (log x)^(s-1) (log L)^-s.
    mix_logX = add(lin(M=1), lin(alpha=1, beta=1, s=1, one=-3),
                   lin(s=1, one=-1))
    mix_logL = add(lin(M=-1), lin(one=1, alpha=-1, beta=-1, s=-1), lin(s=-1))
    mix_total = add(mix_logL, mix_logX, lin(one=1))
    check("mixed block exponent in log X is exactly E = M+alpha+beta+2s-4",
          mix_logX == lin(M=1, alpha=1, beta=1, s=2, one=-4), str(mix_logX))
    check("mixed dyadic sum cancels every symbol and leaves exactly "
          "(log L)^-2", mix_total == lin(one=-2), str(mix_total))

    # Comparison of both losses against the source density rho_L ~ 1/log L.
    check("source loss (log L)^-3/2 beats rho_L by (log L)^-1/2",
          Fraction(-3, 2) + 1 < 0, "net exponent = -1/2")
    check("mixed loss (log L)^(-2 + c log q_o) beats rho_L",
          -2 + c * lnqo_hi + 1 < 0,
          f"net exponent < {decimal(-1 + c * lnqo_hi)}")

    widths = [ln4_hi - ln4_lo, lnqb_hi - lnqb_lo, lnqo_hi - lnqo_lo,
              lnzo_hi - lnzo_lo]
    check("all logarithm intervals have width below 10^-80",
          max(widths) < Fraction(1, 10 ** 80),
          f"maximum width = {decimal(max(widths))}")

    # ---- the only k-dependence is a finite multiplicative constant ----
    # The indicator majorisations pick up q_b^{Omega(2k)} q_o^{Omega(k)+1};
    # every exponent inequality above is free of k.  A finite cutoff L_k
    # absorbing this constant exists precisely because 1 - c log q_o > 0.
    net = -1 + c * lnqo_hi          # strictly negative by the check above
    ok = True
    report = []
    for k in range(1, 26, 2):
        Ck = QB ** big_omega(2 * k) * QO ** (big_omega(k) + 1)
        ok &= Ck > 0 and net < 0
        if k in (1, 3, 5, 15, 25):
            report.append((k, decimal(Ck)[:8]))
    check("for every odd k<=25 the k-dependent constant is finite and the "
          "net cutoff exponent is negative, so a finite L_k exists", ok,
          f"net exponent < {decimal(net)[:12]}; C_k samples {report}")


# --------------------------------------------------------------------------
# 9.  the largest-prime-factor fibration
# --------------------------------------------------------------------------

def audit_large_prime_fibration() -> None:
    print("9. largest-prime-factor fibration")
    bad_cross = None
    bad_fibre = None
    N = 800
    for k in (1, 2, 3, 5, 6):
        threshold = 1
        while threshold * threshold <= max(k, 2) * N:
            threshold += 1
        ps = [p for p in primes_upto(N) if p > threshold]
        for i, p in enumerate(ps):
            for q in ps[i + 1:]:
                for m1 in range(1, N // p + 1):
                    for m2 in range(1, N // q + 1):
                        a, b = p * m1, q * m2
                        if a != b and conflict(a, b, k):
                            bad_cross = (k, a, b)
        for p in ps:
            R = N // p
            for m1 in range(1, R + 1):
                for m2 in range(m1 + 1, R + 1):
                    if conflict(p * m1, p * m2, k) != conflict(m1, m2, k):
                        bad_fibre = (k, p, m1, m2)
    check("elements with different prime factors above sqrt(max(k,2)N) never "
          "conflict", bad_cross is None,
          "" if bad_cross is None else str(bad_cross))
    check("inside one fibre the conflict relation is exactly the original one",
          bad_fibre is None, "" if bad_fibre is None else str(bad_fibre))

    # The contraction constant: sum of 1/p over sqrt-range primes tends to
    # log 2 < 1, so the fibration can never bootstrap a density.
    lo, hi = log_bounds(Fraction(2))
    check("the fibration contraction constant log 2 is strictly below 1",
          hi < 1, f"log 2 < {decimal(hi)}")


# --------------------------------------------------------------------------
# 10.  end-to-end assembly in a finite box
# --------------------------------------------------------------------------

def audit_assembly() -> None:
    print("10. end-to-end two-layer assembly (combinatorics only)")
    print("     NOTE: this checks that the assembled set really is "
          "k-admissible.")
    print("     It cannot exhibit the density gain: that is asymptotic and "
          "needs")
    print("     L and N chosen in the legal order, far beyond any box.")
    for k, N in ((1, 400), (3, 400), (5, 300), (7, 300), (9, 260)):
        lam = dilation(k)
        m = k * lam
        L = max(m + 1, 3 * lam + 1)
        S = [b for b in range(N // 2, N + 1) if is_rough(b, L)]
        om = {n: big_omega(n) for n in range(1, lam * N + 1)}
        B = [b for b in S
             if not any(c != b and conflict(b, c, m) and om[c] <= om[b]
                        for c in range(1, N + 1))]
        odds = list(range(1, lam * N + 1, 2))
        gamma = {a for a in odds
                 if any((m * a * b) % (a + lam * b) == 0 for b in B)}
        A = sorted([a for a in odds if a not in gamma] + [lam * b for b in B])
        clash = None
        for i, ai in enumerate(A):
            for aj in A[i + 1:]:
                if conflict(ai, aj, k):
                    clash = (ai, aj)
                    break
            if clash:
                break
        check(f"k={k}, lambda={lam}, L={L}, N={N}: the assembled set is "
              "k-admissible", clash is None,
              f"|B|={len(B)}, |Gamma|={len(gamma)}, |A|={len(A)}, "
              f"odds={len(odds)}, gain={len(A) - len(odds):+d}"
              if clash is None else str(clash))


def main() -> int:
    audit_periodic_benchmark()
    audit_conflict_criterion()
    audit_two_adic()
    audit_source_coordinates()
    audit_mixed_coordinates()
    audit_local_roots()
    audit_euler_factors()
    audit_parameters()
    audit_large_prime_fibration()
    audit_assembly()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s): {', '.join(FAILURES)}")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
