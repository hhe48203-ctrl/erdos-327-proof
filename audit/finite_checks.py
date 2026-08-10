#!/usr/bin/env python3
"""Independent finite checks for the elementary Erdos 327 reductions."""

from math import gcd, isqrt


def divides(d: int, n: int) -> bool:
    return d > 0 and n % d == 0


def divisors(n: int):
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            yield d
            if d * d != n:
                yield n // d


def primes_below(limit: int):
    for n in range(2, limit):
        if all(n % d for d in range(2, isqrt(n) + 1)):
            yield n


def rough(cutoff: int, n: int) -> bool:
    return all(n % p for p in primes_below(cutoff))


def factor_count_between(cutoff: int, upper: int, n: int) -> int:
    count = 0
    p = 2
    while p * p <= n:
        while n % p == 0:
            if cutoff <= p <= upper:
                count += 1
            n //= p
        p += 1
    if n > 1 and cutoff <= n <= upper:
        count += 1
    return count


def factor_count(n: int) -> int:
    return factor_count_between(2, n, n)


def conflict_one(a: int, b: int) -> bool:
    return divides(a + b, a * b)


def conflict_two(a: int, b: int) -> bool:
    return divides(a + b, 2 * a * b)


def mixed_conflict(a: int, b: int) -> bool:
    return divides(a + 2 * b, a * b)


def recover_mixed_coordinates(a: int, b: int):
    g = gcd(a, b)
    u, w = b // g, a // g
    linear = 2 * u + w
    assert divides(linear, g)
    return g // linear, u, w


def check_basic_reductions(limit: int = 180) -> int:
    checked = 0
    for a in range(1, limit + 1):
        for b in range(1, limit + 1):
            if a % 2 and b % 2:
                assert not conflict_one(a, b)
            assert conflict_one(2 * a, 2 * b) == conflict_two(a, b)
            if a % 2:
                assert conflict_one(a, 2 * b) == mixed_conflict(a, b)
                if mixed_conflict(a, b):
                    t, u, w = recover_mixed_coordinates(a, b)
                    assert t > 0 and gcd(u, w) == 1
                    assert a == t * w * (2 * u + w)
                    assert b == t * u * (2 * u + w)
                    checked += 1
    return checked


def check_coordinate_generation(limit: int = 36) -> int:
    endpoints = {}
    checked = 0
    for t in range(1, limit + 1):
        for u in range(1, limit + 1):
            for w in range(1, limit + 1):
                if gcd(u, w) != 1 or w % 2 == 0:
                    continue
                linear = 2 * u + w
                a, b = t * w * linear, t * u * linear
                assert mixed_conflict(a, b)
                assert recover_mixed_coordinates(a, b) == (t, u, w)
                prior = endpoints.setdefault((a, b), (t, u, w))
                assert prior == (t, u, w)
                checked += 1
    return checked


def check_local_three_form_geometry() -> int:
    checked = 0
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        centered = {
            (u, v)
            for u in range(p)
            for v in range(p)
            if u == 0 or v == 0 or (u + v) % p == 0
        }
        cross = {
            (u, w)
            for u in range(p)
            for w in range(p)
            if u == 0 or w == 0 or (2 * u + w) % p == 0
        }
        assert len(centered) == 3 * p - 2
        assert len(cross) == 3 * p - 2
        checked += p * p
    return checked


def check_mixed_anatomy_identity(limit: int = 45) -> int:
    checked = 0
    for cutoff in (3, 5, 7, 11, 13):
        for t in range(1, limit + 1):
            for u in range(1, limit + 1):
                for w in range(1, limit + 1):
                    linear = 2 * u + w
                    if not rough(cutoff, linear):
                        continue
                    assert w < linear
                    lhs = factor_count_between(
                        cutoff, linear, t * w * linear
                    )
                    rhs = (
                        factor_count_between(cutoff, linear, t)
                        + factor_count_between(cutoff, linear, w)
                        + factor_count(linear)
                    )
                    assert lhs == rhs
                    checked += 1
    return checked


def check_sawin_source_coordinates(limit: int = 260) -> int:
    checked = 0
    for b in range(1, limit + 1):
        for c in range(1, limit + 1):
            if not conflict_two(b, c):
                continue
            g = gcd(b, c)
            u, v = b // g, c // g
            assert gcd(u, v) == 1
            assert divides(u * (u + v), 2 * b)
            checked += 1
    return checked


def check_source_cutoff_endpoint(max_b: int = 600) -> int:
    checked = 0
    for cutoff in (3, 5, 7, 11, 13):
        for b in range(1, max_b + 1):
            if not rough(cutoff, b):
                continue
            twice_b = 2 * b
            for u in divisors(twice_b):
                quotient = twice_b // u
                for total in divisors(quotient):
                    if total <= u:
                        continue
                    v = total - u
                    d = quotient // total
                    assert twice_b == u * (u + v) * d
                    if (u, v) != (1, 1):
                        assert cutoff <= u + v
                        checked += 1
    return checked


def check_rough_source_density() -> int:
    checked = 0
    for cutoff in (3, 5, 7, 11):
        primes = tuple(primes_below(cutoff))
        modulus = 1
        totient = 1
        for p in primes:
            modulus *= p
            totient *= p - 1
        for n in range(4 * modulus, 5 * modulus + 1):
            count = sum(rough(cutoff, x) for x in range(n // 2, n + 1))
            assert n * totient <= 4 * modulus * count
            checked += 1
    return checked


def check_mixed_boundary_arithmetic(max_n: int = 60) -> int:
    checked = 0
    for n in range(2, max_n + 1):
        for t in range(1, n + 1):
            for u in range(1, n + 1):
                for w in range(1, 6 * n + 1):
                    linear = 2 * u + w
                    a = t * w * linear
                    b = t * u * linear
                    if n // 2 <= b <= n and a <= 2 * n:
                        assert w <= 6 * u
                        assert linear <= 8 * u
                        checked += 1
    return checked


def check_exceptional_endpoint_uniqueness(max_n: int = 500) -> int:
    checked = 0
    for n in range(1, max_n + 1):
        pairs = [
            (a, b)
            for a in range(1, 2 * n, 2)
            for b in range(n // 2, n + 1)
            if 4 * b < a
        ]
        assert len(pairs) <= 1
        checked += len(pairs)
    return checked


def main() -> None:
    results = {
        "recovered mixed conflicts": check_basic_reductions(),
        "generated coprime triples": check_coordinate_generation(),
        "three-form residue pairs": check_local_three_form_geometry(),
        "exact mixed anatomy instances": check_mixed_anatomy_identity(),
        "Sawin conflict pairs": check_sawin_source_coordinates(),
        "rough cutoff representations": check_source_cutoff_endpoint(),
        "rough source density bounds": check_rough_source_density(),
        "mixed boundary instances": check_mixed_boundary_arithmetic(),
        "exceptional endpoint pairs": check_exceptional_endpoint_uniqueness(),
    }
    for label, count in results.items():
        print(f"ok: {label}: {count}")


if __name__ == "__main__":
    main()
