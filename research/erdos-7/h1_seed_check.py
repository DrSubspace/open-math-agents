"""Exact checks for the H1 starting-period restriction; Python 3, standard library."""

from fractions import Fraction
from math import isqrt, prod


def primes_to(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = b"\0\0"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n - p*p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def density_check(primes, count, budget):
    none, one = Fraction(1), Fraction(0)
    period_per_divisor = Fraction(1)
    for p in primes[:count]:
        b = Fraction(1, p - 1)
        none, one = none * (1 - b), one * (1 - b) + none * b
        period_per_divisor *= Fraction(p, 2)
        assert (2 * none + one - 1) * period_per_divisor > budget


def capacity_check(primes, omitted, smallest_s, required):
    # Each summand rounds DOWN a uniform lower bound on capacity / s.
    scale = 10**12
    lower = 0
    for p in primes[omitted:]:
        d = p - 2
        t = smallest_s // d
        if not t:
            break
        lower += scale * t // ((t + 1) * d)
    assert Fraction(lower, scale) > required, (omitted, smallest_s, lower)
    return lower


def rank_seven_check():
    # 3,5,7,11,13,17 in their minimum exponents contribute this bound:
    # M/tau(M) >= 255255*q/64, where q is the largest prime factor.
    density_denominator = 1_002_375
    limit = density_denominator * Fraction(14, 45)
    assert limit * 64 / 255255 < 79
    primes = [p for p in primes_to(79) if p >= 3]
    counts = [0, 0]

    def visit(start, factors, ratio):
        if len(factors) == 7:
            counts[0] += 1
            period = prod(p**e for p, e in factors)
            tau = prod(e+1 for p, e in factors)
            fresh = [p for p in primes if all(p != q for q, _ in factors)][:2]
            budget = sum((tau-2)//(p-2) for p in fresh)
            if period > density_denominator * budget:
                return
            counts[1] += 1
            none, one = 1, 0
            for p, e in factors:
                b = (p**e-1)//(p-1)
                a = p**e-b
                none, one = none*a, one*a + none*b
            holes = 2*none + one-period
            print("Seven-prime exception", period, "budget", budget, "lower bound", holes)
            assert holes > budget
            return
        remaining = 6-len(factors)
        for i in range(start, len(primes)-remaining):
            q = primes[i]
            if len(factors) < 2 and q != (3, 5)[len(factors)]:
                break
            tail_min = prod(Fraction(p, 2) for p in primes[i+1:i+1+remaining])
            if ratio * Fraction(q, 2) * tail_min > limit:
                break
            e = 2 if not factors else 1
            while ratio * Fraction(q**e, e+1) * tail_min <= limit:
                visit(i+1, factors + [(q, e)], ratio * Fraction(q**e, e+1))
                e += 1

    visit(0, [], Fraction(1))
    assert counts == [78, 2]


def main():
    primes = primes_to(10_000_000)
    assert len(primes) == 664579
    density_check(primes[2:], 26, Fraction(4, 3))  # 3 absent
    density_check([3] + primes[3:], 8, Fraction(8, 15))  # 3 present, 5 absent
    # Up to 63 factors of M plus one already assigned fresh prime, beyond 2 and 3.
    broad = capacity_check(primes[2:], 64, 2**27 - 2, 1)
    print("27 through 63 factors, uniform capacity fraction at least", Fraction(broad, 10**12))
    # When 3 divides M, at most k-1 of its primes lie above 5.
    # One more fresh prime may be reserved for the other list.
    p_after_5 = primes[3:]
    for low, high in [(9, 9), (10, 11), (12, 16), (17, 26)]:
        bound = capacity_check(p_after_5, high, 2**low - 2, Fraction(1, 3))
        print("5 absent, factor counts", low, high, "at least", Fraction(bound, 10**12))
    rank_seven_check()
    print("All finite certificate inequalities passed.")


if __name__ == "__main__":
    main()
