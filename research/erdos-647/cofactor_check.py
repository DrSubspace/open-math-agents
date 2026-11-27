"""Enumerate the necessary n-k = d*q shapes for large witnesses, with q prime."""
from functools import lru_cache
from math import gcd, lcm

BASE_SHIFTS = (1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 20, 24)
BRANCHES = {16: 16, 56: 128 * 7, 120: 128 * 3 * 5}
MODULUS = lcm(2520, 128)


def smooth_multiples(a, budget):
    """All multiples of a supported on its primes and having tau <= budget."""
    pairs = [(1, 1)]
    remainder = a
    for p in range(2, a + 1):
        if remainder % p == 0:
            while remainder % p == 0:
                remainder //= p
            pairs = [(v * p**e, t * (e + 1))
                     for v, t in pairs for e in range(budget // t)]
        if remainder == 1:
            break
    return [v for v, _ in pairs if v % a == 0]


def check_progression():
    """Bootstrap divisibility by 360360, then close the small exceptions directly."""
    modulus = 1
    thresholds = []
    for power in (2, 4, 8, 3, 9, 5, 7, 11, 13):
        common = gcd(modulus, power)
        cases = []
        for residue in range(common, power, common):
            bounds = []
            for k in BASE_SHIFTS:
                if modulus % k or k % power != residue:
                    continue
                a = lcm(k, power)
                tau = sum(a % i == 0 for i in range(1, a + 1))
                if 2 * tau > k + 2:
                    bounds.append(k + max(smooth_multiples(a, k + 2), default=0))
            assert bounds, (power, residue)
            cases.append(min(bounds))
        thresholds.append(max(cases))
        modulus = lcm(modulus, power)
    cutoff = max(thresholds)
    assert modulus == 360360 and cutoff == 4080
    divisors = [0] * (cutoff + 1)
    for d in range(1, cutoff + 1):
        for m in range(d, cutoff + 1, d):
            divisors[m] += 1
    assert all(any(divisors[n - k] > k + 2 for k in range(1, n))
               for n in range(25, cutoff + 1))
    return thresholds


def branch_matches(n, k):
    if k == 16:
        return n % 16 == 0
    if k in (56, 120):
        return n % 128 == k
    return True


@lru_cache(maxsize=1)
def shapes():
    units = [u for u in range(MODULUS) if gcd(u, MODULUS) == 1]
    result = {}
    for k in (*BASE_SHIFTS, *BRANCHES):
        a = BRANCHES.get(k, k)
        budget = k + 2
        tau_a = sum(a % i == 0 for i in range(1, a + 1))
        assert 4 * tau_a > budget
        smooth = smooth_multiples(a, budget)
        assert k + max(smooth) * 120**2 < 10**22
        targets = {r for r in range(0, MODULUS, 2520) if branch_matches(r, k)}
        for e in (1, 2):
            powers = {pow(u, e, MODULUS) for u in units}
            candidates = [d for d in smooth_multiples(a, budget // (e + 1))
                          if any((k + d * r) % MODULUS in targets for r in powers)]
            if e == 1:
                result[k] = sorted(candidates)
            else:
                assert not candidates, (k, candidates)
    return result


if __name__ == "__main__":
    print("Divisibility induction cutoffs:", *check_progression())
    for shift, multipliers in shapes().items():
        print(shift, *multipliers)
