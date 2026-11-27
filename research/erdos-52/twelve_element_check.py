"""Check 12-element sets made of decreasing rows of powers of 2 scaled by t**j.

The second generator t ranges over all positive rational numbers. Multiplying
by a common denominator gives positive integer sets with the same two counts.
Uses Python 3 with no external packages.
"""

from functools import cache
from itertools import combinations, combinations_with_replacement
from math import gcd, isqrt


def partitions(n, bound):
    if not n:
        yield ()
    for size in range(min(n, bound), 0, -1):
        for rest in partitions(n-size, size):
            yield (size,) + rest


@cache
def divisors(n):
    small = [d for d in range(1, isqrt(n)+1) if n % d == 0]
    return small + [n//d for d in small if d*d != n]


def forms(widths):
    rows = len(widths)
    points = [(i,j) for j,w in enumerate(widths) for i in range(w)]
    sums, products = set(), set()
    for (i,j),(k,l) in combinations_with_replacement(points,2):
        coef = [0]*rows
        coef[j] += 1 << i
        coef[l] += 1 << k
        sums.add(tuple(coef))
        products.add((i+k,j+l))
    return sums, products


def exceptional_ratios(sums):
    # Colliding formal products imply t**b = 2**a with 0 < |b| and |a| <= 22.
    # A positive rational satisfying this identity is an integral power of 2.
    candidates = {(1 << k,1) for k in range(23)} | {(1,1 << k) for k in range(23)}
    endpoints = set()
    for f,g in combinations(sums,2):
        diff = [a-b for a,b in zip(f,g) if a != b]
        if min(diff) >= 0 or max(diff) <= 0:
            continue
        common = 0
        for c in diff:
            common = gcd(common,c)
        # Strip low powers of t and take the primitive polynomial's endpoints.
        endpoints.add((abs(diff[0])//common, abs(diff[-1])//common))
    for bottom,top in endpoints:
        for p in divisors(bottom):
            for q in divisors(top):
                if gcd(p,q) == 1:
                    candidates.add((p,q))
    return candidates


def cardinalities(widths,p,q):
    m = len(widths)-1
    A = [2**i * p**j * q**(m-j) for j,w in enumerate(widths) for i in range(w)]
    if len(set(A)) < len(A):
        return None
    pairs = list(combinations_with_replacement(A,2))
    return len({a+b for a,b in pairs}), len({a*b for a,b in pairs})


def search():
    best = 100
    tested = valid = shapes = 0
    minimizers = []
    for widths in partitions(12,12):
        shapes += 1
        sums,products = forms(widths)
        generic = max(len(sums),len(products))
        assert generic > 41
        for p,q in sorted(exceptional_ratios(sums)):
            tested += 1
            counts = cardinalities(widths,p,q)
            if counts is None:
                continue
            valid += 1
            score = max(counts)
            if score < best:
                best = score
                minimizers.clear()
            if score == best:
                minimizers.append((widths,p,q,counts))
    assert shapes == 77
    assert ((6,4,2),3,1,(41,35)) in minimizers
    print("shapes, candidate evaluations, valid:", shapes,tested,valid)
    print("minimum:",best)
    print("minimizers:",minimizers)


if __name__ == "__main__":
    search()
