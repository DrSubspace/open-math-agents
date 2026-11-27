"""Construct and challenge R1/R2 seed assignments. Requires NumPy, Python 3."""

from math import prod
import numpy as np


def divisors(factors):
    result = [1]
    for p, e in factors:
        result = [d * p**j for d in result for j in range(e + 1)]
    return sorted(result)[1:]


def choose_residue(xs, d, rng):
    if not len(xs):
        return int(rng.integers(d))
    if d > 100_000:
        # Optimize large moduli on a smaller set to keep each move cheap.
        xs = xs[:3000]
    vals = xs % d
    if d <= 100_000:
        counts = np.bincount(vals, minlength=d)
        winners = np.flatnonzero(counts == counts.max())
    else:
        labels, counts = np.unique(vals, return_counts=True)
        winners = labels[counts == counts.max()]
    return int(rng.choice(winners))


def experiment(factors, tag):
    ds = divisors(factors)
    m = prod(p**e for p, e in factors)
    fresh = [p for p in (3,5,7,11,13,17,19,23,29,31,37,41) if m % p][:2]
    single, other = ((len(ds)-1)//(p-2) for p in fresh)
    # Common disjoint challenge set for the different candidate families.
    judge = np.random.default_rng(1980 + tag)
    check = np.unique(judge.integers(m, size=65_537, dtype=np.int64))
    scores = []
    for run in range(3):
        rng = np.random.default_rng(1600 + 10*tag + run)
        train = np.setdiff1d(rng.integers(m, size=100_000, dtype=np.int64), check)
        rng.shuffle(train)
        # Keep small moduli early. Vary the order within logarithmic bands.
        order = sorted(ds, key=lambda d: (d.bit_length(), rng.random()))
        active = train
        residue = {}
        for d in order:
            a = choose_residue(active, d, rng)
            residue[d] = a
            active = active[active % d != a]
        # Coordinate ascent. Update a class using points missed by every other class.
        cover = np.zeros(len(train), dtype=np.int32)
        for d, a in residue.items():
            cover += train % d == a
        small = [d for d in ds if d <= 4096]
        for _ in range(2):
            rng.shuffle(small)
            for d in small:
                old = train % d == residue[d]
                cover -= old
                xs = train[cover == 0]
                a = choose_residue(xs, d, rng)
                new = train % d == a
                if np.count_nonzero((cover == 0) & new) >= np.count_nonzero((cover == 0) & old):
                    residue[d] = a
                    cover += new
                else:
                    cover += old
        holes = check
        for d in ds:
            holes = holes[holes % d != residue[d]]
        assert len(holes) > single + other
        assert len(set(map(int, holes[:single+other+1]))) == single + other+1
        assert all(np.all(holes[:single+other+1] % d != residue[d]) for d in ds)
        scores.append(len(holes))
    print(f"M={m} divisors>1={len(ds)} fresh={fresh} R1={single} R2={single+other} "
          f"test={len(check)} holes={scores}", flush=True)


if __name__ == "__main__":
    primes = (3, 5, 7, 11, 13, 17, 19, 23, 29)
    for i, exponents in enumerate([(2,1,1,1,1,1,1,1,1), (3,2,1,1,1,1,1,1,1),
                                    (4,2,2,1,1,1,1,1,1), (3,1,1,1,1,1,1,1,1)]):
        experiment(list(zip(primes, exponents)), i)
