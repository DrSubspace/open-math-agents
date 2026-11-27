"""Replay interval.json and certify each surviving n has a failing shift."""
import hashlib
import json
from math import gcd, prod
from pathlib import Path

import numpy as np
from flint import fmpz

from cofactor_check import BASE_SHIFTS, shapes
from witness_search import Sieve, reference


def factor_counts(n, shifts):
    counts = {}
    for k in shifts:
        factors = [(int(p), int(e)) for p, e in fmpz(n - k).factor()]
        assert all(fmpz(p).is_prime() for p, _ in factors)
        assert prod(p**e for p, e in factors) == n - k
        counts[k] = prod(e + 1 for _, e in factors)
    return counts


def certified_failure(n, multipliers):
    # A Fermat violation is a one-sided, exact certificate of compositeness.
    # A pseudoprime simply advances to another shift or the divisor fallback.
    for k in BASE_SHIFTS:
        m = n - k
        for d in multipliers[k]:
            q, remainder = divmod(m, d)
            if remainder == 0 and gcd(q, 2520) == 1 and pow(2, q - 1, q) == 1:
                break
        else:
            return "cofactor"
    for k in range(1, 129):
        m = n - k
        divisors = {1}
        for p, e in fmpz(m).factor():
            divisors = {d * int(p)**i for d in divisors for i in range(int(e) + 1)}
            if len(divisors) > k + 2:
                assert all(d > 0 and m % d == 0 for d in divisors)
                return "divisors"
    raise ValueError(f"Found a survivor requiring a longer audit: {n}")


if __name__ == "__main__":
    folder = Path(__file__).resolve().parent
    result = json.loads((folder / "interval.json").read_text())
    base, step, count = (result[k] for k in ("first", "step", "count"))
    assert base == result["start"] + (-result["start"]) % step
    assert base + (count - 1) * step < result["start"] + result["amount"] <= base + count * step
    sieve = Sieve(base, step, result["small_prime_limit"], 4)
    tally = {"cofactor": 0, "divisors": 0}
    exceptional = []
    fingerprint = 0
    multipliers = shapes()
    for batch in sieve.batches(count):
        for index in batch:
            i = int(index)
            n = base + i * step
            method = certified_failure(n, multipliers)
            tally[method] += 1
            if method == "divisors":
                k_extra = 16 if n % 16 == 0 else n % 128
                shifts = sorted(set(BASE_SHIFTS) | set(range(1, 14)) | {k_extra})
                exceptional.append({"n": n, "divisor_counts": factor_counts(n, shifts)})
            fingerprint ^= int.from_bytes(hashlib.sha256(str(i).encode()).digest(), "big")
    fingerprint = f"{fingerprint:064x}"
    assert sum(tally.values()) == result["survivors"] and fingerprint == result["xor_sha256"]
    # Use a shallow cutoff so the independent CPU array has positive controls.
    windows = []
    span = 2_000_003
    for off in (0, count // 2, count - span):
        test = Sieve(base + step * off, step, 521, 3)
        gpu = np.sort(np.concatenate(list(test.batches(span))))
        cpu = reference(test, span)
        assert len(cpu) > 0 and np.array_equal(cpu, gpu)
        windows.append({"offset": off, "length": span, "bound": 521, "survivors": len(cpu)})
    audit = {"device": sieve.device, "replay_wheel_primes": 4, "xor_sha256": fingerprint,
             "rejection_certificate_counts": tally, "cpu_comparisons": windows,
             "direct_divisor_cases": exceptional}
    print(json.dumps(audit, indent=2))
    (folder / "audit.json").write_text(json.dumps(audit, indent=2) + "\n", encoding="utf8")
