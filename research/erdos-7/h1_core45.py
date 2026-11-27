"""Verify the 45-coordinate weights and the product-space probability bound in h1-results.md."""

from fractions import Fraction as F
from functools import cache
from itertools import product
from math import ceil, gcd, prod

WEIGHTS = (
    "004000030003062000000064000005000060000006030",
    "006030000003031000000064000003001060000006060",
    "000060031000000004000066003004000030000006060",
    "006060064000060000000000003004001030000006030",
    "004060064003036000000030000001000000000006060",
    "004030061000062000000030003002000060006006000",
    "000020003003023030000030003003020030003000030",
    "000020022002000010000020002002020010002000022",
    "000030033000033020000000003003030020003003020",
    "000020022000022020000022002002000010000002010",
    "000020022000010020000022002002010000000002022",
    "000010022000022020000022002002010020000002000",
)


def check_weights():
    moduli = (3, 5, 9, 15, 45)
    supports = set()
    for row in WEIGHTS:
        w = list(map(int, row))
        assert len(w) == 45 and 8 * max(w) <= sum(w)
        peaks = sum(max(sum(w[r::d]) for r in range(d)) for d in moduli)
        assert 3 * peaks <= 4 * sum(w)
        for u in range(45):
            if gcd(u, 45) == 1:
                for shift in (0, 15, 30):
                    supports.add(sum(1 << ((u*x+shift) % 45) for x in range(45) if w[x]))
    masks = {d: [sum(1 << x for x in range(r, 45, d)) for r in range(d)] for d in moduli}
    for i, j, k in product(range(9), range(15), range(45)):
        used = masks[3][0] | masks[5][0] | masks[9][i] | masks[15][j] | masks[45][k]
        assert any(s & used == 0 for s in supports), (i, j, k)


def check_polynomial():
    outside = (7, 11, 13, 17, 19, 23, 29)
    anchor = 1 << len(outside)
    atoms = (anchor << 1) - 1
    weights = {}
    for mask in range(1, atoms + 1):
        if mask.bit_count() < 2:
            continue
        weight = prod(F(1, q-1) for i, q in enumerate(outside) if mask & (1 << i))
        weights[mask] = weight * (F(4, 3) if mask & anchor else 1)

    @cache
    def z(mask):
        if mask == 0:
            return F(1)
        first = mask & -mask
        return z(mask ^ first) - sum(
            weight * z(mask ^ edge) for edge, weight in weights.items()
            if edge & first and (edge & mask) == edge
        )

    assert all(z(mask) > 0 for mask in range(atoms + 1))
    # Independent recurrence on the largest coordinate.
    @cache
    def last_z(mask):
        if not mask:
            return F(1)
        last = 1 << (mask.bit_length()-1)
        total = last_z(mask ^ last)
        edge = mask
        while edge:
            if edge & last and edge in weights:
                total -= weights[edge] * last_z(mask ^ edge)
            edge = (edge-1) & mask
        return total

    assert all(last_z(mask) == z(mask) for mask in range(atoms + 1))
    holes = ceil(8 * prod(p-1 for p in outside) * z(atoms))
    print("Avoidance probability at least", z(atoms), "; at least", holes, "holes.")
    assert holes > 766 // 5 + 766 // 9
    return holes


if __name__ == "__main__":
    check_weights()
    check_polynomial()
