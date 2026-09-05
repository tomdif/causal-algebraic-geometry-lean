#!/usr/bin/env python3
"""Exact finite tests of CAG's proposed compatibility-deficit area law.

No asymptotic fit, gravity model, or Lean numerical certificate is claimed.
Only Python's standard library is needed. Counts are arbitrary-size integers;
only the reported logarithms use floating point.

For ambient dimension j, D counts ideals of [m]^j, H counts ideals of
[m]^(j-1) x [m-1], and Q counts strictly separated boundary pairs. Removing
one unit from the upper boundary identifies Q with ideals of
[m]^(j-1) x [m-1] x [2]. Thus
  Delta = 2 log(D) - log(Q)
        = 2 log(D/H) + log(H^2/Q).
The two summands are height-trimming and weak-ordering costs, respectively.
"""

import argparse
import json
from fractions import Fraction
from itertools import product
from math import comb, isclose, log, prod


def rectangular_ideals(shape):
    """Bitmask ideals, using the immediate-predecessor recursion."""
    points = list(product(*(range(side) for side in shape)))
    index = {point: i for i, point in enumerate(points)}
    ideals = [0]
    for i, point in enumerate(points):
        predecessors = 0
        for axis, coordinate in enumerate(point):
            if coordinate:
                parent = list(point)
                parent[axis] -= 1
                predecessors |= 1 << index[tuple(parent)]
        ideals += [mask | (1 << i) for mask in ideals
                   if mask & predecessors == predecessors]
    return ideals


def decreasing_chains(ideals, length):
    if length == 0:
        return 1
    if length == 1:
        return len(ideals)
    if length <= 3:
        # A three-state chain is determined by its middle state and
        # independently chosen predecessor/successor. No matrix is stored.
        upper = [0] * len(ideals)
        lower = [0] * len(ideals)
        for i, inner in enumerate(ideals):
            for j, outer in enumerate(ideals):
                if inner & outer == inner:
                    upper[i] += 1
                    lower[j] += 1
        return sum(upper) if length == 2 else sum(a * b for a, b in zip(upper, lower))
    supersets = [[j for j, outer in enumerate(ideals) if inner & outer == inner]
                 for inner in ideals]
    counts = [1] * len(ideals)
    for _ in range(length - 1):
        counts = [sum(counts[j] for j in possible) for possible in supersets]
    return sum(counts)


def count_box(shape):
    if any(side == 0 for side in shape):
        return 1
    # Slice along a longest factor to minimize the transfer-state poset.
    shape = sorted(shape)
    return decreasing_chains(rectangular_ideals(shape[:-1]), shape[-1])


def macmahon(a, b, c):
    value = prod(Fraction(i + j + k - 1, i + j + k - 2)
                 for i, j, k in product(range(1, a + 1), range(1, b + 1),
                                        range(1, c + 1)))
    assert value.denominator == 1
    return value.numerator


def direct_strict_pairs(dimension, side):
    """Independent check: enumerate both actual height profiles, then compare."""
    masks = rectangular_ideals([side] * dimension)
    column_mask = (1 << side) - 1
    profiles = [tuple(bin((mask >> (column * side)) & column_mask).count('1')
                      for column in range(side ** (dimension - 1))) for mask in masks]
    return sum(all(a < b for a, b in zip(lower, upper))
               for lower in profiles for upper in profiles)


def probe(dimension, side):
    full_shape = [side] * dimension
    trimmed_shape = [side] * (dimension - 1) + [side - 1]
    d = count_box(full_shape)
    h = count_box(trimmed_shape)
    q = count_box(trimmed_shape + [2])
    assert 0 < q <= h * (h + 1) // 2 <= h * h <= d * d
    if side <= 2:
        assert d == len(rectangular_ideals(full_shape))
        assert q == direct_strict_pairs(dimension, side)
    if dimension == 2:
        assert d == comb(2 * side, side)
        assert q == macmahon(side, side - 1, 2)
        assert d * d == 2 * (side + 1) * q
    if dimension == 3:
        assert d == macmahon(side, side, side)
        assert h == macmahon(side, side, side - 1)
    trimming = 2 * (log(d) - log(h))
    ordering = 2 * log(h) - log(q)
    deficit = 2 * log(d) - log(q)
    assert isclose(deficit, trimming + ordering, rel_tol=1e-12)
    area = side ** (dimension - 2)
    return {"ambient_dimension": dimension, "side": side, "D": d, "H": h, "Q": q,
            "compatibility_probability": q / (d * d),
            "deficit": deficit, "height_trimming_cost": trimming,
            "weak_ordering_cost": ordering,
            "deficit_div_codimension_two_scale": deficit / area,
            "trimming_div_codimension_two_scale": trimming / area,
            "ordering_div_codimension_two_scale": ordering / area}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, choices=[2, 3, 4])
    parser.add_argument("--max-side", type=int)
    args = parser.parse_args()
    if args.max_side is not None and args.dimension is None:
        parser.error("--max-side requires --dimension")
    dimensions = [args.dimension] if args.dimension else [2, 3, 4]
    rows = []
    for dimension in dimensions:
        max_side = args.max_side if args.max_side is not None else {2: 5, 3: 4, 4: 3}[dimension]
        if not 1 <= max_side <= {2: 6, 3: 5, 4: 3}[dimension]:
            parser.error("Exact enumeration limited to sides 6, 5, 3 in dimensions 2, 3, 4")
        rows.extend(probe(dimension, side) for side in range(1, max_side + 1))
    print(json.dumps({"kind": "exact counts, floating-point logarithms; no asymptotic fit",
                      "results": rows}, indent=2))


if __name__ == "__main__":
    main()
