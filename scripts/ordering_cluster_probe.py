#!/usr/bin/env python3
"""Exact disagreement-cluster tests; no area law or gravity is assumed.

Uniform independent ideal pairs sort into nested pairs with multiplicity
2^c, where c is the number of connected components of the difference.
Enumerations are intentionally small. Rank-layer witnesses need no ideal
enumeration and show why a worst-case component bound cannot prove area scaling.
"""

import json
from collections import Counter
from fractions import Fraction
from itertools import product
from math import isclose, log

from compatibility_entropy_probe import rectangular_ideals


def grid_neighbors(shape):
    points = list(product(*(range(side) for side in shape)))
    index = {point: i for i, point in enumerate(points)}
    neighbors = [0] * len(points)
    for i, point in enumerate(points):
        for axis, coordinate in enumerate(point):
            for step in [-1, 1]:
                if 0 <= coordinate + step < shape[axis]:
                    other = list(point)
                    other[axis] += step
                    neighbors[i] |= 1 << index[tuple(other)]
    return neighbors


def component_count(mask, neighbors):
    components = 0
    while mask:
        components += 1
        frontier = mask & -mask
        mask ^= frontier
        while frontier:
            vertex = frontier & -frontier
            frontier ^= vertex
            discovered = neighbors[vertex.bit_length() - 1] & mask
            mask ^= discovered
            frontier |= discovered
    return components


def profile_overlap_components(lower, upper, shape):
    """Independent implementation of the base-overlap relation used in Lean."""
    height = shape[-1]
    base = list(product(*(range(side) for side in shape[:-1])))
    column_mask = (1 << height) - 1
    lo = [bin((lower >> (i * height)) & column_mask).count('1') for i in range(len(base))]
    hi = [bin((upper >> (i * height)) & column_mask).count('1') for i in range(len(base))]
    active = sum(1 << i for i in range(len(base)) if lo[i] < hi[i])
    neighbors = [0] * len(base)
    for i, x in enumerate(base):
        for j, y in enumerate(base):
            if i != j and all(a <= b for a, b in zip(x, y)) and lo[i] < hi[j]:
                neighbors[i] |= 1 << j
                neighbors[j] |= 1 << i
    return component_count(active, neighbors)


def cluster_histogram(shape, check_overlap=True):
    ideals = rectangular_ideals(shape)
    fibers = Counter((a & b, a | b) for a in ideals for b in ideals)
    neighbors = grid_neighbors(shape)
    histogram = Counter()
    for (lower, upper), multiplicity in fibers.items():
        components = component_count(upper ^ lower, neighbors)
        assert multiplicity == 1 << components, "Sorting fiber is not 2^c"
        if check_overlap:
            assert components == profile_overlap_components(lower, upper, shape)
        histogram[components] += 1
    h, q = len(ideals), len(fibers)
    assert sum(n * (1 << c) for c, n in histogram.items()) == h * h
    assert sum(histogram.values()) == q
    return h, q, histogram


def summarize(shape):
    h, q, histogram = cluster_histogram(shape)
    ordered_mean = Fraction(sum(c * n for c, n in histogram.items()), q)
    independent_mean = Fraction(sum(c * n * (1 << c) for c, n in histogram.items()), h * h)
    independent_inverse_moment = sum(Fraction(n * (1 << c), h * h) / (1 << c)
                                     for c, n in histogram.items())
    assert independent_inverse_moment == Fraction(q, h * h)
    cost = 2 * log(h) - log(q)
    lower, upper = float(ordered_mean) * log(2), float(independent_mean) * log(2)
    assert lower - 1e-12 <= cost <= upper + 1e-12
    assert isclose(cost, -log(float(independent_inverse_moment)), abs_tol=1e-12)
    return {"shape": shape, "H": h, "Q": q,
            "ordered_pair_cluster_histogram": dict(sorted(histogram.items())),
            "weak_ordering_cost": cost,
            "mean_clusters_uniform_ordered": float(ordered_mean),
            "mean_clusters_sorted_independent": float(independent_mean),
            "jensen_lower_cost": lower, "jensen_upper_cost": upper}


def rank_layer_witness(side):
    """Maximum rank layer in [m]^3 x [m-1] is an antichain band.

    There are m^3*(m-1) cells and 4*(m-1) possible ranks. Some band
    therefore has at least m^3/4 isolated components, for every m >= 2.
    This is a worst-case witness, NOT its probability in either ensemble.
    """
    assert side >= 2
    coefficients = [1]
    for length in [side, side, side, side - 1]:
        updated = [0] * (len(coefficients) + length - 1)
        for rank, count in enumerate(coefficients):
            for step in range(length):
                updated[rank + step] += count
        coefficients = updated
    rank = max(range(len(coefficients)), key=coefficients.__getitem__)
    components = coefficients[rank]
    assert sum(coefficients) == side**3 * (side - 1)
    assert len(coefficients) == 4 * (side - 1)
    assert 4 * components >= side**3
    return {"side": side, "rank": rank, "components": components,
            "components_div_side_squared": components / side**2,
            "pigeonhole_lower_bound": str(Fraction(side**3, 4))}


def main():
    print(json.dumps({
        "kind": "exact finite switching tests; floating-point entropies",
        "ensembles": [summarize(shape) for shape in [[2, 1], [3, 2], [2, 2, 1],
                                                    [3, 3, 2], [2, 2, 2, 1]]],
        "worst_case_rank_layer_witnesses": [rank_layer_witness(m) for m in [2, 3, 4, 8, 16, 32]],
    }, indent=2))


if __name__ == "__main__":
    main()
