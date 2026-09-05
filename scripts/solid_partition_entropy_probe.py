#!/usr/bin/env python3
"""Exact small-box volume counts for the CAG solid-partition program.

The transfer states are all downsets of [m]^3; a boxed solid partition is a
decreasing chain of m such states.  Integer polynomials record volume.
This is an exploratory computation, not a Lean certificate or an asymptotic
estimate.  Run with Python 3; no third-party packages are required.
"""

import argparse
import json
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import log, prod


def grid_ideals(dimension: int, side: int) -> list[int]:
    """Enumerate downsets in a topological order using immediate predecessors."""
    points = list(product(range(side), repeat=dimension))
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


def boxed_histogram(side: int) -> tuple[list[int], int]:
    ideals = grid_ideals(3, side)
    macmahon = prod(
        Fraction(i + j + k - 1, i + j + k - 2)
        for i, j, k in product(range(1, side + 1), repeat=3)
    )
    assert len(ideals) == macmahon, "Transfer states disagree with MacMahon"
    sizes = [bin(mask).count("1") for mask in ideals]
    supersets = [[i for i, outer in enumerate(ideals) if inner & outer == inner]
                 for inner in ideals]
    counts = [{size: 1} for size in sizes]
    for _ in range(1, side):
        next_counts = []
        for inner, possible_outer in enumerate(supersets):
            coefficients = defaultdict(int)
            for outer in possible_outer:
                for volume, count in counts[outer].items():
                    coefficients[volume + sizes[inner]] += count
            next_counts.append(dict(coefficients))
        counts = next_counts
    histogram = [0] * (side**4 + 1)
    for coefficients in counts:
        for volume, count in coefficients.items():
            histogram[volume] += count
    assert histogram == histogram[::-1], "Box-complement symmetry failed"
    assert histogram[0] == histogram[-1] == 1
    if side <= 2:
        direct = Counter(bin(mask).count("1") for mask in grid_ideals(4, side))
        assert histogram == [direct[n] for n in range(side**4 + 1)]
    return histogram, len(ideals)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sides", nargs="+", type=int, default=[1, 2, 3],
                        choices=[1, 2, 3])
    parser.add_argument("--histogram", action="store_true")
    args = parser.parse_args()
    results = []
    for side in args.sides:
        histogram, states = boxed_histogram(side)
        total, peak = sum(histogram), max(histogram)
        peak_volumes = [n for n, count in enumerate(histogram) if count == peak]
        assert total <= (side**4 + 1) * peak
        result = {
            "side": side,
            "plane_partition_transfer_states": states,
            "boxed_solid_partitions": total,
            "max_coefficient": peak,
            "maximizing_volumes": peak_volumes,
            "log_total_div_side_cubed": log(total) / side**3,
            "log_total_minus_log_max_coefficient": log(total) - log(peak),
            "first_coefficients": histogram[: min(7, len(histogram))],
        }
        if args.histogram:
            result["histogram"] = histogram
        results.append(result)
    print(json.dumps({"kind": "exact finite counts; not an asymptotic fit",
                      "results": results}, indent=2))


if __name__ == "__main__":
    main()
