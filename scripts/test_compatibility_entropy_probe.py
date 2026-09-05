"""Independent small-case checks for the compatibility entropy experiment."""

import unittest
from itertools import product
from math import isclose, log

from compatibility_entropy_probe import (
    count_box, decreasing_chains, direct_strict_pairs, probe, rectangular_ideals,
)


def brute_ideals(shape):
    points = list(product(*(range(side) for side in shape)))
    required = [(i, j) for i, x in enumerate(points) for j, y in enumerate(points)
                if all(a <= b for a, b in zip(x, y))]
    return {mask for mask in range(1 << len(points))
            if all(not (mask >> j) & 1 or (mask >> i) & 1 for i, j in required)}


class CompatibilityEntropyTests(unittest.TestCase):
    def test_ideals_against_all_subsets(self):
        for shape in [(0,), (1,), (3,), (2, 2), (2, 3), (2, 2, 2), (2, 2, 2, 2)]:
            with self.subTest(shape=shape):
                expected = brute_ideals(shape)
                self.assertEqual(set(rectangular_ideals(shape)), expected)
                self.assertEqual(count_box(shape), len(expected))

    def test_transfers_against_all_chains(self):
        ideals = rectangular_ideals((2, 2))
        for length in range(5):
            expected = sum(all(inner & outer == inner
                               for outer, inner in zip(chain, chain[1:]))
                           for chain in product(ideals, repeat=length))
            self.assertEqual(decreasing_chains(ideals, length), expected)

    def test_strict_to_weak_reduction(self):
        for dimension, side in [(2, 3), (3, 3), (4, 2)]:
            self.assertEqual(count_box([side] * (dimension - 1) + [side - 1, 2]),
                             direct_strict_pairs(dimension, side))

    def test_two_dimensional_logarithmic_control(self):
        for side in range(1, 7):
            row = probe(2, side)
            self.assertTrue(isclose(row["deficit"], log(2 * (side + 1)), rel_tol=1e-12))
            self.assertTrue(isclose(row["height_trimming_cost"], log(4), rel_tol=1e-12))

    def test_three_dimensional_macmahon_control(self):
        for side, expected in [(1, 2), (2, 20), (3, 980), (4, 232848)]:
            # probe also checks both full and trimmed counts against the
            # independent three-dimensional product formula.
            self.assertEqual(probe(3, side)["D"], expected)

    def test_four_dimensional_three_box_regression(self):
        row = probe(4, 3)
        self.assertEqual((row["D"], row["H"], row["Q"]),
                         (17792748, 211250, 4142605276))
        self.assertAlmostEqual(row["deficit_div_codimension_two_scale"], 1.2493347013833447)


if __name__ == "__main__":
    unittest.main()
