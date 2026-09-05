"""Tests of switching multiplicities, local edges, and rank-layer obstructions."""

import unittest
from itertools import product
from math import log

from ordering_cluster_probe import (
    cluster_histogram, component_count, grid_neighbors, profile_overlap_components,
    rank_layer_witness, summarize,
)


class OrderingClusterTests(unittest.TestCase):
    def test_empty_and_connected_bands(self):
        neighbors = grid_neighbors([3, 2])
        self.assertEqual(component_count(0, neighbors), 0)
        self.assertEqual(component_count((1 << 6) - 1, neighbors), 1)

    def test_four_dimensional_histogram(self):
        h, q, histogram = cluster_histogram([2, 2, 2, 1])
        self.assertEqual((h, q), (20, 168))
        self.assertEqual(histogram, {0: 20, 1: 110, 2: 36, 3: 2})

    def test_cubic_histogram(self):
        h, q, histogram = cluster_histogram([3, 3, 2])
        self.assertEqual((h, q), (175, 8790))
        self.assertEqual(histogram, {0: 175, 1: 4337, 2: 3290, 3: 903, 4: 83, 5: 2})

    def test_ensemble_bias_and_jensen_bounds(self):
        for shape in [[2, 1], [3, 2], [2, 2, 1], [3, 3, 2], [2, 2, 2, 1]]:
            row = summarize(shape)
            self.assertLessEqual(row["mean_clusters_uniform_ordered"],
                                 row["mean_clusters_sorted_independent"])
            self.assertLessEqual(row["jensen_lower_cost"], row["weak_ordering_cost"] + 1e-12)
            self.assertLessEqual(row["weak_ordering_cost"], row["jensen_upper_cost"] + 1e-12)
            self.assertAlmostEqual(row["weak_ordering_cost"], log(row["H"]**2 / row["Q"]))

    def test_rank_layers_are_valid_isolated_bands(self):
        for side in range(2, 6):
            witness = rank_layer_witness(side)
            shape = [side, side, side, side - 1]
            rank = witness["rank"]
            points = list(product(*(range(s) for s in shape)))
            lower = sum(1 << i for i, x in enumerate(points) if sum(x) < rank)
            upper = sum(1 << i for i, x in enumerate(points) if sum(x) <= rank)
            # Both thresholds are downsets; their difference is one rank layer.
            for mask in [lower, upper]:
                for i, x in enumerate(points):
                    if (mask >> i) & 1:
                        for axis, coordinate in enumerate(x):
                            if coordinate:
                                y = list(x)
                                y[axis] -= 1
                                self.assertEqual((mask >> points.index(tuple(y))) & 1, 1)
            neighbors = grid_neighbors(shape)
            count = component_count(upper ^ lower, neighbors)
            self.assertEqual(count, witness["components"])
            self.assertEqual(count, bin(upper ^ lower).count('1'))
            self.assertEqual(count, profile_overlap_components(lower, upper, shape))
            self.assertGreaterEqual(4 * count, side**3)


if __name__ == "__main__":
    unittest.main()
