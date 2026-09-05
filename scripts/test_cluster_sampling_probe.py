"""Deterministic statistical-interface and actual C++ sampler checks."""

import json
from math import log, sqrt
from pathlib import Path
import subprocess
import tempfile
import unittest

from cluster_sampling_probe import empirical_bernstein, summarize, summarize_ordered
from ordering_cluster_probe import cluster_histogram


class ClusterSamplingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="cag-sampler-tests-")
        cls.binary = Path(cls.directory.name) / "sampler"
        cls.checks = Path(cls.directory.name) / "checks"
        source = Path(__file__).parent
        for name, target in [("cluster_cftp.cpp", cls.binary), ("cluster_cftp_checks.cpp", cls.checks)]:
            subprocess.run(["c++", "-std=c++17", "-O2", "-Wall", "-Wextra", "-pedantic",
                            str(source / name), "-o", str(target)], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def sample(self, side, pairs, seed, ordered=False):
        command = [str(self.binary), "3", str(side), str(pairs), str(seed)]
        if ordered:
            command.append("--ordered")
        return json.loads(subprocess.run(command, check=True, capture_output=True, text=True).stdout)

    def test_actual_cpp_exhaustive_checks(self):
        result = subprocess.run([str(self.checks)], check=True, capture_output=True, text=True)
        self.assertIn("exhaustive full-state checks passed", result.stdout)

    def test_empirical_bernstein_formula(self):
        result = empirical_bernstein([2, 2], float, 1, 0.01)
        self.assertEqual(result["estimate"], 0.5)
        self.assertAlmostEqual(result["sample_variance"], 1 / 3)
        self.assertAlmostEqual(result["radius"], sqrt(2 * (1 / 3) * log(400) / 4) + 7 * log(400) / 9)

    def test_invalid_incomplete_batch_rejected(self):
        with self.assertRaises(ValueError):
            summarize({"side": 2, "base_dimension": 3, "pairs": 10,
                       "cluster_histogram": [1] * 9, "volume_histogram": [20]}, 0.01)

    def test_small_batch_without_informative_cdf(self):
        raw = {"side": 2, "base_dimension": 3, "pairs": 2, "seed": 1,
               "cluster_histogram": [0, 0, 0, 2, 0, 0, 0, 0, 0], "volume_histogram": [4],
               "total_coupled_updates": 0, "largest_horizon": 0, "seconds": 0}
        row = summarize(raw, 0.0001)
        self.assertIsNone(row["best_low_cluster_event"])
        self.assertTrue(row["interval_consistent"])

    def test_exact_low_cluster_event_bound(self):
        for shape in [[2, 2, 2, 1], [3, 3, 2]]:
            h, q, histogram = cluster_histogram(shape)
            cost = log(h * h / q)
            mass = 0
            for threshold in range(max(histogram) + 1):
                mass += histogram[threshold] * 2**threshold
                probability = mass / (h * h)
                self.assertLessEqual(cost, threshold * log(2) - log(probability) + 1e-12)

    def test_seed_replay_and_small_exact_ensemble(self):
        first = self.sample(2, 8000, 99173)
        second = self.sample(2, 8000, 99173)
        self.assertEqual(first["cluster_histogram"], second["cluster_histogram"])
        self.assertEqual(first["total_coupled_updates"], second["total_coupled_updates"])
        _, _, ordered = cluster_histogram([2, 2, 2, 1])
        expected = {c: n * 2**c / 400 for c, n in ordered.items()}
        # Fixed-seed smoke test, NOT the proof of uniformity or an adaptive stopping rule.
        epsilon = sqrt(log(2 * 9 / 0.0001) / (2 * 8000))
        for c, frequency in enumerate(first["cluster_histogram"]):
            self.assertLessEqual(abs(frequency / 8000 - expected.get(c, 0)), epsilon)
        row = summarize(first, 0.01)
        self.assertLessEqual(row["weak_ordering_cost_interval"][0], log(400 / 168))
        self.assertGreaterEqual(row["weak_ordering_cost_interval"][1], log(400 / 168))

    def test_ordered_ensemble_is_not_independent(self):
        raw = self.sample(2, 8000, 77431, ordered=True)
        expected = [20 / 168, 110 / 168, 36 / 168, 2 / 168]
        epsilon = sqrt(log(2 * 9 / 0.0001) / (2 * 8000))
        for c, probability in enumerate(expected):
            self.assertLessEqual(abs(raw["cluster_histogram"][c] / 8000 - probability), epsilon)
        row = summarize_ordered(raw, 0.01)
        self.assertLessEqual(row["mean_clusters"]["lower"], 47 / 42)
        self.assertGreaterEqual(row["mean_clusters"]["upper"], 47 / 42)


if __name__ == "__main__":
    unittest.main()
