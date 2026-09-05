#!/usr/bin/env python3
"""Fixed-size CFTP cluster experiment with simultaneous uncertainty bounds.

Requires Python 3 and a C++17 compiler. CFTP is exact in the ideal independent
random-bit model; this implementation uses mt19937_64. The sampler and the
statistical coverage arguments are not Lean-verified. No asymptotic fit is made.

References: Propp--Wilson (1996), and Maurer--Pontil (2009), Theorem 4.
The confidence budget is split over the preselected box sides and three
methods: mean clusters, inverse moment, and all low-cluster thresholds.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess
import tempfile


def empirical_bernstein(histogram, observable, span, delta):
    """Two-sided bounded-variable interval; unbiased sample variance.

    Apply Maurer--Pontil Theorem 4 to X/span and 1-X/span, with delta/2
    for each direction. This produces log(4/delta), not log(2/delta).
    """
    n = sum(histogram)
    if n < 2 or not 0 < delta < 1 or span <= 0:
        raise ValueError("Need n >= 2, positive range, and delta in (0,1)")
    mean = sum(count * observable(c) for c, count in enumerate(histogram)) / n
    variance = sum(count * (observable(c) - mean)**2 for c, count in enumerate(histogram)) / (n - 1)
    logarithm = math.log(4) - math.log(delta)
    radius = math.sqrt(2 * variance * logarithm / n) + 7 * span * logarithm / (3 * (n - 1))
    return {"estimate": mean, "sample_variance": variance, "radius": radius,
            "lower": max(0.0, mean - radius), "upper": min(span, mean + radius)}


def summarize(raw, method_delta):
    dimension, side, n = raw["base_dimension"], raw["side"], raw["pairs"]
    histogram = raw["cluster_histogram"]
    maximum = side**dimension  # At most one component per active base column.
    if len(histogram) != maximum + 1 or sum(histogram) != n:
        raise ValueError("Malformed or incomplete CFTP cluster histogram")
    if any(not isinstance(value, int) or value < 0 for value in histogram):
        raise ValueError("Invalid histogram frequency")
    if sum(raw["volume_histogram"]) != 2 * n:
        raise ValueError("Incomplete profile batch")
    area = side**(dimension - 1)
    mean = empirical_bernstein(histogram, float, maximum, method_delta)
    inverse = empirical_bernstein(histogram, lambda c: math.ldexp(1.0, -c), 1.0, method_delta)
    # Two-sided Hoeffding plus a union bound covers every integer threshold
    # simultaneously, permitting selection of K AFTER seeing the histogram.
    cdf_radius = math.sqrt((math.log(2 * (maximum + 1)) - math.log(method_delta)) / (2 * n))
    cumulative, best = 0, None
    tails = []
    thresholds = {min(maximum, area // 2), min(maximum, area), min(maximum, 2 * area)}
    for threshold, frequency in enumerate(histogram):
        cumulative += frequency
        empirical_cdf = cumulative / n
        lower_probability = max(0.0, empirical_cdf - cdf_radius)
        if lower_probability > 0:
            upper = threshold * math.log(2) - math.log(lower_probability)
            if best is None or upper < best["cost_upper_bound"]:
                best = {"threshold": threshold, "empirical_probability": empirical_cdf,
                        "probability_lower_bound": lower_probability, "cost_upper_bound": upper}
        if threshold in thresholds:
            tails.append({"threshold": threshold, "event": "clusters > threshold",
                          "empirical_probability": 1 - empirical_cdf,
                          "probability_lower_bound": max(0.0, 1 - empirical_cdf - cdf_radius),
                          "probability_upper_bound": min(1.0, 1 - empirical_cdf + cdf_radius)})
    inverse_upper = -math.log(inverse["lower"]) if inverse["lower"] > 0 else None
    upper_candidates = [math.log(2) * mean["upper"]]
    if best is not None:
        upper_candidates.append(best["cost_upper_bound"])
    if inverse_upper is not None:
        upper_candidates.append(inverse_upper)
    cost_interval = [max(0.0, -math.log(inverse["upper"])), min(upper_candidates)]
    return {"ambient_dimension": dimension + 1, "side": side, "pairs": n,
            "seed": raw["seed"], "method_failure_budget": method_delta,
            "mean_clusters": mean,
            "mean_clusters_div_area": {k: mean[k] / area for k in ["estimate", "lower", "upper"]},
            "inverse_cluster_moment": inverse,
            "weak_ordering_cost_plugin_estimate": -math.log(inverse["estimate"]) if inverse["estimate"] > 0 else None,
            "weak_ordering_cost_interval": cost_interval,
            "interval_consistent": cost_interval[0] <= cost_interval[1],
            "weak_ordering_cost_div_area_interval": [x / area for x in cost_interval],
            "inverse_moment_cost_upper_bound": inverse_upper,
            "mean_cluster_cost_upper_bound": math.log(2) * mean["upper"],
            "best_low_cluster_event": best,
            "simultaneous_cdf_radius": cdf_radius, "fragmentation_tail_bounds": tails,
            "total_coupled_updates": raw["total_coupled_updates"],
            "largest_horizon": raw["largest_horizon"], "seconds": raw["seconds"]}


def summarize_ordered(raw, delta):
    side, dimension = raw["side"], raw["base_dimension"]
    histogram = raw["cluster_histogram"]
    if len(histogram) != side**dimension + 1 or sum(histogram) != raw["pairs"]:
        raise ValueError("Malformed ordered-pair batch")
    if any(not isinstance(value, int) or value < 0 for value in histogram):
        raise ValueError("Invalid ordered histogram frequency")
    if sum(raw["volume_histogram"]) != 2 * raw["pairs"]:
        raise ValueError("Incomplete ordered profile batch")
    area = side**(dimension - 1)
    mean = empirical_bernstein(histogram, float, side**dimension, delta)
    return {"ambient_dimension": dimension + 1, "side": side, "pairs": raw["pairs"],
            "seed": raw["seed"], "mean_clusters": mean,
            "mean_clusters_div_area": {k: mean[k] / area for k in ["estimate", "lower", "upper"]},
            "weak_ordering_cost_lower_bound": mean["lower"] * math.log(2),
            "weak_ordering_cost_div_area_lower_bound": mean["lower"] * math.log(2) / area,
            "note": "No upper entropy estimate from this ensemble; exponential moments can have rare-tail bias",
            "total_coupled_updates": raw["total_coupled_updates"],
            "largest_horizon": raw["largest_horizon"], "seconds": raw["seconds"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sides", nargs="+", type=int, default=[2, 3, 4, 6, 8])
    parser.add_argument("--pairs", type=int, default=2000)
    parser.add_argument("--base-dimension", type=int, choices=[1, 2, 3], default=3)
    parser.add_argument("--seed", type=int, default=20260906)
    parser.add_argument("--failure-probability", type=float, default=0.01)
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--include-raw", action="store_true")
    parser.add_argument("--ensemble", choices=["independent", "ordered"], default="independent")
    args = parser.parse_args()
    if (not 2 <= args.pairs <= 1000000 or any(not 1 <= m <= 12 for m in args.sides)
            or len(set(args.sides)) != len(args.sides) or not 0 < args.failure_probability < 1
            or not 0 <= args.seed < 2**64 - 13):
        parser.error("Invalid size, duplicated side, confidence budget, or seed")
    source = Path(__file__).with_name("cluster_cftp.cpp")
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    results, raw_batches = [], []
    with tempfile.TemporaryDirectory(prefix="cag-cluster-cftp-") as directory:
        executable = args.binary.resolve() if args.binary else Path(directory) / "cluster_cftp"
        if not args.binary:
            subprocess.run(["c++", "-std=c++17", "-O3", "-Wall", "-Wextra", "-pedantic",
                            str(source), "-o", str(executable)], check=True)
        for side in args.sides:
            command = [str(executable), str(args.base_dimension), str(side), str(args.pairs), str(args.seed + side)]
            if args.ensemble == "ordered":
                command.append("--ordered")
            completed = subprocess.run(command,
                                       check=True, stdout=subprocess.PIPE, text=True)
            raw = json.loads(completed.stdout)
            if args.ensemble == "independent":
                results.append(summarize(raw, args.failure_probability / (3 * len(args.sides))))
            else:
                results.append(summarize_ordered(raw, args.failure_probability / len(args.sides)))
            raw_batches.append(raw)
    report = {"kind": "fixed-size CFTP statistical experiment; not a Lean numerical certificate",
              "coverage_scope": "simultaneous across listed sides and methods, under ideal iid randomness",
              "family_failure_probability": args.failure_probability,
              "ensemble": args.ensemble,
              "random_generator": "C++ mt19937_64; theoretical coverage is not a PRNG guarantee",
              "sampler_source_sha256": source_hash,
              "binary_provenance": "caller-supplied, source correspondence not verified" if args.binary
                                   else "compiled from the hashed source in this invocation",
              "results": results}
    if args.include_raw:
        report["raw_batches"] = raw_batches
    print(json.dumps(report, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
