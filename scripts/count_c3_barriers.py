#!/usr/bin/env python3
"""Exact transfer-matrix experiment for the c3 barrier lower bound.

For an m x m boxed plane partition, a row is a non-increasing tuple with
entries in {0, ..., m}.  Consecutive rows are also ordered componentwise.
This script builds that one-row transfer matrix and exactly counts

    Below(b) = {h : h(i,j) <= b(i,j)},
    Above(b) = {h : h(i,j) >  b(i,j)}.

The candidate barriers come from the exact finite-volume one-point means and
medians.  We also optimize among self-dual barriers

    b(i,j) + b(m-1-i,m-1-j) = m-1.

For such a barrier, boxed complementation followed by a 180-degree rotation
is an explicit bijection Above(b) ~= Below(b), so the product lower bound is
Below(b)^2.

Through m=7, counts use signed 64-bit sparse matrix arithmetic.  At m=8 the
script uses three modular transfers and Chinese remaindering; their product
exceeds 8*PP(8,8,8), so counts and one-point moments remain exact.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement
from pathlib import Path

import numpy as np
import scipy.sparse as sp


KNOWN_Q = {
    1: 1,
    2: 20,
    3: 8790,
    4: 89613429,
    5: 21493411201893,
    6: 121692074796863105211,
}

INT64_MAX = np.iinfo(np.int64).max
CRT_PRIMES = (1_000_000_007, 1_000_000_009, 998_244_353)


def chinese_remainder(residues: list[int], moduli: tuple[int, ...] = CRT_PRIMES) -> int:
    """The least nonnegative simultaneous residue for pairwise-coprime moduli."""
    value = 0
    product = 1
    for residue, modulus in zip(residues, moduli):
        correction = ((residue - value) * pow(product, -1, modulus)) % modulus
        value += product * correction
        product *= modulus
    return value


def macmahon(m: int) -> int:
    """Return PP(m,m,m) from the exact MacMahon product."""
    ans = Fraction(1)
    for i in range(1, m + 1):
        for j in range(1, m + 1):
            for k in range(1, m + 1):
                ans *= Fraction(i + j + k - 1, i + j + k - 2)
    assert ans.denominator == 1
    return ans.numerator


def row_states(m: int) -> np.ndarray:
    """All non-increasing length-m rows in {0, ..., m}."""
    rows = [tuple(reversed(c)) for c in combinations_with_replacement(range(m + 1), m)]
    return np.asarray(rows, dtype=np.int16)


def transfer_matrix(states: np.ndarray, chunk: int = 256) -> sp.csr_matrix:
    """A[p,q] = 1 exactly when row p can sit immediately above row q."""
    nstates = states.shape[0]
    source_parts: list[np.ndarray] = []
    target_parts: list[np.ndarray] = []
    for start in range(0, nstates, chunk):
        stop = min(start + chunk, nstates)
        comparable = (states[start:stop, None, :] >= states[None, :, :]).all(axis=2)
        local_source, target = np.nonzero(comparable)
        source_parts.append((local_source + start).astype(np.int32))
        target_parts.append(target.astype(np.int32))
    source = np.concatenate(source_parts)
    target = np.concatenate(target_parts)
    data = np.ones(source.size, dtype=np.int8)
    return sp.csr_matrix((data, (source, target)), shape=(nstates, nstates))


@dataclass
class PlanePartitionTM:
    m: int
    states: np.ndarray
    transfer: sp.csr_matrix

    @classmethod
    def build(cls, m: int) -> "PlanePartitionTM":
        states = row_states(m)
        return cls(m=m, states=states, transfer=transfer_matrix(states))

    def unrestricted_messages(
        self, modulus: int | None = None
    ) -> tuple[list[np.ndarray], list[np.ndarray], int]:
        """Exact forward/backward messages for the uniform boxed model."""
        ones = np.ones(self.states.shape[0], dtype=np.int64)

        forward = [ones]
        for _ in range(1, self.m):
            message = self.transfer.T @ forward[-1]
            if modulus is not None:
                message %= modulus
            forward.append(message)

        backward: list[np.ndarray] = [ones] * self.m
        backward[-1] = ones
        for i in range(self.m - 2, -1, -1):
            message = self.transfer @ backward[i + 1]
            if modulus is not None:
                message %= modulus
            backward[i] = message

        total = sum(int(x) for x in forward[-1])
        if modulus is not None:
            total %= modulus
        for i in range(self.m):
            marginal_total = sum(int(x) * int(y) for x, y in zip(forward[i], backward[i]))
            if modulus is not None:
                marginal_total %= modulus
            assert marginal_total == total
        return forward, backward, total

    def count(self, barrier: np.ndarray, side: str, modulus: int | None = None) -> int:
        """Count profiles below or strictly above a barrier."""
        if barrier.shape != (self.m, self.m):
            raise ValueError(f"barrier must have shape {(self.m, self.m)}")
        if side == "below":
            allowed = (self.states[None, :, :] <= barrier[:, None, :]).all(axis=2)
        elif side == "above":
            allowed = (self.states[None, :, :] > barrier[:, None, :]).all(axis=2)
        else:
            raise ValueError("side must be 'below' or 'above'")

        values = allowed[0].astype(np.int64)
        for i in range(1, self.m):
            values = self.transfer.T @ values
            if modulus is not None:
                values %= modulus
            values *= allowed[i]
        answer = sum(int(x) for x in values)
        return answer % modulus if modulus is not None else answer


def exact_mean_and_median_barriers(
    tm: PlanePartitionTM,
    forward: list[np.ndarray],
    backward: list[np.ndarray],
    total: int,
) -> tuple[np.ndarray, np.ndarray, list[list[Fraction]]]:
    """Return floor(mean), lower-median, and exact rational one-point means."""
    m = tm.m
    mean_floor = np.zeros((m, m), dtype=np.int16)
    lower_median = np.zeros((m, m), dtype=np.int16)
    exact_means: list[list[Fraction]] = [[Fraction(0) for _ in range(m)] for _ in range(m)]

    median_target = (total + 1) // 2
    for i in range(m):
        weights = [int(x) * int(y) for x, y in zip(forward[i], backward[i])]
        for j in range(m):
            by_height = [0] * (m + 1)
            numerator = 0
            for state, weight in zip(tm.states, weights):
                height = int(state[j])
                by_height[height] += weight
                numerator += height * weight
            mean = Fraction(numerator, total)
            exact_means[i][j] = mean
            mean_floor[i, j] = mean.numerator // mean.denominator

            cumulative = 0
            for height, count in enumerate(by_height):
                cumulative += count
                if cumulative >= median_target:
                    lower_median[i, j] = height
                    break
    return mean_floor, lower_median, exact_means


def exact_mean_and_median_barriers_crt(
    tm: PlanePartitionTM,
    messages: list[tuple[list[np.ndarray], list[np.ndarray]]],
    total: int,
) -> tuple[np.ndarray, np.ndarray, list[list[Fraction]]]:
    """Exact one-point statistics reconstructed from modular messages."""
    m = tm.m
    mean_floor = np.zeros((m, m), dtype=np.int16)
    lower_median = np.zeros((m, m), dtype=np.int16)
    exact_means: list[list[Fraction]] = [[Fraction(0) for _ in range(m)] for _ in range(m)]
    median_target = (total + 1) // 2

    for i in range(m):
        for j in range(m):
            count_residues = [[0] * (m + 1) for _ in CRT_PRIMES]
            moment_residues = [0] * len(CRT_PRIMES)
            for prime_index, (prime, (forward, backward)) in enumerate(zip(CRT_PRIMES, messages)):
                counts = count_residues[prime_index]
                moment = 0
                for state, prefix, suffix in zip(tm.states, forward[i], backward[i]):
                    height = int(state[j])
                    weight = (int(prefix) * int(suffix)) % prime
                    counts[height] = (counts[height] + weight) % prime
                    moment = (moment + height * weight) % prime
                moment_residues[prime_index] = moment

            by_height = [
                chinese_remainder([count_residues[p][height] for p in range(len(CRT_PRIMES))])
                for height in range(m + 1)
            ]
            assert sum(by_height) == total
            numerator = chinese_remainder(moment_residues)
            assert numerator <= m * total
            mean = Fraction(numerator, total)
            exact_means[i][j] = mean
            mean_floor[i, j] = mean.numerator // mean.denominator

            cumulative = 0
            for height, count in enumerate(by_height):
                cumulative += count
                if cumulative >= median_target:
                    lower_median[i, j] = height
                    break
    return mean_floor, lower_median, exact_means


def exact_constrained_count(tm: PlanePartitionTM, barrier: np.ndarray, side: str, pp: int) -> int:
    if pp <= INT64_MAX:
        return tm.count(barrier, side)
    residues = [tm.count(barrier, side, prime) for prime in CRT_PRIMES]
    answer = chinese_remainder(residues)
    assert answer <= pp
    return answer


def make_self_dual(seed: np.ndarray) -> np.ndarray:
    """Project a seed to b(x) + b(rot(x)) = m-1 using one representative."""
    m = seed.shape[0]
    barrier = np.zeros_like(seed)
    for flat in range(m * m):
        i, j = divmod(flat, m)
        ri, rj = m - 1 - i, m - 1 - j
        rflat = ri * m + rj
        if flat < rflat:
            value = min(m - 1, max(0, int(seed[i, j])))
            barrier[i, j] = value
            barrier[ri, rj] = m - 1 - value
        elif flat == rflat:
            if m % 2 == 0:
                raise AssertionError("an even square cannot have a rotation-fixed cell")
            barrier[i, j] = (m - 1) // 2
    assert is_self_dual(barrier)
    return barrier


def central_plane_barrier(m: int) -> np.ndarray:
    """Closed-form discrete barrier nearest 3(m-1)/2 - i - j.

    For odd m the displayed affine function is integer-valued and the result
    depends only on i+j.  For even m it is half-integral; ``make_self_dual``
    makes a deterministic complementary rounding choice on rotation pairs.
    """
    seed = np.zeros((m, m), dtype=np.int16)
    for i in range(m):
        for j in range(m):
            seed[i, j] = min(m - 1, max(0, (3 * (m - 1) - 2 * (i + j)) // 2))
    return make_self_dual(seed)


def is_self_dual(barrier: np.ndarray) -> bool:
    m = barrier.shape[0]
    return bool(np.all(barrier + np.rot90(barrier, 2) == m - 1))


def is_antitone(barrier: np.ndarray) -> bool:
    return bool(np.all(barrier[:-1, :] >= barrier[1:, :]) and np.all(barrier[:, :-1] >= barrier[:, 1:]))


def optimize_self_dual(
    tm: PlanePartitionTM,
    seed: np.ndarray,
    sweeps: int,
) -> tuple[np.ndarray, int, int]:
    """Coordinate-ascent Below(b) over self-dual barriers.

    There are floor(m^2/2) independent coordinates.  A full coordinate pass
    tries every threshold 0, ..., m-1 at each coordinate and its rotated mate.
    Ties prefer the current value, which keeps the result deterministic.
    """
    m = tm.m
    barrier = make_self_dual(seed)
    score = tm.count(barrier, "below")
    evaluations = 1
    pairs = []
    for flat in range(m * m):
        i, j = divmod(flat, m)
        ri, rj = m - 1 - i, m - 1 - j
        if flat < ri * m + rj:
            pairs.append((i, j, ri, rj))

    for _ in range(sweeps):
        start_score = score
        for i, j, ri, rj in pairs:
            current = int(barrier[i, j])
            best_value = current
            best_score = score
            for value in range(m):
                if value == current:
                    continue
                barrier[i, j] = value
                barrier[ri, rj] = m - 1 - value
                candidate = tm.count(barrier, "below")
                evaluations += 1
                if candidate > best_score:
                    best_value = value
                    best_score = candidate
            barrier[i, j] = best_value
            barrier[ri, rj] = m - 1 - best_value
            score = best_score
        if score == start_score:
            break

    assert is_self_dual(barrier)
    assert tm.count(barrier, "above") == score
    return barrier, score, evaluations


def barrier_result(tm: PlanePartitionTM, name: str, barrier: np.ndarray, pp: int) -> dict:
    below = exact_constrained_count(tm, barrier, "below", pp)
    above = exact_constrained_count(tm, barrier, "above", pp)
    lower_bound = below * above
    return {
        "name": name,
        "barrier": barrier.astype(int).tolist(),
        "below": below,
        "above": above,
        "lower_bound": lower_bound,
        "below_probability": below / pp,
        "above_probability": above / pp,
        "entropy_deficit_below": math.log(pp / below) if below else math.inf,
        "entropy_deficit_above": math.log(pp / above) if above else math.inf,
        "deficit_below_per_m": math.log(pp / below) / tm.m if below else math.inf,
        "deficit_above_per_m": math.log(pp / above) / tm.m if above else math.inf,
        "entropy_deficit_product": math.log((pp * pp) / lower_bound) if lower_bound else math.inf,
        "lower_bound_log_density": (
            math.log(lower_bound) / (tm.m * tm.m) if lower_bound else -math.inf
        ),
        "self_dual": is_self_dual(barrier),
        "antitone": is_antitone(barrier),
    }


def format_matrix(matrix: list[list[int]]) -> str:
    return "/".join(",".join(str(x) for x in row) for row in matrix)


def run_one(m: int, sweeps: int, optimize: bool) -> dict:
    started = time.time()
    pp_formula = macmahon(m)
    tm = PlanePartitionTM.build(m)
    if pp_formula <= INT64_MAX:
        forward, backward, pp_transfer = tm.unrestricted_messages()
        assert pp_transfer == pp_formula
        mean_floor, lower_median, exact_means = exact_mean_and_median_barriers(
            tm, forward, backward, pp_transfer
        )
    else:
        if math.prod(CRT_PRIMES) <= m * pp_formula:
            raise OverflowError("CRT modulus product is too small for exact one-point moments")
        modular_messages = []
        for prime in CRT_PRIMES:
            forward, backward, pp_residue = tm.unrestricted_messages(prime)
            assert pp_residue == pp_formula % prime
            modular_messages.append((forward, backward))
        pp_transfer = pp_formula
        mean_floor, lower_median, exact_means = exact_mean_and_median_barriers_crt(
            tm, modular_messages, pp_transfer
        )
    mean_symmetric = make_self_dual(mean_floor)
    median_symmetric = make_self_dual(lower_median)
    central_plane = central_plane_barrier(m)

    candidates: list[tuple[str, np.ndarray]] = [
        ("mean-floor", mean_floor),
        ("lower-median", lower_median),
        ("symmetric-mean", mean_symmetric),
        ("symmetric-median", median_symmetric),
        ("central-plane", central_plane),
    ]

    optimization: dict | None = None
    if optimize and pp_formula <= INT64_MAX:
        trials = []
        for seed_name, seed in (
            ("symmetric-mean", mean_symmetric),
            ("symmetric-median", median_symmetric),
            ("central-plane", central_plane),
        ):
            optimized_trial, score, evaluations = optimize_self_dual(tm, seed, sweeps)
            trials.append((score, seed_name, optimized_trial, evaluations))
        optimized_score, optimized_seed, optimized, _ = max(trials, key=lambda x: x[0])
        candidates.append(("optimized-symmetric", optimized))
        optimization = {
            "seed": optimized_seed,
            "sweeps_requested": sweeps,
            "trials": [
                {"seed": seed_name, "score": score, "evaluations": evaluations}
                for score, seed_name, _, evaluations in trials
            ],
            "score": optimized_score,
        }

    results = [barrier_result(tm, name, barrier, pp_transfer) for name, barrier in candidates]
    q = KNOWN_Q.get(m)
    for result in results:
        result["fraction_of_Q"] = result["lower_bound"] / q if q is not None else None
        result["gap_to_Q"] = (
            math.log(q / result["lower_bound"])
            if q is not None and result["lower_bound"]
            else math.inf if q is not None
            else None
        )

    return {
        "m": m,
        "row_states": int(tm.states.shape[0]),
        "transfer_edges": int(tm.transfer.nnz),
        "plane_partitions": pp_transfer,
        "Q": q,
        "Q_log_density": math.log(q) / (m * m) if q is not None else None,
        "PP_log_density": math.log(pp_transfer) / (m * m),
        "exact_mean_numerators": [
            [[x.numerator, x.denominator] for x in row] for row in exact_means
        ],
        "optimization": optimization,
        "barriers": results,
        "seconds": time.time() - started,
    }


def print_result(run: dict) -> None:
    m = run["m"]
    print(
        f"m={m} states={run['row_states']} edges={run['transfer_edges']} "
        f"PP={run['plane_partitions']} Q={run['Q']} ({run['seconds']:.3f}s)"
    )
    print(
        "  barrier                 below          above   "
        "D-/m     D+/m   logLB/m^2   LB/Q      flags"
    )
    for result in run["barriers"]:
        flags = []
        if result["self_dual"]:
            flags.append("self-dual")
        if result["antitone"]:
            flags.append("antitone")
        ratio = result["fraction_of_Q"]
        ratio_text = f"{ratio:.3e}" if ratio is not None else "n/a"
        print(
            f"  {result['name']:<19} {result['below']:>13} {result['above']:>13} "
            f"{result['deficit_below_per_m']:>7.4f} "
            f"{result['deficit_above_per_m']:>7.4f} "
            f"{result['lower_bound_log_density']:>11.6f} "
            f"{ratio_text:>9}  {','.join(flags) or '-'}"
        )
        print(f"    b={format_matrix(result['barrier'])}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-m", type=int, default=6)
    parser.add_argument("--sweeps", type=int, default=3)
    parser.add_argument("--no-optimize", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_m <= 8:
        parser.error("this exact implementation supports 1 <= --max-m <= 8")
    if args.sweeps < 0:
        parser.error("--sweeps must be nonnegative")

    runs = []
    for m in range(1, args.max_m + 1):
        run = run_one(m, args.sweeps, not args.no_optimize)
        runs.append(run)
        print_result(run)
    if args.json_out is not None:
        args.json_out.write_text(json.dumps(runs, indent=2) + "\n")


if __name__ == "__main__":
    main()
