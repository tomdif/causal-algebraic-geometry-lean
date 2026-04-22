"""
Attempt to compute Q(6) = |J(2*5*6*6)| via Berman-Koehler, using
numpy-vectorized containment for speed.

Expected: |S(2,5,6)| = PP(2,5,6), on the order of tens of thousands.
Goal: finish adjacency + 6 iterations in reasonable time.
"""
import math
import sys
import time

import numpy as np


def enumerate_ideals(a, b, c):
    ideals = []
    def rec(profile, idx):
        if idx == a * b:
            ideals.append(tuple(profile))
            return
        i, j = divmod(idx, b)
        max_h = c
        if i > 0:
            max_h = min(max_h, profile[(i - 1) * b + j])
        if j > 0:
            max_h = min(max_h, profile[i * b + (j - 1)])
        for h in range(max_h + 1):
            profile.append(h)
            rec(profile, idx + 1)
            profile.pop()
    rec([], 0)
    return ideals


def main():
    a, b, c = 2, 5, 6
    n_target = 6

    print(f"Computing |J({a}*{b}*{c}*n)| for n up to {n_target}", file=sys.stderr)
    t0 = time.time()
    ideals_tuples = enumerate_ideals(a, b, c)
    N = len(ideals_tuples)
    print(f"  |S({a}*{b}*{c})| = {N}  ({time.time()-t0:.1f}s)", file=sys.stderr)

    # Convert to numpy array: N x (a*b) int8
    ideals = np.array(ideals_tuples, dtype=np.int8)
    print(f"  ideals array: shape {ideals.shape}, dtype {ideals.dtype}",
          file=sys.stderr)

    # Build supersets: for each i, indices j such that ideals[j] >= ideals[i] elementwise
    # Using vectorized comparison: for each row i, compare against all rows.
    # supersets_mask[i, j] = 1 if ideals[j] >= ideals[i] elementwise

    # Dense boolean matrix: N x N, roughly N bytes per row. For N=60K that's 3.6 GB. Too big.
    # Instead, iterate i from 0 to N-1, compute row mask on the fly.

    t1 = time.time()
    # Use Python ints for values (will get very large)
    # f is length N, supersets[i] is list of indices.
    # Iterate by row. For each i, supersets[i] = indices j where ideals[j] >= ideals[i] all coords.

    # To save memory during iteration, build supersets ONCE and store as list-of-arrays.
    supersets = [None] * N
    for i in range(N):
        # (ideals >= ideals[i]) elementwise, then all(axis=1)
        mask = np.all(ideals >= ideals[i], axis=1)
        supersets[i] = np.where(mask)[0]
        if i % 5000 == 0:
            print(f"    row {i}/{N}: {len(supersets[i])} supersets "
                  f"  ({time.time()-t1:.1f}s)", file=sys.stderr)
    total_edges = sum(len(s) for s in supersets)
    print(f"  supersets built: {total_edges} edges  "
          f"({time.time()-t1:.1f}s)", file=sys.stderr)

    # Iterate
    # f[i] = 1; f_{k+1}[i] = sum_{j in supersets[i]} f[j]; total_n = sum(f_n)
    f = [1] * N  # Python ints (big when needed)
    values = [1, N]  # n = 0, 1
    for k in range(2, n_target + 1):
        t2 = time.time()
        f_new = [0] * N
        for i in range(N):
            s_big = 0
            for j in supersets[i]:
                s_big += f[j]
            f_new[i] = s_big
        f = f_new
        values.append(sum(f))
        print(f"  step n={k}: total={values[-1]}  ({time.time()-t2:.1f}s)",
              file=sys.stderr)

    print(f"\n|J({a}*{b}*{c}*n)| for n = 0..{n_target}:")
    for n in range(len(values)):
        print(f"  n={n}: {values[n]}")
    q6 = values[6]
    print(f"\nQ(6) = |J({a}*{b}*{c}*6)| = {q6}")

    # ln(Q(6)) / 36
    ln_q6 = math.log(q6)
    print(f"  log Q(6) = {ln_q6:.6f}")
    print(f"  log Q(6) / 36 = {ln_q6/36:.6f}")
    print(f"  2 L_3 = {2*(4.5*math.log(3) - 6*math.log(2)):.6f}")


if __name__ == "__main__":
    main()
