"""
Compute |J(2*(m-1)*m*n)| = the Q(m) family of 4D poset counts.

For each m, Q(m) = |J(2*(m-1)*m*n)| at n = m.

m = 3: base 2*2*3, |S| = 50,  Q(3) = 8,790
m = 4: base 2*3*4, |S| = 490, Q(4) = 89,613,429 (= A056936(4))
m = 5: base 2*4*5, |S| ≈ 5292, Q(5) = 21,493,411,201,893
m = 6: base 2*5*6, |S| ≈ 60K,  Q(6) = unknown

Uses Berman-Koehler iterated transfer matrix: states = order ideals of
the 3D base, transitions = containment I ⊆ I'. For level n, apply the
supersets matrix n times to the all-ones vector, sum.

This cross-verifies the direct Q(m) TM (which uses a different state
space = pairs of non-increasing rows).
"""

import math
import sys
import time
from fractions import Fraction


def enumerate_order_ideals_3d(a, b, c):
    """Order ideals of [a]*[b]*[c], encoded as height-profile tuples."""
    ideals = []
    def rec(profile, idx):
        if idx == a * b:
            prof_tuple = tuple(
                tuple(profile[i * b + j] for j in range(b))
                for i in range(a)
            )
            ideals.append(prof_tuple)
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


def build_supersets(ideals, a, b):
    """For each ideal I (as tuple-of-tuples), list indices of J ⊇ I."""
    N = len(ideals)
    supersets = [[] for _ in range(N)]
    for i in range(N):
        Hi = ideals[i]
        for j in range(N):
            Hj = ideals[j]
            ok = True
            for ii in range(a):
                if not ok:
                    break
                for jj in range(b):
                    if Hj[ii][jj] < Hi[ii][jj]:
                        ok = False
                        break
            if ok:
                supersets[i].append(j)
    return supersets


def compute_J(a, b, c, n_max, log=True):
    """Compute |J(a*b*c*[n])| for n = 0..n_max."""
    t0 = time.time()
    ideals = enumerate_order_ideals_3d(a, b, c)
    N = len(ideals)
    if log:
        print(f"  |S({a}*{b}*{c})| = {N}  ({time.time()-t0:.1f}s to enumerate)",
              file=sys.stderr)
    t1 = time.time()
    supersets = build_supersets(ideals, a, b)
    total_edges = sum(len(s) for s in supersets)
    if log:
        print(f"  supersets built: {total_edges} edges  ({time.time()-t1:.1f}s)",
              file=sys.stderr)
    # |J(a*b*c*[n])| = sum over chains of supersets of length n
    # f_1[I] = 1; f_{k+1}[I] = sum_{J ⊇ I} f_k[J]
    # total_n = sum_I f_n[I]
    values = [1, N]  # n=0, n=1
    f = [1] * N
    for k in range(2, n_max + 1):
        t2 = time.time()
        f_new = [0] * N
        for i in range(N):
            s = 0
            for j in supersets[i]:
                s += f[j]
            f_new[i] = s
        f = f_new
        values.append(sum(f))
        if log:
            print(f"  step n={k}: total={values[-1]}  ({time.time()-t2:.1f}s)",
                  file=sys.stderr)
    return values


def main():
    # m = 4: cross-verify Q(4) = 89,613,429 via |J(2*3*4*4)|
    print("=" * 60)
    print("m = 4: base 2*3*4")
    print("=" * 60)
    values4 = compute_J(2, 3, 4, 5)
    print(f"|J(2*3*4*n)| for n = 0..5:")
    for n in range(len(values4)):
        print(f"  n={n}: {values4[n]}")
    q4 = values4[4]
    q4_expected = 89613429
    print(f"Q(4) via Berman-Koehler: {q4}")
    print(f"Q(4) expected from direct TM: {q4_expected}")
    print(f"Match: {q4 == q4_expected}")
    print()

    # m = 5: cross-verify Q(5) = 21,493,411,201,893 via |J(2*4*5*5)|
    print("=" * 60)
    print("m = 5: base 2*4*5 (this may take a few minutes)")
    print("=" * 60)
    values5 = compute_J(2, 4, 5, 6)
    print(f"|J(2*4*5*n)| for n = 0..6:")
    for n in range(len(values5)):
        print(f"  n={n}: {values5[n]}")
    q5 = values5[5]
    q5_expected = 21493411201893
    print(f"Q(5) via Berman-Koehler: {q5}")
    print(f"Q(5) expected from direct TM: {q5_expected}")
    print(f"Match: {q5 == q5_expected}")
    print()

    # Also output values beyond known Q(m) for future reference
    print("Extra |J(2*4*5*n)| values beyond n=5:")
    for n in range(5, len(values5)):
        print(f"  n={n}: {values5[n]}")


if __name__ == "__main__":
    main()
