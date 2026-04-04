#!/usr/bin/env python3
"""
Transfer-matrix computation of a(m) = |CC([m]^2)| and bounds on rho.

State space: N = (m+1)(m+2)/2 states, parameterized as:
  - F(k) for k=0..m: "not in block, global L_min = k" (k=m means unconstrained)
  - B(L,R) for 0<=L<=R<=m-1: "in block with leftmost col L, constraint row R"

Transitions:
  From F(k):
    - Empty row: F(k) -> F(k)
    - Start box (L_new, R_new): if k < m then R_new < k required
      -> B(L_new, R_new)

  From B(L, R):
    - End row: B(L,R) -> F(L)
    - Extend box (L_new, R_new): need L_new <= L and R_new <= R
      -> B(L_new, R_new)

Results computed up to m=150.
"""

import time
import math
import sys

def compute_a(m, verbose=True):
    t0 = time.time()
    n = m

    def F_idx(k):
        return k

    def B_idx(L, R):
        offset = (n + 1) + L * n - L * (L - 1) // 2
        return offset + (R - L)

    N_F = n + 1
    N_B = n * (n + 1) // 2
    N = N_F + N_B

    # Build adjacency with multiplicities
    adj = [None] * N

    for k in range(N_F):
        targets = {}
        fi = F_idx(k)
        targets[fi] = targets.get(fi, 0) + 1
        if k < n:
            for L_new in range(n):
                for R_new in range(L_new, min(k, n)):
                    bi = B_idx(L_new, R_new)
                    targets[bi] = targets.get(bi, 0) + 1
        else:
            for L_new in range(n):
                for R_new in range(L_new, n):
                    bi = B_idx(L_new, R_new)
                    targets[bi] = targets.get(bi, 0) + 1
        adj[k] = list(targets.items())

    for L in range(n):
        for R in range(L, n):
            si = B_idx(L, R)
            targets = {}
            fi = F_idx(L)
            targets[fi] = targets.get(fi, 0) + 1
            for L_new in range(L + 1):
                for R_new in range(L_new, R + 1):
                    bi = B_idx(L_new, R_new)
                    targets[bi] = targets.get(bi, 0) + 1
            adj[si] = list(targets.items())

    t1 = time.time()

    # Matvec
    vec = [0] * N
    vec[F_idx(n)] = 1

    for row in range(m):
        new_vec = [0] * N
        for i in range(N):
            v = vec[i]
            if v == 0:
                continue
            for j, cnt in adj[i]:
                new_vec[j] += v * cnt
        vec = new_vec

    result = sum(vec)
    t2 = time.time()
    if verbose:
        print(f"m={m}: N={N} states, adj={t1-t0:.1f}s, matvec={t2-t1:.1f}s, total={t2-t0:.1f}s")

    return result


# Exact computed values
EXACT_VALUES = {
    2: 13,
    3: 114,
    4: 1146,
    5: 12578,
    6: 146581,
    7: 1784114,
    8: 22443232,
    9: 289721772,
    10: 3818789778,
    100: 103476014291738868206926819804507561463213504641768118793672647526305378356785520197982990566765883855881487146905256,
    120: 87111454495590752641289094942414717512299742744549051413404171412637970038144454867214681813466658557601727593369276017162215700169396489756,
    150: 74311324399133062480173099267483548134923401460219222685797798265473917702973311934679169613351442677757575266132920218851584282348404186568583203641297216539475105341465246832,
}


if __name__ == "__main__":
    # Quick verification
    for m in [2, 3, 4, 5, 10]:
        a = compute_a(m, verbose=False)
        print(f"a({m}) = {a}")
