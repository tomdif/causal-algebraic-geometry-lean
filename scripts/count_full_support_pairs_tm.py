"""
Transfer-matrix counting of full-support antitone pairs on [m]² → [0, m].

State: pair of non-increasing rows (r_φ, r_ψ) with r_φ(j) < r_ψ(j) for all j,
both in [0, m]^m.

Transition (r_φ, r_ψ) → (r'_φ, r'_ψ): r'_φ ≤ r_φ and r'_ψ ≤ r_ψ pointwise
(and the target is itself a valid state, i.e., r'_φ < r'_ψ pointwise and rows
non-increasing).

Q(m) = 1ᵀ T^{m-1} 1, where T is the adjacency matrix on states.
"""

import math
import sys
from itertools import combinations_with_replacement


def nonincreasing_rows(length, max_val):
    """All non-increasing sequences of `length` with entries in [0, max_val]."""
    rows = []
    for c in combinations_with_replacement(range(max_val + 1), length):
        rows.append(tuple(sorted(c, reverse=True)))
    return rows


def build_states(m):
    """Pairs (r_φ, r_ψ) both non-increasing length m in [0, m], r_φ < r_ψ pointwise."""
    rows = nonincreasing_rows(m, m)
    states = []
    for r_psi in rows:
        for r_phi in rows:
            if all(r_phi[j] < r_psi[j] for j in range(m)):
                states.append((r_phi, r_psi))
    return states


def count_Q_tm(m):
    """Transfer-matrix count of Q(m)."""
    if m == 0:
        return 1
    states = build_states(m)
    n = len(states)
    print(f"  m={m}: {n} transfer-matrix states", flush=True)

    if m == 1:
        return n

    # Adjacency matrix row-stored as list of lists of target indices (sparse).
    idx = {s: i for i, s in enumerate(states)}
    adj_out = [[] for _ in range(n)]
    for i, (r_phi, r_psi) in enumerate(states):
        for j, (r_phi2, r_psi2) in enumerate(states):
            ok = True
            for k in range(m):
                if r_phi2[k] > r_phi[k] or r_psi2[k] > r_psi[k]:
                    ok = False
                    break
            if ok:
                adj_out[i].append(j)

    # Iterate v ← T^T v, starting from all-ones.  After (m-1) iterations, sum of v
    # over all states = 1ᵀ T^{m-1} 1.
    v = [1] * n
    for step in range(m - 1):
        v_new = [0] * n
        for i in range(n):
            vi = v[i]
            if vi == 0:
                continue
            for j in adj_out[i]:
                v_new[j] += vi
        v = v_new
        print(f"    step {step+1}/{m-1}: max(v)={max(v)}, sum(v)={sum(v)}",
              flush=True)
    return sum(v)


def count_PP(m):
    """PP(m,m,m) via MacMahon: ∏_{i,j,k=1..m} (i+j+k-1)/(i+j+k-2)."""
    from fractions import Fraction
    result = Fraction(1)
    for i in range(1, m + 1):
        for j in range(1, m + 1):
            for k in range(1, m + 1):
                result *= Fraction(i + j + k - 1, i + j + k - 2)
    assert result.denominator == 1
    return result.numerator


def main():
    L3 = 4.5 * math.log(3) - 6 * math.log(2)
    print(f"L_3 = (9/2)ln 3 - 6 ln 2 = {L3:.6f}")
    print(f"2 L_3 = {2 * L3:.6f}")
    print()
    header = f"{'m':>3} {'PP(m,m,m)':>14} {'Q(m)':>20} {'lnQ/m²':>9} {'lnPP/m²':>9}"
    print(header)
    print("-" * len(header))

    max_m = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for m in range(1, max_m + 1):
        n_pp = count_PP(m)
        q = count_Q_tm(m)
        lnQ = math.log(q) if q > 0 else 0.0
        lnPP = math.log(n_pp) if n_pp > 0 else 0.0
        print(f"{m:>3} {n_pp:>14} {q:>20} "
              f"{lnQ/m**2:>9.4f} {lnPP/m**2:>9.4f}", flush=True)


if __name__ == "__main__":
    main()
