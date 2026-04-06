#!/usr/bin/env python3
"""
spectral_concentration_v3.py — The key structural observation

K_F(P,Q) = K(P,Q) - K(P, swap(Q))  on the chamber {(i,j) : i < j}
where K = comparability indicator on [m]^2.

Symmetrize: K_sym = (K_F + K_F^T) / 2.
R-decompose and study eigenvalue structure.

KEY FINDING TO VERIFY: the second even eigenvalue ≈ first odd eigenvalue.
"""

import numpy as np
from scipy.linalg import eigh

def build_KF_sym(m):
    """Build the symmetrized antisymmetrized chamber kernel."""
    states = [(i, j) for i in range(m) for j in range(i+1, m)]
    n = len(states)
    state_idx = {s: i for i, s in enumerate(states)}

    def comparable(x, y):
        return (x[0] <= y[0] and x[1] <= y[1]) or (y[0] <= x[0] and y[1] <= x[1])

    K_F = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            K_F[a, b] = int(comparable(P, Q)) - int(comparable(P, (Q[1], Q[0])))

    K_sym = (K_F + K_F.T) / 2

    R = np.zeros((n, n))
    for i, (lo, hi) in enumerate(states):
        j = state_idx[(m-1-hi, m-1-lo)]
        R[i, j] = 1.0

    return K_sym, R, states, n

def analyze(m):
    K_sym, R, states, n = build_KF_sym(m)

    # Project
    P_e = (np.eye(n) + R) / 2
    P_o = (np.eye(n) - R) / 2

    K_e = P_e @ K_sym @ P_e
    K_o = P_o @ K_sym @ P_o

    ee = np.sort(eigh(K_e, eigvals_only=True))[::-1]
    eo = np.sort(eigh(K_o, eigvals_only=True))[::-1]

    tol = 1e-8
    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]

    tr_K = np.trace(K_sym)
    tr_RK = np.trace(R @ K_sym)
    tr_e = (tr_K + tr_RK) / 2
    tr_o = (tr_K - tr_RK) / 2

    return {
        'm': m, 'n': n,
        'tr_e': tr_e, 'tr_o': tr_o,
        'tr_ratio': tr_e / tr_o if tr_o > 0 else float('inf'),
        'ee': ee_nz, 'eo': eo_nz,
        'le': ee_nz[0], 'lo': eo_nz[0] if len(eo_nz) > 0 else 0,
    }

def main():
    print("SPECTRAL STRUCTURE OF K_F (antisymmetrized, symmetrized)")
    print("=" * 100)

    # Detailed eigenvalue comparison for several m values
    for m in [10, 15, 20, 25, 30, 35, 39]:
        r = analyze(m)
        ee, eo = r['ee'], r['eo']
        le, lo = r['le'], r['lo']
        tr_e, tr_o = r['tr_e'], r['tr_o']

        print(f"\nm = {m}  (n={r['n']}, tr_e={tr_e:.2f}, tr_o={tr_o:.2f}, tr_e/tr_o={r['tr_ratio']:.4f})")
        print(f"  le={le:.4f}, lo={lo:.4f}, le/lo={le/lo:.5f}")
        print(f"  fe={le/tr_e:.6f}, fo={lo/tr_o:.6f}, fe/fo={le/tr_e*tr_o/lo:.6f}")

        # Compare λ_{k+1}^even with λ_k^odd
        n_cmp = min(8, len(ee)-1, len(eo))
        print(f"\n  Eigenvalue matching: λ_(k+1)^even vs λ_k^odd")
        for k in range(n_cmp):
            e_val = ee[k+1]
            o_val = eo[k]
            ratio = e_val / o_val if abs(o_val) > 1e-10 else float('inf')
            print(f"    k={k+1}: even={e_val:12.4f}  odd={o_val:12.4f}  "
                  f"ratio={ratio:.6f}  diff={e_val - o_val:.6f}")

    # Summary table: convergence of key quantities
    print("\n\n" + "=" * 100)
    print("CONVERGENCE TABLE")
    print("=" * 100)
    print(f"{'m':>3} {'tr_e/o':>8} {'le/lo':>8} {'fe':>8} {'fo':>8} {'fe/fo':>8} "
          f"{'λ2e/λ1o':>8} {'Σee[2:]/Σeo':>12}")
    print("-" * 85)

    for m in range(4, 45):
        r = analyze(m)
        ee, eo = r['ee'], r['eo']
        le, lo = r['le'], r['lo']
        tr_e, tr_o = r['tr_e'], r['tr_o']

        fe = le / tr_e if tr_e else 0
        fo = lo / tr_o if tr_o else 0

        # λ₂^even / λ₁^odd ratio
        ratio_2e_1o = ee[1] / eo[0] if len(ee) > 1 and len(eo) > 0 and abs(eo[0]) > 1e-10 else 0

        # Sum of even tail vs sum of odd
        sum_even_tail = sum(ee[1:]) if len(ee) > 1 else 0
        sum_odd = sum(eo)
        tail_ratio = sum_even_tail / sum_odd if abs(sum_odd) > 1e-10 else float('inf')

        ffo = fe / fo if fo > 0 else float('inf')

        print(f"{m:3d} {r['tr_ratio']:8.4f} {le/lo if lo else 0:8.4f} "
              f"{fe:8.5f} {fo:8.5f} {ffo:8.5f} "
              f"{ratio_2e_1o:8.5f} {tail_ratio:12.6f}")

    # The KEY relationship
    print("\n\n" + "=" * 100)
    print("THE KEY STRUCTURAL INSIGHT")
    print("=" * 100)
    r = analyze(39)
    ee, eo = r['ee'], r['eo']

    print(f"\nAt m=39:")
    print(f"  Even eigenvalues: λ₁^e = {ee[0]:.4f}, then {ee[1]:.4f}, {ee[2]:.4f}, ...")
    print(f"  Odd eigenvalues:  λ₁^o = {eo[0]:.4f}, then {eo[1]:.4f}, {eo[2]:.4f}, ...")
    print(f"\n  λ₂^even / λ₁^odd = {ee[1]/eo[0]:.6f}")
    print(f"  Sum(even[2:]) / Sum(odd) = {sum(ee[1:])/sum(eo):.6f}")

    # If the spectra EXACTLY matched after the top even eigenvalue:
    # tr_e = le + S, tr_o = S where S = shared sum
    # Then fe = le/(le+S), fo = μ₁/S where μ₁ = first shared eigenvalue
    # fe/fo = le·S / (μ₁·(le+S)) = (le/μ₁) · (S/(le+S)) = (le/μ₁) · (1 - fe)
    # And tr_e/tr_o = (le+S)/S = 1 + le/S
    # le/lo = le/μ₁
    # residual = (le/μ₁) / (1 + le/S) - 1 = (le·S - μ₁·(le+S)) / (μ₁·(le+S))
    #          = (le·S - μ₁·le - μ₁·S) / (...) = (le(S-μ₁) - μ₁·S) / (...)
    # This = 0 iff le(S-μ₁) = μ₁·S iff le/μ₁ = S/(S-μ₁) iff le/μ₁ = 1/(1-μ₁/S)

    # In fact: fe/fo = (le/(le+S)) / (μ₁/S) = le·S / (μ₁(le+S))
    # = (le/μ₁) · (S/(le+S)) = (le/μ₁) · (tr_o/tr_e)
    # So fe/fo = (le/lo) · (tr_o/tr_e) ... which is the residual definition!
    # fe/fo = 1 iff le/lo = tr_e/tr_o. That's exactly what we want to prove!

    print(f"\n  EXACT RELATIONSHIP:")
    print(f"  fe/fo = (le/lo) × (tr_o/tr_e) = {(r['le']/r['lo'])*(r['tr_o']/r['tr_e']):.6f}")
    print(f"  This is IDENTICALLY fe/fo by definition. Not a new identity!")

    # So the real question: WHY is the even tail ≈ odd total?
    tail_e = sum(ee[1:])
    total_o = sum(eo)
    print(f"\n  Even tail (sum λ_k^even for k≥2): {tail_e:.4f}")
    print(f"  Odd total (sum λ_k^odd):            {total_o:.4f}")
    print(f"  Ratio: {tail_e/total_o:.6f}")
    print(f"  Difference: {tail_e - total_o:.4f}")

    # If tail_e = total_o exactly, then fe = fo.
    # Proof: tr_e = le + tail_e, tr_o = total_o = tail_e
    # fe = le/tr_e = le/(le+tail_e), fo = lo/total_o = lo/tail_e
    # fe/fo = le·tail_e / (lo·(le+tail_e))

    # For fe = fo: le/(le+tail_e) = lo/tail_e
    # le·tail_e = lo·(le+tail_e) = lo·le + lo·tail_e
    # le·(tail_e - lo) = lo·tail_e
    # Doesn't simplify to tail_e = total_o.

    # Different approach: what if eigenvalues interleave?
    print(f"\n  INTERLEAVING TEST:")
    all_evals = list(zip(ee, ['e']*len(ee))) + list(zip(eo, ['o']*len(eo)))
    all_evals.sort(key=lambda x: -x[0])
    for i, (val, sector) in enumerate(all_evals[:20]):
        print(f"    #{i+1}: {val:12.4f}  ({sector})")

if __name__ == "__main__":
    main()
