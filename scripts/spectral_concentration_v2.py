#!/usr/bin/env python3
"""
spectral_concentration_v2.py — R-sector decomposition of the COMPARABILITY kernel

The d=2 chamber = {(lo, hi) : 0 <= lo < hi <= m-1} (intervals on [m]).
The comparability kernel: K(P,Q) = 1 iff P <= Q or Q <= P componentwise.
  i.e., (lo₁ ≤ lo₂ and hi₁ ≤ hi₂) or (lo₂ ≤ lo₁ and hi₂ ≤ hi₁).

The simplex reflection: R(lo, hi) = (m-1-hi, m-1-lo).
[R, K] = 0 since R preserves comparability.

We decompose into R-even and R-odd sectors.
"""

import numpy as np
from scipy.linalg import eigh

def analyze_comparability(m):
    """Compute R-sector eigenvalues of the comparability kernel on the chamber."""
    # Enumerate chamber states: (lo, hi) with 0 <= lo < hi <= m-1
    states = [(lo, hi) for lo in range(m) for hi in range(lo+1, m)]
    n = len(states)
    state_idx = {s: i for i, s in enumerate(states)}

    # Build comparability kernel (symmetric)
    K = np.zeros((n, n))
    for a in range(n):
        lo1, hi1 = states[a]
        for b in range(a, n):
            lo2, hi2 = states[b]
            if (lo1 <= lo2 and hi1 <= hi2) or (lo2 <= lo1 and hi2 <= hi1):
                K[a, b] = 1.0
                K[b, a] = 1.0

    # Build reflection matrix R: (lo, hi) -> (m-1-hi, m-1-lo)
    R = np.zeros((n, n))
    for i, (lo, hi) in enumerate(states):
        reflected = (m - 1 - hi, m - 1 - lo)
        j = state_idx[reflected]
        R[i, j] = 1.0

    # Verify symmetry and commutation
    assert np.max(np.abs(K - K.T)) < 1e-12, "K not symmetric"
    assert np.max(np.abs(R @ K - K @ R)) < 1e-10, "[R, K] != 0"
    assert np.max(np.abs(R @ R - np.eye(n))) < 1e-12, "R² != I"

    # Project onto R-sectors
    P_even = (np.eye(n) + R) / 2
    P_odd = (np.eye(n) - R) / 2

    K_even = P_even @ K @ P_even
    K_odd = P_odd @ K @ P_odd

    # Eigenvalues (K is symmetric, projections preserve symmetry)
    evals_even = np.sort(eigh(K_even, eigvals_only=True))[::-1]
    evals_odd = np.sort(eigh(K_odd, eigvals_only=True))[::-1]

    # Filter near-zero eigenvalues
    tol = 1e-8
    ee = evals_even[np.abs(evals_even) > tol]
    eo = evals_odd[np.abs(evals_odd) > tol]

    # Traces from the formula
    tr_K = np.trace(K)  # = n (diagonal all 1s since every state is comparable with itself)
    tr_RK = np.trace(R @ K)
    tr_even = (tr_K + tr_RK) / 2
    tr_odd = (tr_K - tr_RK) / 2

    # Verify: sum of eigenvalues = trace
    sum_ee = np.sum(ee)
    sum_eo = np.sum(eo)

    le = ee[0] if len(ee) > 0 else 0
    lo_val = eo[0] if len(eo) > 0 else 0
    le2 = ee[1] if len(ee) > 1 else 0
    lo2 = eo[1] if len(eo) > 1 else 0

    fe = le / tr_even if tr_even > 0 else 0
    fo = lo_val / tr_odd if tr_odd > 0 else 0

    return {
        'm': m, 'n': n,
        'tr_K': tr_K, 'tr_RK': tr_RK,
        'tr_even': tr_even, 'tr_odd': tr_odd,
        'sum_ee': sum_ee, 'sum_eo': sum_eo,
        'tr_ratio': tr_even / tr_odd if tr_odd > 0 else float('inf'),
        'le': le, 'lo': lo_val,
        'le2': le2, 'lo2': lo2,
        'le_lo': le / lo_val if lo_val > 0 else float('inf'),
        'fe': fe, 'fo': fo,
        'fe_fo': fe / fo if fo > 0 else float('inf'),
        'residual': (le / lo_val) / (tr_even / tr_odd) - 1 if tr_odd > 0 and lo_val > 0 else float('inf'),
        'n_even': len(ee), 'n_odd': len(eo),
        'gap_even': le / le2 if le2 > tol else float('inf'),
        'gap_odd': lo_val / lo2 if lo2 > tol else float('inf'),
        'evals_even': ee,
        'evals_odd': eo,
    }

def main():
    print("=" * 95)
    print("SPECTRAL CONCENTRATION: Comparability kernel on d=2 chamber, R-sector decomposition")
    print("=" * 95)

    print(f"\n{'m':>3} {'n':>5} {'tr_e/o':>8} {'le/lo':>8} {'fe':>8} {'fo':>8} "
          f"{'fe/fo':>8} {'resid':>10} {'gap_e':>7} {'gap_o':>7} {'n_e':>4} {'n_o':>4}")
    print("-" * 95)

    results = []
    for m in range(4, 50):
        r = analyze_comparability(m)
        results.append(r)
        print(f"{m:3d} {r['n']:5d} {r['tr_ratio']:8.4f} {r['le_lo']:8.4f} "
              f"{r['fe']:8.5f} {r['fo']:8.5f} {r['fe_fo']:8.5f} "
              f"{r['residual']:10.6f} {r['gap_even']:7.3f} {r['gap_odd']:7.3f} "
              f"{r['n_even']:4d} {r['n_odd']:4d}")

    # Detailed analysis
    print("\n" + "=" * 95)
    print("CONVERGENCE: m*|residual| for even and odd m")
    print("=" * 95)

    for parity_label, parity_val in [("Even m", 0), ("Odd m", 1)]:
        subset = [r for r in results if r['m'] % 2 == parity_val and r['m'] >= 10]
        print(f"\n{parity_label}:")
        print(f"  {'m':>3} {'fe/fo':>10} {'residual':>12} {'m*|resid|':>10} {'m²*|resid|':>12}")
        for r in subset:
            mr = r['m'] * abs(r['residual'])
            m2r = r['m']**2 * abs(r['residual'])
            print(f"  {r['m']:3d} {r['fe_fo']:10.6f} {r['residual']:12.8f} {mr:10.5f} {m2r:12.4f}")

    # Spectrum at largest m
    r = results[-1]
    m = r['m']
    print(f"\n{'='*95}")
    print(f"DETAILED SPECTRUM at m={m}")
    print(f"{'='*95}")

    print(f"\nEven sector ({r['n_even']} eigenvalues, tr={r['tr_even']:.2f}, sum={r['sum_ee']:.2f}):")
    for i, ev in enumerate(r['evals_even'][:10]):
        print(f"  λ_{i+1}^even = {ev:12.4f}  ({ev/r['tr_even']*100:6.2f}% of tr)")
    print(f"  ... remaining {r['n_even']-10} eigenvalues sum to {r['tr_even'] - sum(r['evals_even'][:10]):.4f}")

    print(f"\nOdd sector ({r['n_odd']} eigenvalues, tr={r['tr_odd']:.2f}, sum={r['sum_eo']:.2f}):")
    for i, ev in enumerate(r['evals_odd'][:10]):
        print(f"  λ_{i+1}^odd  = {ev:12.4f}  ({ev/r['tr_odd']*100:6.2f}% of tr)")
    print(f"  ... remaining {r['n_odd']-10} eigenvalues sum to {r['tr_odd'] - sum(r['evals_odd'][:10]):.4f}")

    # Check if eigenvalues match between sectors
    print(f"\nEigenvalue matching between sectors:")
    n_match = min(8, len(r['evals_even'])-1, len(r['evals_odd']))
    for i in range(n_match):
        e = r['evals_even'][i+1]  # skip top even eigenvalue
        o = r['evals_odd'][i]
        print(f"  λ_{i+2}^even = {e:12.6f}   λ_{i+1}^odd = {o:12.6f}   diff = {e-o:12.8f}")

    # Concentration fraction analysis
    print(f"\n{'='*95}")
    print(f"CONCENTRATION FRACTION CONVERGENCE")
    print(f"{'='*95}")
    ms = [r['m'] for r in results if r['m'] >= 10]
    fes = [r['fe'] for r in results if r['m'] >= 10]
    fos = [r['fo'] for r in results if r['m'] >= 10]

    # Extrapolate fe and fo to m -> infinity
    if len(ms) >= 10:
        from numpy.polynomial import polynomial as P
        inv_m = [1.0/m for m in ms]

        # Fit fe(1/m) = a + b/m + c/m²
        coeffs_e = np.polyfit(inv_m, fes, 2)
        coeffs_o = np.polyfit(inv_m, fos, 2)

        print(f"\nExtrapolation (quadratic in 1/m):")
        print(f"  f_even(∞) = {coeffs_e[2]:.6f}")
        print(f"  f_odd(∞)  = {coeffs_o[2]:.6f}")
        print(f"  f_even/f_odd(∞) = {coeffs_e[2]/coeffs_o[2]:.6f}")

        print(f"\n  f_even = {coeffs_e[2]:.6f} + ({coeffs_e[1]:.4f})/m + ({coeffs_e[0]:.4f})/m²")
        print(f"  f_odd  = {coeffs_o[2]:.6f} + ({coeffs_o[1]:.4f})/m + ({coeffs_o[0]:.4f})/m²")

if __name__ == "__main__":
    main()
