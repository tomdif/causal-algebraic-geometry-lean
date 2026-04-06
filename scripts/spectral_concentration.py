#!/usr/bin/env python3
"""
spectral_concentration.py — Compute R-sector eigenvalues and concentration fractions

The d=2 chamber kernel K_F on the Weyl chamber C = {(i,j) : 0 <= i < j <= m-1}
is the antisymmetrized comparability kernel:
  K_F(P,Q) = K(P,Q) - K(P, swap(Q))
where K(x,y) = 1 iff x <= y or y <= x componentwise.

The simplex reflection R: (i,j) -> (m-1-j, m-1-i) commutes with K_F.
We decompose into R-even and R-odd sectors and study:
  - tr_even, tr_odd (proved: ratio -> 3)
  - lambda_even, lambda_odd (top eigenvalues in each sector)
  - fe = lambda_even / tr_even, fo = lambda_odd / tr_odd (concentration fractions)
  - residual = (lambda_even/lambda_odd) / (tr_even/tr_odd) = fe/fo
"""

import numpy as np
from numpy.linalg import eigvalsh

def build_chamber_kernel(m):
    """Build the d=2 chamber kernel K_F on C = {(i,j) : 0 <= i < j <= m-1}."""
    # Enumerate chamber states
    states = [(i, j) for i in range(m) for j in range(i+1, m)]
    n = len(states)

    # Comparability kernel on [m]^2: K(x,y) = 1 iff x<=y or y<=x componentwise
    def comparable(x, y):
        return (x[0] <= y[0] and x[1] <= y[1]) or (y[0] <= x[0] and y[1] <= x[1])

    # Chamber kernel: K_F(P,Q) = K(P,Q) - K(P, swap(Q))
    K_F = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            val = int(comparable(P, Q)) - int(comparable(P, (Q[1], Q[0])))
            K_F[a, b] = val

    return K_F, states

def build_reflection_matrix(m, states):
    """Build the simplex reflection R: (i,j) -> (m-1-j, m-1-i) as a permutation matrix."""
    n = len(states)
    state_idx = {s: i for i, s in enumerate(states)}
    R = np.zeros((n, n))
    for i, (a, b) in enumerate(states):
        reflected = (m - 1 - b, m - 1 - a)
        j = state_idx[reflected]
        R[i, j] = 1.0
    return R

def analyze_sectors(m):
    """Compute R-sector eigenvalues, traces, and concentration fractions."""
    K_F, states = build_chamber_kernel(m)
    R = build_reflection_matrix(m, states)
    n = len(states)

    # Verify [R, K_F] = 0
    comm_norm = np.max(np.abs(R @ K_F - K_F @ R))
    assert comm_norm < 1e-10, f"[R, K_F] != 0, norm = {comm_norm}"

    # Symmetrize K_F for eigenvalue computation: K_sym = (K_F + K_F^T) / 2
    # Actually K_F may not be symmetric. Let's check.
    sym_err = np.max(np.abs(K_F - K_F.T))

    # Project onto R-even and R-odd sectors
    P_even = (np.eye(n) + R) / 2
    P_odd = (np.eye(n) - R) / 2

    # K restricted to each sector
    K_even = P_even @ K_F @ P_even
    K_odd = P_odd @ K_F @ P_odd

    # Symmetrize for eigenvalue computation
    K_even_sym = (K_even + K_even.T) / 2
    K_odd_sym = (K_odd + K_odd.T) / 2

    # Eigenvalues
    evals_even = np.sort(eigvalsh(K_even_sym))[::-1]
    evals_odd = np.sort(eigvalsh(K_odd_sym))[::-1]

    # Filter near-zero eigenvalues (from projection)
    tol = 1e-8
    evals_even_nz = evals_even[np.abs(evals_even) > tol]
    evals_odd_nz = evals_odd[np.abs(evals_odd) > tol]

    # Traces
    tr_K = np.trace(K_F)
    tr_RK = np.trace(R @ K_F)
    tr_even = (tr_K + tr_RK) / 2
    tr_odd = (tr_K - tr_RK) / 2

    # Top eigenvalues
    le = evals_even_nz[0] if len(evals_even_nz) > 0 else 0
    lo = evals_odd_nz[0] if len(evals_odd_nz) > 0 else 0

    # Second eigenvalues
    le2 = evals_even_nz[1] if len(evals_even_nz) > 1 else 0
    lo2 = evals_odd_nz[1] if len(evals_odd_nz) > 1 else 0

    # Concentration fractions
    fe = le / tr_even if tr_even > 0 else 0
    fo = lo / tr_odd if tr_odd > 0 else 0

    return {
        'm': m,
        'n_chamber': n,
        'sym_err': sym_err,
        'tr_K': tr_K,
        'tr_RK': tr_RK,
        'tr_even': tr_even,
        'tr_odd': tr_odd,
        'tr_ratio': tr_even / tr_odd if tr_odd > 0 else float('inf'),
        'le': le, 'lo': lo,
        'le2': le2, 'lo2': lo2,
        'le_lo': le / lo if lo > 0 else float('inf'),
        'fe': fe, 'fo': fo,
        'fe_fo': fe / fo if fo > 0 else float('inf'),
        'residual': (le / lo) / (tr_even / tr_odd) - 1 if tr_odd > 0 and lo > 0 else float('inf'),
        'n_even': len(evals_even_nz),
        'n_odd': len(evals_odd_nz),
        'gap_even': le / le2 if le2 > 0 else float('inf'),
        'gap_odd': lo / lo2 if lo2 > 0 else float('inf'),
        'evals_even': evals_even_nz,
        'evals_odd': evals_odd_nz,
    }

def main():
    print("=" * 90)
    print("SPECTRAL CONCENTRATION ANALYSIS: d=2 chamber kernel, R-sector decomposition")
    print("=" * 90)

    print(f"\n{'m':>4} {'n':>5} {'tr_e/tr_o':>10} {'le/lo':>10} {'fe':>8} {'fo':>8} "
          f"{'fe/fo':>8} {'resid':>10} {'gap_e':>8} {'gap_o':>8}")
    print("-" * 90)

    results = []
    for m in range(4, 40):
        r = analyze_sectors(m)
        results.append(r)
        print(f"{m:4d} {r['n_chamber']:5d} {r['tr_ratio']:10.5f} {r['le_lo']:10.5f} "
              f"{r['fe']:8.5f} {r['fo']:8.5f} {r['fe_fo']:8.5f} "
              f"{r['residual']:10.6f} {r['gap_even']:8.3f} {r['gap_odd']:8.3f}")

    # Analysis of convergence
    print("\n" + "=" * 90)
    print("CONVERGENCE ANALYSIS")
    print("=" * 90)

    # Separate even and odd m
    even_ms = [r for r in results if r['m'] % 2 == 0 and r['m'] >= 8]
    odd_ms = [r for r in results if r['m'] % 2 == 1 and r['m'] >= 9]

    print("\nEven m:")
    print(f"  {'m':>4} {'fe/fo':>10} {'residual':>12} {'m*|resid|':>12} {'gap_even':>10} {'gap_odd':>10}")
    for r in even_ms:
        print(f"  {r['m']:4d} {r['fe_fo']:10.6f} {r['residual']:12.8f} "
              f"{r['m']*abs(r['residual']):12.6f} {r['gap_even']:10.4f} {r['gap_odd']:10.4f}")

    print("\nOdd m:")
    print(f"  {'m':>4} {'fe/fo':>10} {'residual':>12} {'m*|resid|':>12} {'gap_even':>10} {'gap_odd':>10}")
    for r in odd_ms:
        print(f"  {r['m']:4d} {r['fe_fo']:10.6f} {r['residual']:12.8f} "
              f"{r['m']*abs(r['residual']):12.6f} {r['gap_even']:10.4f} {r['gap_odd']:10.4f}")

    # Spectral structure for large m
    if results:
        r = results[-1]
        m = r['m']
        print(f"\nDetailed spectrum at m={m}:")
        print(f"  Even sector ({r['n_even']} nonzero eigenvalues):")
        top_e = r['evals_even'][:min(8, len(r['evals_even']))]
        for i, ev in enumerate(top_e):
            print(f"    λ_{i+1}^even = {ev:.6f}  (fraction of tr: {ev/r['tr_even']:.6f})")
        print(f"    Sum top 8 / tr_even = {sum(top_e)/r['tr_even']:.6f}")

        print(f"  Odd sector ({r['n_odd']} nonzero eigenvalues):")
        top_o = r['evals_odd'][:min(8, len(r['evals_odd']))]
        for i, ev in enumerate(top_o):
            print(f"    λ_{i+1}^odd = {ev:.6f}  (fraction of tr: {ev/r['tr_odd']:.6f})")
        print(f"    Sum top 8 / tr_odd = {sum(top_o)/r['tr_odd']:.6f}")

        # Within-sector gap analysis
        print(f"\n  Within-sector spectral gaps:")
        print(f"    Even: λ₁/λ₂ = {r['gap_even']:.4f}")
        print(f"    Odd:  λ₁/λ₂ = {r['gap_odd']:.4f}")

        # Concentration fraction limit
        print(f"\n  Concentration fractions:")
        print(f"    f_even = λ₁/tr_even = {r['fe']:.6f}")
        print(f"    f_odd  = λ₁/tr_odd  = {r['fo']:.6f}")
        print(f"    f_even/f_odd = {r['fe_fo']:.6f}")

    # Key theoretical quantities
    print("\n" + "=" * 90)
    print("THEORETICAL PREDICTIONS (Volterra SVD)")
    print("=" * 90)
    # σ_k = 1/(2 sin((2k-1)π/(4m+2))) for the discrete Volterra operator
    # In the continuum limit: σ_k ~ 2m/((2k-1)π)
    # Compound products: σ_i σ_j for i < j
    # Parity: (-1)^{i+j} determines R-sector assignment
    m_last = results[-1]['m']
    print(f"\nAt m={m_last}:")
    from math import pi, sin
    for k in range(1, 8):
        sigma_k = 1 / (2 * sin((2*k-1) * pi / (4*m_last + 2)))
        print(f"  σ_{k} = {sigma_k:.6f}  (continuum: {2*m_last/((2*k-1)*pi):.6f})")

    # Compound products
    print(f"\n  Compound products σ_i σ_j (first 10):")
    sigmas = [1 / (2 * sin((2*k-1) * pi / (4*m_last + 2))) for k in range(1, 20)]
    products = []
    for i in range(len(sigmas)):
        for j in range(i+1, len(sigmas)):
            parity = "even" if (i+j) % 2 == 0 else "odd"
            products.append((sigmas[i]*sigmas[j], i+1, j+1, parity))
    products.sort(reverse=True)
    for val, i, j, par in products[:15]:
        print(f"    σ_{i}σ_{j} = {val:.4f}  ({par})")

if __name__ == "__main__":
    main()
