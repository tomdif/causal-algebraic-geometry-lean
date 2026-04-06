#!/usr/bin/env python3
"""
rainbow_e_mechanism.py — Investigate the spectral mechanism behind (d+1)/(d-1)

The trace ratio gives (d+1)/(d-1) only for d=2.
The EIGENVALUE ratio gives (d+1)/(d-1) for d=2,3,4,5.
So the mechanism is spectral, not combinatorial.

Key questions:
1. What is the continuum operator for general d?
2. How do the Volterra SVs interact with the R-sectors?
3. Is there a d-dependent Volterra formula?

Approach: study the 1D Volterra SVs σ_k = 1/(2sin((2k-1)π/(4m+2)))
and how the d-fold compound C_d(V) interacts with the simplex reflection.
"""

import numpy as np
from math import pi, sin, comb
from itertools import combinations

def volterra_svs(m, n_svs=20):
    """Compute 1D Volterra singular values for [m] grid."""
    return [1.0 / (2 * sin((2*k-1) * pi / (4*m + 2))) for k in range(1, n_svs+1)]

def compound_eigenvalues(svs, d):
    """Compute all d-fold products of SVs (eigenvalues of C_d(V))."""
    products = []
    indices = list(combinations(range(len(svs)), d))
    for idx in indices:
        prod = 1.0
        for i in idx:
            prod *= svs[i]
        products.append((prod, idx))
    products.sort(reverse=True)
    return products

def sv_parity(indices, d):
    """R-parity of compound eigenvector u_{i1} ∧ ... ∧ u_{id}.
    Under R, the k-th SV has parity (-1)^{k+1}: σ₁ even, σ₂ odd, σ₃ even, ...
    Compound parity = product of individual parities = (-1)^{sum(i_j+1)} = (-1)^{sum + d}.
    Actually, parity = (-1)^{i₁+i₂+...+i_d} (using 0-indexed).
    With 1-indexing: σ_k has parity (-1)^{k-1}. Product: (-1)^{Σ(k_j-1)} = (-1)^{Σk_j - d}.
    """
    # 0-indexed: index i corresponds to σ_{i+1}
    # σ_{i+1} has R-parity (-1)^i
    # Compound parity = (-1)^{sum of indices (0-based)}
    s = sum(indices)
    return 'even' if s % 2 == 0 else 'odd'

print("=" * 95)
print("SPECTRAL MECHANISM: Compound Volterra eigenvalues and R-parity")
print("=" * 95)

for d in [2, 3, 4, 5]:
    print(f"\n### d={d}: Compound C_{d}(V) eigenvalues, target ratio = ({d+1})/({d-1}) = {(d+1)/(d-1):.4f}")
    m = 100  # large m for near-continuum values
    svs = volterra_svs(m, 2*d + 5)
    prods = compound_eigenvalues(svs, d)

    # Separate by parity
    even_prods = [(p, idx) for p, idx in prods if sv_parity(idx, d) == 'even']
    odd_prods = [(p, idx) for p, idx in prods if sv_parity(idx, d) == 'odd']

    print(f"  Top 5 even-parity compound eigenvalues:")
    for i, (p, idx) in enumerate(even_prods[:5]):
        labels = [f"σ_{j+1}" for j in idx]
        cont_labels = [f"{2*m/((2*(j+1)-1)*pi):.2f}" for j in idx]
        print(f"    #{i+1}: {'·'.join(labels)} = {p:.4f}  (parity sum={sum(idx)})")

    print(f"  Top 5 odd-parity compound eigenvalues:")
    for i, (p, idx) in enumerate(odd_prods[:5]):
        labels = [f"σ_{j+1}" for j in idx]
        print(f"    #{i+1}: {'·'.join(labels)} = {p:.4f}  (parity sum={sum(idx)})")

    if even_prods and odd_prods:
        top_even = even_prods[0][0]
        top_odd = odd_prods[0][0]
        print(f"\n  COMPOUND SVD RATIO: top_even / top_odd = {top_even/top_odd:.6f}")
        print(f"  TARGET:             ({d+1})/({d-1}) = {(d+1)/(d-1):.6f}")
        print(f"  MATCH:              {abs(top_even/top_odd - (d+1)/(d-1)) < 0.01}")

        # What is the ratio in terms of SV indices?
        e_idx = even_prods[0][1]
        o_idx = odd_prods[0][1]
        print(f"\n  Top even indices: {[i+1 for i in e_idx]}")
        print(f"  Top odd indices:  {[i+1 for i in o_idx]}")

        # The ratio of the two products
        ratio_factors = []
        for i in range(d):
            if e_idx[i] != o_idx[i]:
                ratio_factors.append(f"σ_{e_idx[i]+1}/σ_{o_idx[i]+1}")
        print(f"  Ratio = {'·'.join(ratio_factors)}")

        # Compute the ratio from continuum SVs: σ_k ~ 2m/((2k-1)π)
        # So σ_a/σ_b = (2b-1)/(2a-1)
        ratio_val = 1.0
        for i in range(d):
            if e_idx[i] != o_idx[i]:
                a, b = e_idx[i]+1, o_idx[i]+1
                ratio_val *= (2*b-1) / (2*a-1)
                print(f"    σ_{a}/σ_{b} = (2·{b}-1)/(2·{a}-1) = {2*b-1}/{2*a-1} = {(2*b-1)/(2*a-1):.6f}")
        print(f"  Product of ratios = {ratio_val:.6f}")
        print(f"  Target = {(d+1)/(d-1):.6f}")

# Now test: what IS the right parity assignment?
print("\n\n" + "=" * 95)
print("PARITY ANALYSIS: Which compound eigenvectors are R-even/odd?")
print("=" * 95)

# For the ACTUAL chamber kernel (not the compound Volterra), the R-reflection
# acts differently. Let me check the actual eigenvalue data against the compound
# SVD prediction.

print("\nThe compound SVD assigns R-parity based on (-1)^{sum of 0-indexed SV indices}.")
print("For d=2: top even = σ₁σ₃ (indices 0,2, sum=2, even)")
print("         top odd  = σ₁σ₂ (indices 0,1, sum=1, odd)")
print("         ratio = σ₃/σ₂ ... but we KNOW the d=2 ratio → 3 = σ₁/σ₂, not σ₃/σ₂.")
print("\nSo the COMPOUND SVD parity assignment may be WRONG!")
print("The actual R-parity on the chamber must be different.")

# Let's check: what parity assignment gives (d+1)/(d-1)?
print("\n\nSEARCH: What parity assignment reproduces (d+1)/(d-1)?")
for d in [2, 3, 4]:
    m = 100
    svs = volterra_svs(m, 2*d+5)
    prods = compound_eigenvalues(svs, d)
    target = (d+1)/(d-1)

    # Find the pair whose ratio is closest to target
    print(f"\nd={d}: target = {target:.4f}")
    best_pairs = []
    for i, (pi_val, i_idx) in enumerate(prods[:20]):
        for j, (pj_val, j_idx) in enumerate(prods[:20]):
            if i != j and pj_val > 0:
                ratio = pi_val / pj_val
                if abs(ratio - target) < 0.05:
                    best_pairs.append((abs(ratio-target), pi_val, pj_val, i_idx, j_idx, ratio))

    best_pairs.sort()
    for diff, pv1, pv2, idx1, idx2, ratio in best_pairs[:3]:
        labels1 = [f"σ_{k+1}" for k in idx1]
        labels2 = [f"σ_{k+1}" for k in idx2]
        print(f"  {'·'.join(labels1)} / {'·'.join(labels2)} = {ratio:.6f} (diff={diff:.6f})")
        # Show the SV ratio
        for a, b in zip(idx1, idx2):
            if a != b:
                print(f"    differs at position: σ_{a+1} vs σ_{b+1}, "
                      f"ratio = {(2*(b+1)-1)/(2*(a+1)-1):.4f}")
