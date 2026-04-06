#!/usr/bin/env python3
"""
rep_theory_argument.py — The representation-theoretic route to (d+1)/(d-1)

KEY IDEA: The chamber kernel K_F acts on Λ^d(ℝ^m). The reflection R = Λ^d(R₁)
where R₁ reverses and negates. R acts on the root space as the diagram
automorphism τ.

The eigenvalue ratio should be determined by the MOMENT OF INERTIA of the
comparability region in the τ-even vs τ-odd root directions.

CONCRETELY: for two points P, Q in the chamber, comparability P ≤ Q means
Δx_i ≥ 0 for all i. In root coordinates:
  Δs = Σ Δx_i ≥ 0  (center shift)
  Δy_i = Δx_{i+1} - Δx_i  (root shifts, can be positive or negative)

The conditions Δx_i ≥ 0 for all i constrain (Δs, Δy) to a CONE.

The eigenvalue ratio comes from how the kernel's "weight" is distributed
across τ-even and τ-odd root directions within this cone.

PREDICTION: The "moment of inertia" ratio in the τ-even vs τ-odd directions
gives exactly (d+1)/(d-1).
"""

import numpy as np
from itertools import combinations
from math import comb

def compute_moments(d, N=100000):
    """
    Monte Carlo: sample random comparable pairs in the d-dimensional chamber
    and compute moments of the displacement in root coordinates.

    For P, Q in chamber {0 < x₁ < ... < x_d < 1}, P ≤ Q means x_i^P ≤ x_i^Q.

    Root coordinates: center s = Σx_i/d, differences y_i = x_{i+1} - x_i.

    Diagram automorphism τ: y_i → y_{d-i}.
    τ-odd displacement: Δy_i - Δy_{d-i} for each pair (i, d-i).
    τ-even displacement: Δy_i + Δy_{d-i} for each pair.
    """
    rng = np.random.default_rng(42)

    # Sample P in the chamber: sort d uniform [0,1] samples
    P = np.sort(rng.random((N, d)), axis=1)
    Q = np.sort(rng.random((N, d)), axis=1)

    # Keep only comparable pairs (P ≤ Q componentwise)
    comparable = np.all(P <= Q, axis=1)
    P_comp = P[comparable]
    Q_comp = Q[comparable]
    n_comp = P_comp.shape[0]

    if n_comp < 100:
        return None

    # Displacements
    Delta = Q_comp - P_comp  # all ≥ 0

    # Center displacement
    Ds = np.sum(Delta, axis=1) / d  # Δs = ΣΔx_i / d

    # Root displacements: Δy_i = Δx_{i+1} - Δx_i
    Dy = np.diff(Delta, axis=1)  # shape (n_comp, d-1)

    # τ-even and τ-odd decomposition of root displacements
    k = d - 1  # number of root coordinates

    # τ acts as y_i → y_{k-1-i} (0-indexed: y_0,...,y_{k-1})
    # τ-even: (y_i + y_{k-1-i})/2
    # τ-odd: (y_i - y_{k-1-i})/2

    tau_even_vars = []
    tau_odd_vars = []

    for i in range(k):
        j = k - 1 - i
        if i < j:
            even_comp = (Dy[:, i] + Dy[:, j]) / 2
            odd_comp = (Dy[:, i] - Dy[:, j]) / 2
            tau_even_vars.append(even_comp)
            tau_odd_vars.append(odd_comp)
        elif i == j:
            # Fixed by τ: purely even
            tau_even_vars.append(Dy[:, i])

    # Compute second moments (variances)
    var_s = np.mean(Ds**2)  # variance of center displacement

    # Total variance in τ-even root directions
    var_even = sum(np.mean(v**2) for v in tau_even_vars) if tau_even_vars else 0

    # Total variance in τ-odd root directions
    var_odd = sum(np.mean(v**2) for v in tau_odd_vars) if tau_odd_vars else 0

    # Total root variance
    var_root = np.mean(np.sum(Dy**2, axis=1))

    # Number of even and odd root directions
    n_even = len(tau_even_vars)
    n_odd = len(tau_odd_vars)

    return {
        'd': d,
        'n_comp': n_comp,
        'n_total': N,
        'comp_frac': n_comp / N,
        'var_s': var_s,
        'var_root': var_root,
        'var_even': var_even,
        'var_odd': var_odd,
        'n_even_dirs': n_even,
        'n_odd_dirs': n_odd,
        'var_per_even': var_even / n_even if n_even > 0 else 0,
        'var_per_odd': var_odd / n_odd if n_odd > 0 else 0,
    }

print("=" * 95)
print("REPRESENTATION-THEORETIC MOMENT ANALYSIS")
print("Diagram automorphism τ: α_i → α_{d-i}")
print("=" * 95)

N = 500000
for d in [2, 3, 4, 5, 6]:
    r = compute_moments(d, N)
    if r is None:
        print(f"\nd={d}: insufficient comparable pairs")
        continue

    target = (d+1)/(d-1)

    print(f"\n### d={d}: target ratio = ({d+1})/({d-1}) = {target:.4f}")
    print(f"  Comparable pairs: {r['n_comp']}/{r['n_total']} ({r['comp_frac']:.4f})")
    print(f"  Var(center): {r['var_s']:.6f}")
    print(f"  Var(root):   {r['var_root']:.6f}")
    print(f"  τ-even root dirs: {r['n_even_dirs']}, total var = {r['var_even']:.6f}, per dir = {r['var_per_even']:.6f}")
    print(f"  τ-odd root dirs:  {r['n_odd_dirs']}, total var = {r['var_odd']:.6f}, per dir = {r['var_per_odd']:.6f}")

    # KEY RATIOS
    if r['var_odd'] > 0:
        ratio_var = r['var_even'] / r['var_odd']
        ratio_per_dir = r['var_per_even'] / r['var_per_odd'] if r['var_per_odd'] > 0 else float('inf')
        print(f"\n  RATIOS:")
        print(f"    Var_even/Var_odd = {ratio_var:.6f}")
        print(f"    (Var_even/n_e) / (Var_odd/n_o) = {ratio_per_dir:.6f}")
        print(f"    Target (d+1)/(d-1) = {target:.6f}")

        # Try: (Var_s + Var_even) / (Var_s + Var_odd)?
        r1 = (r['var_s'] + r['var_even']) / (r['var_s'] + r['var_odd']) if (r['var_s'] + r['var_odd']) > 0 else 0
        # Or: Var_s / Var_odd?
        r2 = r['var_s'] / r['var_odd'] if r['var_odd'] > 0 else 0
        # Or: (Var_s + Var_root) / Var_root?
        r3 = (r['var_s'] + r['var_root']) / r['var_root'] if r['var_root'] > 0 else 0
        # Or: total_var / root_var = 1 + var_s/var_root
        r4 = 1 + r['var_s'] / r['var_root'] if r['var_root'] > 0 else 0

        print(f"\n  CANDIDATE FORMULAS:")
        print(f"    (var_s + var_even)/(var_s + var_odd) = {r1:.6f}")
        print(f"    var_s / var_odd = {r2:.6f}")
        print(f"    (var_s + var_root) / var_root = {r3:.6f}")
        print(f"    1 + var_s/var_root = {r4:.6f}")

        # The TOTAL displacement variance: var_total = var_s + var_root (since s and root are orthogonal)
        # In d coordinates: var_total = Σ Var(Δx_i).
        # For P ≤ Q with P,Q uniform on simplex: Var(Δx_i) is the same for each i by symmetry?
        # NO: in the CHAMBER, x₁ < ... < x_d, so the coordinates are NOT symmetric.
        # But COMPARABLE pairs P ≤ Q have Δx_i ≥ 0 for all i.

        per_coord_var = [np.mean((r['n_comp'] > 0) * 1.0)] # placeholder

    # The REAL test: does the per-direction variance ratio give (d+1)/(d-1)?
    # Or does a TRACE formula involving these variances give the ratio?

# ============================================================
# DEEPER: The mean displacement vector and its projection
# ============================================================
print("\n\n" + "=" * 95)
print("MEAN DISPLACEMENT ANALYSIS")
print("=" * 95)

for d in [2, 3, 4, 5]:
    rng = np.random.default_rng(42)
    N = 500000
    P = np.sort(rng.random((N, d)), axis=1)
    Q = np.sort(rng.random((N, d)), axis=1)
    comp = np.all(P <= Q, axis=1)
    Delta = (Q - P)[comp]
    n = Delta.shape[0]

    if n < 100:
        continue

    # Mean displacement per coordinate
    mean_delta = np.mean(Delta, axis=1)  # per sample
    mean_per_coord = np.mean(Delta, axis=0)  # per coordinate, averaged over samples

    # In the continuum, Δx_i = Q_i - P_i ≥ 0 for comparable P ≤ Q.
    # The MEAN of Δx_i for each coordinate i:
    print(f"\nd={d}: Mean displacement per coordinate (comparable pairs):")
    for i in range(d):
        print(f"  ⟨Δx_{i+1}⟩ = {mean_per_coord[i]:.6f}")

    # Total mean displacement (= mean of ΣΔx_i = d·⟨Δs⟩)
    print(f"  ⟨Σ Δx_i⟩ = {np.sum(mean_per_coord):.6f}")

    # SECOND MOMENT: ⟨Δx_i · Δx_j⟩
    cov = np.zeros((d, d))
    for i in range(d):
        for j in range(d):
            cov[i,j] = np.mean(Delta[:, i] * Delta[:, j])

    print(f"  Covariance matrix ⟨Δx_i Δx_j⟩:")
    for i in range(d):
        row = " ".join(f"{cov[i,j]:8.5f}" for j in range(d))
        print(f"    [{row}]")

    # Eigenvalues of the covariance matrix
    evals = np.sort(np.linalg.eigvalsh(cov))[::-1]
    print(f"  Eigenvalues: {evals.round(6)}")
    if len(evals) >= 2:
        print(f"  λ₁/λ₂ = {evals[0]/evals[1]:.6f}  (target: {(d+1)/(d-1):.6f})")
    if len(evals) >= 3 and evals[2] > 1e-10:
        print(f"  λ₁/λ₃ = {evals[0]/evals[2]:.6f}")
