#!/usr/bin/env python3
"""
schur_isotropy_test.py — Verify Schur's lemma isotropy

The standard representation of S_d on the root space {y_i = x_{i+1}-x_i}
is irreducible. Schur's lemma says any S_d-invariant quadratic form on this
space is proportional to the identity.

TEST: Compute the Hessian of the "comparability function" at the symmetric
point and verify it's proportional to the identity in root coordinates.

The comparability function: for a point P in the chamber, define
f(P) = #{Q in chamber : Q comparable to P} / (total chamber size).
This measures the "centrality" of P. The Hessian of f at the symmetric
point should be isotropic by Schur's lemma.
"""

import numpy as np
from itertools import combinations
from math import comb

def build_comparability_function(m, d):
    """For each state P, count how many Q are comparable to P."""
    states = list(combinations(range(m), d))
    n = len(states)

    # Comparability: P comparable to Q iff P ≤ Q or Q ≤ P componentwise
    comp_count = np.zeros(n)
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            if all(P[i] <= Q[i] for i in range(d)) or \
               all(Q[i] <= P[i] for i in range(d)):
                comp_count[a] += 1

    return states, comp_count

print("=" * 90)
print("SCHUR'S LEMMA ISOTROPY TEST")
print("Hessian of comparability function at the symmetric point")
print("=" * 90)

for d in [3, 4, 5]:
    max_m = {3: 12, 4: 8, 5: 7}[d]
    for m in [max_m]:
        states, comp = build_comparability_function(m, d)
        n = len(states)

        # Find the most symmetric states (y_i all equal or nearly equal)
        # y_i = x_{i+1} - x_i. Symmetric: all y_i = w₀.
        # For d=3, m=12: symmetric states have y₁=y₂=w₀ where x₁ < x₁+w₀ < x₁+2w₀ < m.
        # The most central: x₁ = (m-1)/2 - w₀, middle = (m-1)/2, x₃ = (m-1)/2 + w₀.

        # Compute root coordinates for each state
        y_vals = np.zeros((n, d-1))
        for i, s in enumerate(states):
            for k in range(d-1):
                y_vals[i, k] = s[k+1] - s[k]

        # Asymmetry: deviation from equal widths
        y_mean = np.mean(y_vals, axis=1, keepdims=True)  # mean width per state
        y_dev = y_vals - y_mean  # deviation from mean width

        # Find the state closest to symmetric with maximum comp_count
        # Symmetric: all y_i equal, i.e., y_dev = 0
        asym = np.sum(y_dev**2, axis=1)
        sym_mask = asym < 0.5  # exactly symmetric

        if np.sum(sym_mask) > 0:
            sym_states = np.where(sym_mask)[0]
            sym_comp = comp[sym_states]
            # Among symmetric states, which has highest comp count?
            best_sym = sym_states[np.argmax(sym_comp)]
            print(f"\nd={d}, m={m}: Most central symmetric state: {states[best_sym]}")
            print(f"  Comparability count: {comp[best_sym]:.0f} out of {n}")
            print(f"  Root coords y_i: {y_vals[best_sym]}")

        # Now: compute the Hessian of comp_count as a function of root deviations
        # Use a finite-difference approximation:
        # Group states by their center (s = Σx_i) and total width (W = x_d - x_1)
        # At fixed s and W, vary the root asymmetry δ = y - mean_y

        # Better: compute the covariance of comp_count with root deviations
        # If comp(P) = c₀ + Σ H_ij δy_i δy_j + ..., then
        # Cov(comp, δy_i δy_j) ∝ H_ij (for uniformly sampled P near symmetric point)

        # Crude approach: compute the "Hessian" from nearby states
        # For each symmetric state, look at neighbors that differ by ±1 in one y_i
        # and check if the comp_count change is isotropic.

        # Even simpler: compute ⟨comp · y_dev_i · y_dev_j⟩ / ⟨comp⟩
        comp_centered = comp - np.mean(comp)
        y_cov = np.zeros((d-1, d-1))
        for i in range(d-1):
            for j in range(d-1):
                y_cov[i,j] = np.mean(comp * y_dev[:, i] * y_dev[:, j]) / np.mean(comp)

        print(f"\n  Comparability-weighted root covariance:")
        for i in range(d-1):
            row = " ".join(f"{y_cov[i,j]:10.4f}" for j in range(d-1))
            print(f"    [{row}]")

        evals = np.sort(np.linalg.eigvalsh(y_cov))[::-1]
        print(f"  Eigenvalues: {evals.round(6)}")
        print(f"  Isotropy ratio (max/min): {evals[0]/evals[-1]:.6f}")
        print(f"  (1.0 = perfectly isotropic)")

        # Check the EIGENVECTOR-weighted covariance
        # Build the full antisymmetrized kernel
        from itertools import permutations
        perms = list(permutations(range(d)))
        signs = [(-1)**sum(1 for a in range(d) for b in range(a+1,d) if p[a]>p[b]) for p in perms]

        K = np.zeros((n, n))
        for a, P in enumerate(states):
            for b, Q in enumerate(states):
                val = 0
                for perm, sgn in zip(perms, signs):
                    Qp = tuple(Q[perm[i]] for i in range(d))
                    if all(P[i] <= Qp[i] for i in range(d)) or \
                       all(Qp[i] <= P[i] for i in range(d)):
                        val += sgn
                K[a, b] = val
        K_sym = (K + K.T) / 2

        # Get top eigenvector
        from scipy.linalg import eigh
        evals_K, evecs = eigh(K_sym)
        top_idx = np.argsort(evals_K)[-1]
        psi = evecs[:, top_idx]
        psi2 = psi**2

        # Eigenvector-weighted root covariance
        y_cov_psi = np.zeros((d-1, d-1))
        for i in range(d-1):
            for j in range(d-1):
                y_mean_i = np.sum(psi2 * y_vals[:, i])
                y_mean_j = np.sum(psi2 * y_vals[:, j])
                y_cov_psi[i,j] = np.sum(psi2 * (y_vals[:,i] - y_mean_i) * (y_vals[:,j] - y_mean_j))

        print(f"\n  TOP EIGENVECTOR-weighted root covariance:")
        for i in range(d-1):
            row = " ".join(f"{y_cov_psi[i,j]:10.6f}" for j in range(d-1))
            print(f"    [{row}]")

        evals_psi = np.sort(np.linalg.eigvalsh(y_cov_psi))[::-1]
        print(f"  Eigenvalues: {evals_psi.round(6)}")
        if evals_psi[-1] > 1e-10:
            print(f"  Isotropy ratio (max/min): {evals_psi[0]/evals_psi[-1]:.6f}")
        print(f"  (1.0 = perfectly isotropic by Schur's lemma)")
