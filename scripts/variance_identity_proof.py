#!/usr/bin/env python3
"""
variance_identity_proof.py — Prove the ground-state variance identity

APPROACH: Compute the ACTUAL eigenvector-weighted variance ratio for the
discrete chamber kernel. If it converges to 2/(d-1), that's the proof target.

For d=2: compute ⟨ψ_e, s² ψ_e⟩, ⟨ψ_e, y² ψ_e⟩ etc. using the exact
eigenvector from diagonalization.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations, combinations
from math import comb

def sign_of_perm(p):
    n = len(p)
    return (-1)**sum(1 for i in range(n) for j in range(i+1,n) if p[i] > p[j])

def build(m, d):
    states = list(combinations(range(m), d))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    perms = list(permutations(range(d)))
    perm_signs = [sign_of_perm(p) for p in perms]
    K = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            val = 0
            for perm, sgn in zip(perms, perm_signs):
                Qp = tuple(Q[perm[i]] for i in range(d))
                if all(P[i] <= Qp[i] for i in range(d)) or \
                   all(Qp[i] <= P[i] for i in range(d)):
                    val += sgn
            K[a, b] = val
    K_sym = (K + K.T) / 2
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d-1-j] for j in range(d))
        R[i, idx[reflected]] = 1.0
    return K_sym, R, states, n

def get_top_eigenvectors(K, R, n):
    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2
    ee, ve = eigh(Pe @ K @ Pe)
    eo, vo = eigh(Po @ K @ Po)
    ie = np.argsort(ee)[::-1]
    io = np.argsort(eo)[::-1]
    return ee[ie[0]], ve[:, ie[0]], eo[io[0]], vo[:, io[0]]

print("=" * 95)
print("GROUND-STATE VARIANCE RATIO: Exact eigenvector computation")
print("=" * 95)

for d in [2, 3, 4, 5]:
    target = 2.0 / (d - 1)
    print(f"\n### d={d}, target Var_s/Var_root = 2/({d-1}) = {target:.6f}")
    print(f"{'m':>3} {'le/lo':>8} {'⟨s²⟩_e':>10} {'⟨s⟩²_e':>10} {'Var_s':>10} "
          f"{'Var_root':>10} {'ratio':>10} {'target':>10}")

    max_m = {2: 30, 3: 12, 4: 9, 5: 8}[d]
    for m in range(d+2, max_m+1):
        if comb(m, d) > 2000:
            break
        K, R, states, n = build(m, d)
        le, psi_e, lo, psi_o = get_top_eigenvectors(K, R, n)

        if lo < 1e-10:
            continue

        # Compute coordinate functions for each state
        # Center: s = Σx_i / d (centered at mean)
        center_mean = d * (m - 1) / 2.0 / d  # = (m-1)/2
        s_vals = np.array([sum(st) / d - center_mean for st in states])

        # Root coordinates: y_i = x_{i+1} - x_i for i=0,...,d-2
        # Total root variance = Σ_i Var(y_i)
        y_vals = np.zeros((n, d-1))
        for idx_s, st in enumerate(states):
            for i in range(d-1):
                y_vals[idx_s, i] = st[i+1] - st[i]

        # Mean width (for centering)
        y_mean = np.array([np.sum(psi_e**2 * y_vals[:, i]) for i in range(d-1)])

        # EVEN eigenvector variances (using ψ_e as probability: |ψ_e|² weight)
        psi_e2 = psi_e**2  # probability weights

        # Var_s = ⟨s²⟩ - ⟨s⟩²
        s_mean_e = np.sum(psi_e2 * s_vals)
        s2_mean_e = np.sum(psi_e2 * s_vals**2)
        var_s_e = s2_mean_e - s_mean_e**2

        # Var_root = Σ_i [⟨y_i²⟩ - ⟨y_i⟩²]
        var_root_e = 0.0
        for i in range(d-1):
            yi = y_vals[:, i]
            yi_mean = np.sum(psi_e2 * yi)
            yi2_mean = np.sum(psi_e2 * yi**2)
            var_root_e += yi2_mean - yi_mean**2

        ratio_e = var_s_e / var_root_e if var_root_e > 0 else float('inf')

        print(f"{m:3d} {le/lo:8.4f} {s2_mean_e:10.4f} {s_mean_e**2:10.4f} "
              f"{var_s_e:10.4f} {var_root_e:10.4f} {ratio_e:10.6f} {target:10.6f}")

    # Also compute for ODD eigenvector
    print(f"\n  ODD eigenvector variance ratio (should differ):")
    for m in [max_m - 1, max_m]:
        if comb(m, d) > 2000 or m < d + 2:
            continue
        K, R, states, n = build(m, d)
        le, psi_e, lo, psi_o = get_top_eigenvectors(K, R, n)
        if lo < 1e-10:
            continue

        s_vals = np.array([sum(st) / d - (m-1)/2.0 for st in states])
        y_vals = np.zeros((n, d-1))
        for idx_s, st in enumerate(states):
            for i in range(d-1):
                y_vals[idx_s, i] = st[i+1] - st[i]

        psi_o2 = psi_o**2
        var_s_o = np.sum(psi_o2 * s_vals**2) - np.sum(psi_o2 * s_vals)**2
        var_root_o = 0.0
        for i in range(d-1):
            yi = y_vals[:, i]
            var_root_o += np.sum(psi_o2 * yi**2) - np.sum(psi_o2 * yi)**2

        ratio_o = var_s_o / var_root_o if var_root_o > 0 else float('inf')
        print(f"    m={m}: Var_s/Var_root (odd) = {ratio_o:.6f}")
