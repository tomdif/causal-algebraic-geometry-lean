#!/usr/bin/env python3
"""
sector_mixing_coefficients.py — Extract the 2×2 R-odd block coefficients

For each d: compute the projected 2×2 matrix in the R-odd sector,
extract a, b, κ (normalized by S = top compound SV), and look for
exact formulas in d.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations, combinations
from math import comb

def sign_of_perm(p):
    n = len(p)
    return (-1)**sum(1 for i in range(n) for j in range(i+1,n) if p[i] > p[j])

def build_full(m, d):
    states = list(combinations(range(m), d))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    perms = list(permutations(range(d)))
    signs = [sign_of_perm(p) for p in perms]
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

    # R-reflection: x_i → m-1-x_{d-1-i}
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d-1-j] for j in range(d))
        R[i, idx[reflected]] = 1.0

    # Width reversal W: swap w_i = x_{i+1}-x_i to w_{d-1-i}
    # For (x₁,...,x_d): W keeps x₁ and x_d fixed, reverses the interior.
    # W(x₁,...,x_d) = (x₁, x₁+(x_d-x_{d-1}), x₁+(x_d-x_{d-1})+(x_{d-1}-x_{d-2}), ..., x_d)
    # Simpler: W reverses the gaps. If gaps are g_i = x_{i+1}-x_i, then W maps g_i → g_{d-1-i}.
    # The new coordinates: x₁' = x₁, x_{k+1}' = x₁ + Σ_{i=0}^{k-1} g_{d-1-i}.
    W = np.zeros((n, n))
    for i, s in enumerate(states):
        gaps = [s[j+1]-s[j] for j in range(d-1)]
        new_gaps = gaps[::-1]  # reverse
        new_s = [s[0]]
        for g in new_gaps:
            new_s.append(new_s[-1] + g)
        new_s = tuple(new_s)
        if new_s in idx:
            W[i, idx[new_s]] = 1.0

    # Center flip C = R · W (or W · R, since [W,R]=0)
    C = R @ W

    return K_sym, R, W, C, states, idx, n

print("=" * 95)
print("2×2 R-ODD BLOCK COEFFICIENTS: a/S, b/S, κ/S as functions of d")
print("=" * 95)

for d in [3, 4, 5]:
    target = (d+1)/(d-1)
    print(f"\n{'='*60}")
    print(f"d={d}, target le/lo = ({d+1})/({d-1}) = {target:.4f}")
    print(f"{'='*60}")

    max_m = {3: 14, 4: 10, 5: 8}[d]
    print(f"\n{'m':>3} {'S':>10} {'a/S':>10} {'b/S':>10} {'κ/S':>10} "
          f"{'le/lo_2x2':>10} {'le/lo_act':>10} {'target':>10}")

    for m in range(d+2, max_m+1):
        if comb(m, d) > 1500:
            break

        K, R, W, C, states, idx, n = build_full(m, d)

        # Verify R = C·W
        assert np.max(np.abs(R - C @ W)) < 1e-10

        # R-sector eigenvalues (for reference)
        Pe = (np.eye(n) + R) / 2
        Po = (np.eye(n) - R) / 2
        ee = np.sort(eigh(Pe @ K @ Pe, eigvals_only=True))[::-1]
        eo = np.sort(eigh(Po @ K @ Po, eigvals_only=True))[::-1]
        tol = 1e-8
        ee_nz = ee[np.abs(ee) > tol]
        eo_nz = eo[np.abs(eo) > tol]
        le = ee_nz[0]
        lo = eo_nz[0]

        # 4-sector projectors
        Pc_p = (np.eye(n) + C) / 2
        Pc_m = (np.eye(n) - C) / 2
        Pw_p = (np.eye(n) + W) / 2
        Pw_m = (np.eye(n) - W) / 2

        # Get top eigenvectors in each sub-sector of R-odd
        # R-odd = (C+,W-) ⊕ (C-,W+)
        P_cpwm = Pc_p @ Pw_m  # C+, W-
        P_cmwp = Pc_m @ Pw_p  # C-, W+

        K_cpwm = P_cpwm @ K @ P_cpwm
        K_cmwp = P_cmwp @ K @ P_cmwp

        e1, v1 = eigh(K_cpwm)
        e2, v2 = eigh(K_cmwp)

        i1 = np.argsort(e1)[::-1]
        i2 = np.argsort(e2)[::-1]

        # Top eigenvector in each sub-sector
        b_val = e1[i1[0]]  # top of C+W- (center-even, width-odd)
        psi_b = v1[:, i1[0]]  # the eigenvector

        a_val = e2[i2[0]]  # top of C-W+ (center-odd, width-even)
        psi_a = v2[:, i2[0]]  # the eigenvector

        # Off-diagonal coupling: κ = ⟨ψ_a, K ψ_b⟩
        kappa = np.dot(psi_a, K @ psi_b)

        # The S = top R-even eigenvalue
        S = le

        # 2×2 eigenvalue problem: [[a, κ], [κ, b]]
        # Top eigenvalue: (a+b)/2 + sqrt((a-b)²/4 + κ²)
        lo_2x2 = (a_val + b_val) / 2 + np.sqrt(((a_val - b_val) / 2)**2 + kappa**2)
        le_lo_2x2 = S / lo_2x2 if lo_2x2 > 0 else float('inf')
        le_lo_act = le / lo

        print(f"{m:3d} {S:10.4f} {a_val/S:10.6f} {b_val/S:10.6f} {abs(kappa)/S:10.6f} "
              f"{le_lo_2x2:10.5f} {le_lo_act:10.5f} {target:10.5f}")

    # Extrapolate a/S, b/S, κ/S to m→∞
    print(f"\n  Asymptotic formulas (if they exist):")
    print(f"  Target: a/S → 1/(center_ratio) = 1/3 = {1/3:.6f}")
    print(f"  Target: b/S → 1/(width_ratio)?")
    print(f"  For d={d}: (d+1)/(d-1) = {target:.4f}")
    print(f"  Required: lo/S = (d-1)/(d+1) = {(d-1)/(d+1):.6f}")
