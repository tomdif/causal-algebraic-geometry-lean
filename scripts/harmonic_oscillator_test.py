#!/usr/bin/env python3
"""
harmonic_oscillator_test.py — Test the HO hypothesis for width dynamics

HYPOTHESIS: The width dynamics of the chamber kernel behaves like a
(d-1)-dimensional harmonic oscillator. The R-reversal on widths gives
even/odd decomposition, and the eigenvalue ratio is the HO ratio
(k+2)/k = (d+1)/(d-1) where k = d-1 = number of width variables.

TEST: For d=3, project eigenvectors onto (center, width) coordinates.
Check if the width component of ψ_o (top R-odd) looks like the first
antisymmetric HO excitation (w₁-w₂).
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

    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d-1-j] for j in range(d))
        R[i, idx[reflected]] = 1.0

    K_sym = (K + K.T) / 2
    return K_sym, R, states, idx, n

def get_top_eigenvectors(K, R, n):
    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2
    ee, ve = eigh(Pe @ K @ Pe)
    eo, vo = eigh(Po @ K @ Po)
    ie = np.argsort(ee)[::-1]
    io = np.argsort(eo)[::-1]
    return ee[ie], ve[:, ie], eo[io], vo[:, io]

# ============================================================
# TEST 1: Width decomposition for d=3
# ============================================================
print("=" * 90)
print("TEST 1: Width structure of eigenvectors (d=3)")
print("=" * 90)

d = 3
for m in [8, 10, 12]:
    K, R, states, idx, n = build(m, d)
    ee, ve, eo, vo = get_top_eigenvectors(K, R, n)

    psi_e = ve[:, 0]  # top even
    psi_o = vo[:, 0]  # top odd

    # Compute width coordinates for each state
    # For d=3: state (x₁,x₂,x₃) has widths w₁=x₂-x₁, w₂=x₃-x₂
    # Width asymmetry: w₁-w₂ = x₂-x₁ - (x₃-x₂) = 2x₂-x₁-x₃
    # Under R: x_i → m-1-x_{4-i}, so x₁→m-1-x₃, x₂→m-1-x₂, x₃→m-1-x₁
    # w₁ = x₂-x₁ → (m-1-x₂)-(m-1-x₃) = x₃-x₂ = w₂
    # So w₁↔w₂ under R. Asymmetry w₁-w₂ → w₂-w₁ = -(w₁-w₂). R-odd!

    w_asym = np.array([2*s[1] - s[0] - s[2] for s in states], dtype=float)
    w_sum = np.array([s[2] - s[0] for s in states], dtype=float)  # total width
    center = np.array([sum(s) for s in states], dtype=float)

    # Projections of eigenvectors onto width-asymmetry
    # ψ_e should have NO w₁-w₂ component (it's R-even, w_asym is R-odd)
    proj_e_wasym = np.dot(psi_e, w_asym)
    proj_o_wasym = np.dot(psi_o, w_asym)

    # ψ_o should have w₁-w₂ component (it's R-odd)
    # The question: is ψ_o ≈ (w₁-w₂) · f(w_sum, center)?

    # Compute correlation: is ψ_o proportional to w_asym * something?
    # Regress: ψ_o = α·w_asym + residual
    alpha = np.dot(psi_o, w_asym) / np.dot(w_asym, w_asym)
    residual = psi_o - alpha * w_asym
    r_squared = 1 - np.dot(residual, residual) / np.dot(psi_o, psi_o)

    print(f"\nm={m}: n={n}")
    print(f"  le={ee[0]:.4f}, lo={eo[0]:.4f}, ratio={ee[0]/eo[0]:.5f}")
    print(f"  ⟨ψ_e, w_asym⟩ = {proj_e_wasym:.6f} (should be ~0)")
    print(f"  ⟨ψ_o, w_asym⟩ = {proj_o_wasym:.6f}")
    print(f"  R² of ψ_o ~ w_asym: {r_squared:.6f}")

    # Better: is ψ_o proportional to w_asym · g(w_sum)?
    # For each value of w_sum, compute ψ_o / w_asym
    # Group states by (w_sum, center)
    wsum_vals = sorted(set(int(s[2]-s[0]) for s in states))
    print(f"  Width asymmetry analysis by total width:")
    for ws in wsum_vals[:5]:
        mask = np.array([s[2]-s[0] == ws for s in states])
        if not any(mask):
            continue
        psi_o_ws = psi_o[mask]
        wasym_ws = w_asym[mask]
        if np.max(np.abs(wasym_ws)) < 0.01:
            continue
        # Correlation between ψ_o and w_asym at this w_sum
        if len(psi_o_ws) > 1 and np.std(wasym_ws) > 0.01:
            corr = np.corrcoef(psi_o_ws, wasym_ws)[0,1]
            print(f"    w_sum={ws}: corr(ψ_o, w_asym) = {corr:.4f}, n_states={sum(mask)}")

# ============================================================
# TEST 2: Does the top odd mode factorize as (w₁-w₂)·f?
# ============================================================
print("\n\n" + "=" * 90)
print("TEST 2: Factorization ψ_o ≈ (w₁-w₂) · f(center, total_width)")
print("=" * 90)

for d in [3, 4]:
    if d == 3:
        m_range = [8, 10, 12]
    else:
        m_range = [7, 8, 9]

    for m in m_range:
        if comb(m, d) > 2000:
            continue
        K, R, states, idx, n = build(m, d)
        ee, ve, eo, vo = get_top_eigenvectors(K, R, n)
        psi_o = vo[:, 0]

        if d == 3:
            # R-odd width coordinate: w₁-w₂ = 2x₂-x₁-x₃
            w_odd = np.array([2*s[1]-s[0]-s[2] for s in states], dtype=float)
        elif d == 4:
            # R reverses (w₁,w₂,w₃) to (w₃,w₂,w₁)
            # R-odd combination: w₁-w₃ = (x₂-x₁)-(x₄-x₃)
            w_odd = np.array([(s[1]-s[0])-(s[3]-s[2]) for s in states], dtype=float)

        # Normalize
        if np.linalg.norm(w_odd) > 0:
            w_odd_n = w_odd / np.linalg.norm(w_odd)
        else:
            continue

        # Check: is ψ_o in the span of w_odd · (R-even functions)?
        # For factorization ψ_o(P) = w_odd(P) · f(P), we need ψ_o/w_odd = f
        # But w_odd can be zero at some states. Compute ratio where w_odd ≠ 0.
        nonzero = np.abs(w_odd) > 0.01 * np.max(np.abs(w_odd))
        if np.sum(nonzero) < 3:
            continue

        ratios = psi_o[nonzero] / w_odd[nonzero]
        # If factorized, ratios should depend only on R-even coordinates
        # (center and total width), not on w_odd itself.

        # Check: variance of ratios normalized
        cv = np.std(ratios) / np.abs(np.mean(ratios)) if np.abs(np.mean(ratios)) > 1e-10 else float('inf')

        # Better: compute R² of ψ_o = α·w_odd + residual
        alpha = np.dot(psi_o, w_odd) / np.dot(w_odd, w_odd)
        resid = psi_o - alpha * w_odd
        r2 = 1 - np.dot(resid, resid) / np.dot(psi_o, psi_o)

        # Even better: ψ_o = w_odd · f where f is R-even.
        # Project out the w_odd component at each (center, total_width) group.
        # For simplicity, compute the weighted R² including width dependence.

        print(f"\n  d={d}, m={m}: ratio={ee[0]/eo[0]:.5f}")
        print(f"    R²(ψ_o ~ w_odd) = {r2:.6f}")
        print(f"    CV of ψ_o/w_odd (where w_odd≠0): {cv:.4f}")

# ============================================================
# TEST 3: The HO prediction for higher excitations
# ============================================================
print("\n\n" + "=" * 90)
print("TEST 3: HO prediction for eigenvalue ratios of excited states")
print("=" * 90)

print("""
HO in k dimensions: E_n = n + k/2.
Even ground: E = k/2.
First even excited: E = k/2 + 2 (two quanta, symmetric).
  For k=2: E_exc_even/E_ground = 3/1 = 3.
  For k=3: E_exc_even/E_ground = 7/2 / 3/2 = 7/3.

First odd: E = k/2 + 1.
  Ratio to ground: (k+2)/k.
  For k=2: 4/2 = 2 ✓.

Second odd: E = k/2 + 3 (for k≥3, via (2,0,0)-(0,0,2) type).
  For k=2: (|2,0⟩-|0,2⟩)/√2, E = 3. Ratio to first odd: 3/2.
  For k=3: next antisymmetric is (|2,0,0⟩-|0,0,2⟩), E = 7/2. Ratio to first: 7/5.

Prediction: λ₂^odd / λ₁^odd for the CHAMBER kernel should match HO second/first odd ratio.
""")

for d in [3, 4]:
    k = d - 1
    # HO predictions
    E_ground = k / 2.0
    E_first_odd = k / 2.0 + 1
    E_second_odd = k / 2.0 + 3  # for k=2: second antisymmetric
    # Actually for k=2: antisymmetric states are (n₁-n₂ quanta), E = n₁+n₂+1 with n₁>n₂.
    # First: (1,0)-(0,1), E=2. Second: (2,0)-(0,2), E=3. Ratio: 3/2.
    # For k=3: First: (1,0,0)-(0,0,1), E=5/2. Second: (2,0,0)-(0,0,2), E=7/2. Ratio: 7/5.
    first_odd = E_first_odd
    if k == 2:
        second_odd = 3.0  # E = 1+0+1 = 2+1 for the second
    elif k == 3:
        second_odd = 3.5  # 2+0+0+3/2 = 7/2
    else:
        second_odd = k/2.0 + 2  # rough

    ho_ratio_12 = second_odd / first_odd

    max_m = {3: 12, 4: 9}[d]
    print(f"\nd={d} (k={k}): HO predicts λ₂^odd/λ₁^odd → {ho_ratio_12:.4f}")
    print(f"  {'m':>3} {'λ₁^odd':>10} {'λ₂^odd':>10} {'ratio':>10} {'HO pred':>10}")

    for m in range(d+2, max_m+1):
        if comb(m, d) > 2000:
            break
        K, R, states, idx, n = build(m, d)
        ee, ve, eo, vo = get_top_eigenvectors(K, R, n)

        tol = 1e-8
        eo_nz = eo[np.abs(eo) > tol]
        if len(eo_nz) >= 2:
            ratio_12 = eo_nz[0] / eo_nz[1]
            print(f"  {m:3d} {eo_nz[0]:10.4f} {eo_nz[1]:10.4f} {ratio_12:10.5f} {ho_ratio_12:10.4f}")

# ============================================================
# TEST 4: Even-sector excitations
# ============================================================
print("\n\n" + "=" * 90)
print("TEST 4: Even-sector excitation ratios")
print("=" * 90)

print("""
Even sector: HO ground E = k/2, first excited E = k/2 + 1 (one quantum, symmetric combo).
Wait: symmetric excitations are |1,0⟩+|0,1⟩ with E = k/2+1 for k=2.
Ratio: (k+2)/k = same as odd! That's because the FIRST even and odd excitations
have the SAME energy in HO. The ratio λ₁^even/λ₂^even should be...

Actually: λ₁^even = ground state. λ₂^even = first even excitation.
If λ₂^even = λ₁^odd (parity separation), then λ₁^even/λ₂^even = (d+1)/(d-1).
And the first even excitation should equal the first odd eigenvalue.

In HO: ground symmetric |0,0⟩ E=1. First antisymmetric |1,0⟩-|0,1⟩ E=2.
First symmetric excited: |1,0⟩+|0,1⟩ E=2. SAME energy as first antisymmetric!

That's the PARITY SEPARATION! In HO, the symmetric and antisymmetric first
excitations are DEGENERATE. They both have E = k/2 + 1. This explains why
λ₂^even = λ₁^odd (they correspond to the same HO energy level).
""")

for d in [3, 4]:
    k = d - 1
    print(f"\nd={d} (k={k}):")
    print(f"  {'m':>3} {'λ₂^even':>10} {'λ₁^odd':>10} {'match?':>10}")
    max_m = {3: 12, 4: 9}[d]
    for m in range(d+2, max_m+1):
        if comb(m, d) > 2000:
            break
        K, R, states, idx, n = build(m, d)
        ee, ve, eo, vo = get_top_eigenvectors(K, R, n)
        tol = 1e-8
        ee_nz = ee[np.abs(ee) > tol]
        eo_nz = eo[np.abs(eo) > tol]
        if len(ee_nz) >= 2 and len(eo_nz) >= 1:
            match = "YES" if abs(ee_nz[1] - eo_nz[0]) < tol * max(abs(ee_nz[1]), 1) else "NO"
            print(f"  {m:3d} {ee_nz[1]:10.4f} {eo_nz[0]:10.4f} {match:>10}")
