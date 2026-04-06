#!/usr/bin/env python3
"""
rainbow_e_universal.py — Test the dimensional eigenvalue law

CONJECTURE: le/lo → (d+1)/(d-1) for the d-dimensional chamber kernel.
  d=2: 3/1 = 3 ✓ (proved)
  d=3: 4/2 = 2 (numerical, m up to 11)
  d=4: 5/3 = 1.6667 (prediction!)

Also compute d=3 at larger m using transfer matrix / Galerkin.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations, combinations
from math import comb

def sign_of_perm(p):
    """Sign of permutation p (a list/tuple)."""
    n = len(p)
    inv = sum(1 for i in range(n) for j in range(i+1,n) if p[i] > p[j])
    return (-1)**inv

def chamber_kernel(m, d):
    """Build antisymmetrized comparability kernel for dimension d.
    States: strictly increasing d-tuples from [m].
    K_F(P,Q) = Σ_{σ∈S_d} sign(σ) · [comparable(P, σQ)]
    """
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
                # Comparable: all(P[i]<=Qp[i]) or all(Qp[i]<=P[i])
                if all(P[i] <= Qp[i] for i in range(d)) or \
                   all(Qp[i] <= P[i] for i in range(d)):
                    val += sgn
            K[a, b] = val
    return K, states

def reflection(m, d, states):
    """Simplex reflection: (x_1,...,x_d) → (m-1-x_d,...,m-1-x_1)."""
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d-1-j] for j in range(d))
        R[i, idx[reflected]] = 1.0
    return R

def analyze(m, d):
    K, states = chamber_kernel(m, d)
    n = len(states)
    if n < 3:
        return None
    R = reflection(m, d, states)
    K_sym = (K + K.T) / 2

    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2
    Ke = Pe @ K_sym @ Pe
    Ko = Po @ K_sym @ Po

    ee = np.sort(eigh(Ke, eigvals_only=True))[::-1]
    eo = np.sort(eigh(Ko, eigvals_only=True))[::-1]

    tol = 1e-8
    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]

    if len(ee_nz) < 2 or len(eo_nz) < 1:
        return None

    le, le2 = ee_nz[0], ee_nz[1]
    lo = eo_nz[0]

    return {
        'm': m, 'd': d, 'n': n,
        'le': le, 'lo': lo, 'le2': le2,
        'le_lo': le/lo if lo > 0 else float('inf'),
        'le_le2': le/le2 if abs(le2) > tol else float('inf'),
        'lo_eq_le2': abs(lo - le2) < tol * max(abs(lo), abs(le2), 1),
        'tr': np.trace(K_sym),
        'trRK': np.trace(R @ K_sym),
    }

# ============================================================
# d=2: confirm → 3 = (2+1)/(2-1)
# ============================================================
print("=" * 90)
print("RAINBOW E: THE DIMENSIONAL EIGENVALUE LAW")
print("CONJECTURE: le/lo → (d+1)/(d-1)")
print("=" * 90)

print(f"\n### d=2: Target = (2+1)/(2-1) = 3")
print(f"{'m':>3} {'le/lo':>10} {'3-le/lo':>10} {'lo=le2?':>8}")
for m in range(4, 35):
    r = analyze(m, 2)
    if r:
        print(f"{m:3d} {r['le_lo']:10.6f} {3-r['le_lo']:10.6f} "
              f"{'YES' if r['lo_eq_le2'] else 'NO':>8}")

# ============================================================
# d=3: test → 2 = (3+1)/(3-1)
# ============================================================
print(f"\n### d=3: Target = (3+1)/(3-1) = 2")
print(f"{'m':>3} {'n':>6} {'le/lo':>10} {'2-le/lo':>10} {'lo=le2?':>8}")
d3_data = []
for m in range(4, 14):
    n_states = comb(m, 3)
    if n_states > 3000:
        break
    r = analyze(m, 3)
    if r:
        d3_data.append(r)
        print(f"{m:3d} {r['n']:6d} {r['le_lo']:10.6f} {2-r['le_lo']:10.6f} "
              f"{'YES' if r['lo_eq_le2'] else 'NO':>8}")

# Extrapolation for d=3
if len(d3_data) >= 3:
    ms = [r['m'] for r in d3_data[-5:]]
    rs = [r['le_lo'] for r in d3_data[-5:]]
    # Fit: ratio(m) = L - a/m
    from numpy.polynomial import polynomial as P
    inv_ms = [1.0/m for m in ms]
    coeffs = np.polyfit(inv_ms, rs, 1)  # rs = coeffs[0]/m + coeffs[1]
    L_extrap = coeffs[1]
    print(f"\n  Linear extrapolation (1/m fit): L = {L_extrap:.6f}")
    print(f"  Target 2.000000, diff = {abs(L_extrap - 2):.6f}")

    # Quadratic fit
    if len(ms) >= 3:
        coeffs2 = np.polyfit(inv_ms, rs, 2)
        L_extrap2 = coeffs2[2]
        print(f"  Quadratic extrapolation: L = {L_extrap2:.6f}")
        print(f"  Target 2.000000, diff = {abs(L_extrap2 - 2):.6f}")

# ============================================================
# d=4: test → 5/3 = (4+1)/(4-1)
# ============================================================
print(f"\n### d=4: Target = (4+1)/(4-1) = 5/3 ≈ 1.666667")
print(f"{'m':>3} {'n':>6} {'le/lo':>10} {'5/3-le/lo':>10} {'lo=le2?':>8}")
d4_data = []
for m in range(5, 12):
    n_states = comb(m, 4)
    if n_states > 2000:
        print(f"{m:3d} {n_states:6d}    (too large, skipping)")
        continue
    r = analyze(m, 4)
    if r:
        d4_data.append(r)
        print(f"{m:3d} {r['n']:6d} {r['le_lo']:10.6f} {5/3-r['le_lo']:10.6f} "
              f"{'YES' if r['lo_eq_le2'] else 'NO':>8}")

# ============================================================
# d=5: test → 3/2 = (5+1)/(5-1)
# ============================================================
print(f"\n### d=5: Target = (5+1)/(5-1) = 3/2 = 1.5")
print(f"{'m':>3} {'n':>6} {'le/lo':>10} {'1.5-le/lo':>10} {'lo=le2?':>8}")
for m in range(6, 11):
    n_states = comb(m, 5)
    if n_states > 1000:
        print(f"{m:3d} {n_states:6d}    (too large, skipping)")
        continue
    r = analyze(m, 5)
    if r:
        print(f"{m:3d} {r['n']:6d} {r['le_lo']:10.6f} {1.5-r['le_lo']:10.6f} "
              f"{'YES' if r['lo_eq_le2'] else 'NO':>8}")

# ============================================================
# Summary
# ============================================================
print("\n" + "=" * 90)
print("SUMMARY: Dimensional Eigenvalue Law le/lo → (d+1)/(d-1)")
print("=" * 90)
print(f"\n{'d':>2} {'target':>10} {'best m':>7} {'best ratio':>12} {'error':>10} {'parity sep?':>12}")
for d, target, data in [(2, 3.0, None), (3, 2.0, d3_data), (4, 5/3, d4_data)]:
    if d == 2:
        r = analyze(34, 2)
        if r:
            print(f"{d:2d} {target:10.6f} {34:7d} {r['le_lo']:12.6f} {abs(target-r['le_lo']):10.6f} {'YES':>12}")
    elif data:
        r = data[-1]
        print(f"{d:2d} {target:10.6f} {r['m']:7d} {r['le_lo']:12.6f} {abs(target-r['le_lo']):10.6f} "
              f"{'YES' if r['lo_eq_le2'] else 'NO':>12}")
