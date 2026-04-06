#!/usr/bin/env python3
"""
Test the EXACT eigenvalue pairing: λ_{k+1}^even = λ_k^odd for k ≥ 1.
"""
import numpy as np
from scipy.linalg import eigh

def build_KF(m):
    states = [(i, j) for i in range(m) for j in range(i+1, m)]
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}

    K = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            # K_F(P,Q) = comparable(P,Q) - comparable(P, swap(Q))
            comp_PQ = int((P[0]<=Q[0] and P[1]<=Q[1]) or (Q[0]<=P[0] and Q[1]<=P[1]))
            comp_PS = int((P[0]<=Q[1] and P[1]<=Q[0]) or (Q[1]<=P[0] and Q[0]<=P[1]))
            K[a, b] = comp_PQ - comp_PS

    R = np.zeros((n, n))
    for i, (lo, hi) in enumerate(states):
        R[i, idx[(m-1-hi, m-1-lo)]] = 1.0

    return K, R, n

def test_pairing(m):
    K, R, n = build_KF(m)
    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2

    Ke = Pe @ K @ Pe
    Ko = Po @ K @ Po

    ee = np.sort(eigh(Ke, eigvals_only=True))[::-1]
    eo = np.sort(eigh(Ko, eigvals_only=True))[::-1]

    tol = 1e-8
    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]

    # Test: λ_{k+1}^even = λ_k^odd
    n_test = min(10, len(ee_nz)-1, len(eo_nz))
    max_diff = 0
    for k in range(n_test):
        diff = abs(ee_nz[k+1] - eo_nz[k])
        max_diff = max(max_diff, diff)

    return {
        'm': m, 'n': n,
        'le': ee_nz[0], 'lo': eo_nz[0] if len(eo_nz) > 0 else 0,
        'le2': ee_nz[1] if len(ee_nz) > 1 else 0,
        'max_pairing_error': max_diff,
        'n_even': len(ee_nz), 'n_odd': len(eo_nz),
        'le_lo': ee_nz[0] / eo_nz[0] if len(eo_nz) > 0 and eo_nz[0] > 0 else float('inf'),
        'le_le2': ee_nz[0] / ee_nz[1] if len(ee_nz) > 1 and ee_nz[1] > 0 else float('inf'),
    }

print("EIGENVALUE PAIRING TEST: λ_{k+1}^even = λ_k^odd ?")
print("=" * 90)
print(f"{'m':>3} {'le/lo':>10} {'le/le2':>10} {'lo==le2?':>10} {'max_err':>15} {'n_e':>5} {'n_o':>5}")
print("-" * 68)

for m in range(4, 55):
    r = test_pairing(m)
    match = "YES" if r['max_pairing_error'] < 1e-10 else f"NO ({r['max_pairing_error']:.2e})"
    print(f"{m:3d} {r['le_lo']:10.5f} {r['le_le2']:10.5f} {match:>10s} {r['max_pairing_error']:15.2e} "
          f"{r['n_even']:5d} {r['n_odd']:5d}")

# Test: is le/lo = le/le2 always?
print("\n\nVERIFICATION: le/lo == le/le2 (both = spectral gap of full K_F)?")
print("-" * 50)
for m in [10, 20, 30, 40, 50]:
    r = test_pairing(m)
    print(f"m={m:3d}: le/lo = {r['le_lo']:.8f}, le/le2 = {r['le_le2']:.8f}, "
          f"diff = {abs(r['le_lo'] - r['le_le2']):.2e}")
