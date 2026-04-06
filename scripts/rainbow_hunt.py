#!/usr/bin/env python3
"""
rainbow_hunt.py — Systematic search for the next rainbow

Investigate:
1. d=3 eigenvalue ratio: does λ₁/λ₂ approach a recognizable constant?
2. Mass ratios m_F/m_B for d=2,3: exact values?
3. Dimensional recursion: γ_{d+1} = f(γ_d)?
4. Trace identities in d=3: analogues of tr(RK) = ⌊m/2⌋²?
5. Palindromic eigenvalue structure (Rainbow D)
6. Chamber dimension formulas across d
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations
from math import factorial, comb, log, pi

# ============================================================
# SECTION 1: d=2 Chamber eigenvalue ratio (already known → 3)
# ============================================================

def d2_chamber_kernel(m):
    """Build antisymmetrized comparability kernel for d=2."""
    states = [(i, j) for i in range(m) for j in range(i+1, m)]
    n = len(states)
    K = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            comp_PQ = int((P[0]<=Q[0] and P[1]<=Q[1]) or (Q[0]<=P[0] and Q[1]<=P[1]))
            comp_PS = int((P[0]<=Q[1] and P[1]<=Q[0]) or (Q[1]<=P[0] and Q[0]<=P[1]))
            K[a, b] = comp_PQ - comp_PS
    return K, states

# ============================================================
# SECTION 2: d=3 Chamber eigenvalue structure
# ============================================================

def d3_chamber_states(m):
    """States in d=3 chamber: (i,j,k) with i < j < k in [m]."""
    return [(i,j,k) for i in range(m) for j in range(i+1,m) for k in range(j+1,m)]

def comparable_d(x, y):
    """Componentwise comparable in [m]^d."""
    return all(a <= b for a,b in zip(x,y)) or all(b <= a for a,b in zip(x,y))

def d3_chamber_kernel(m):
    """Build antisymmetrized comparability kernel for d=3.
    K_F(P,Q) = Σ_{σ∈S_3} sign(σ) · K(P, σQ)
    where K(x,y) = 1 iff comparable componentwise."""
    states = d3_chamber_states(m)
    n = len(states)
    if n == 0:
        return np.zeros((0,0)), states

    perms = list(permutations(range(3)))
    signs = []
    for p in perms:
        # Compute sign of permutation
        inv = sum(1 for i in range(3) for j in range(i+1,3) if p[i] > p[j])
        signs.append((-1)**inv)

    K = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            val = 0
            for perm, sign in zip(perms, signs):
                Qp = tuple(Q[perm[i]] for i in range(3))
                if comparable_d(P, Qp):
                    val += sign
            K[a, b] = val
    return K, states

def d3_reflection(m, states):
    """d=3 simplex reflection: (i,j,k) → (m-1-k, m-1-j, m-1-i)."""
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    R = np.zeros((n, n))
    for i, (a,b,c) in enumerate(states):
        reflected = (m-1-c, m-1-b, m-1-a)
        R[i, idx[reflected]] = 1.0
    return R

# ============================================================
# SECTION 3: Universal quantities to compute
# ============================================================

def analyze_gap(K, R, d, m):
    """Compute R-sector eigenvalues and gap for any d."""
    n = K.shape[0]
    if n < 2:
        return None

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

    le = ee_nz[0]
    lo = eo_nz[0] if len(eo_nz) > 0 else 0
    le2 = ee_nz[1]

    # Full spectrum eigenvalues
    full_evals = np.sort(eigh(K_sym, eigvals_only=True))[::-1]
    full_nz = full_evals[np.abs(full_evals) > tol]

    return {
        'd': d, 'm': m, 'n': n,
        'le': le, 'lo': lo, 'le2': le2,
        'le_lo': le/lo if lo > 0 else float('inf'),
        'le_le2': le/le2 if abs(le2) > tol else float('inf'),
        'lo_eq_le2': abs(lo - le2) < tol * max(abs(lo), abs(le2), 1),
        'full_gap': full_nz[0]/full_nz[1] if len(full_nz) > 1 else float('inf'),
        'tr_K': np.trace(K_sym),
        'tr_RK': np.trace(R @ K_sym),
        'n_even': len(ee_nz), 'n_odd': len(eo_nz),
    }

# ============================================================
# MAIN: Compute and compare across dimensions
# ============================================================

print("=" * 100)
print("RAINBOW HUNT: Searching for universal spectral laws")
print("=" * 100)

# --- d=2 ---
print("\n### d=2: Chamber eigenvalue ratios (expect → 3)")
print(f"{'m':>3} {'le/lo':>10} {'le/le2':>10} {'lo=le2?':>8} {'full_gap':>10} {'n':>5}")
for m in range(4, 30):
    K, states = d2_chamber_kernel(m)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    R = np.zeros((n,n))
    for i, (a,b) in enumerate(states):
        R[i, idx[(m-1-b, m-1-a)]] = 1.0
    r = analyze_gap(K, R, 2, m)
    if r:
        print(f"{m:3d} {r['le_lo']:10.5f} {r['le_le2']:10.5f} "
              f"{'YES' if r['lo_eq_le2'] else 'NO':>8} {r['full_gap']:10.5f} {n:5d}")

# --- d=3 ---
print("\n### d=3: Chamber eigenvalue ratios (what do they approach?)")
print(f"{'m':>3} {'le/lo':>10} {'le/le2':>10} {'lo=le2?':>8} {'full_gap':>10} {'n':>5}")
for m in range(4, 12):
    K, states = d3_chamber_kernel(m)
    if len(states) < 3:
        continue
    R = d3_reflection(m, states)
    r = analyze_gap(K, R, 3, m)
    if r:
        print(f"{m:3d} {r['le_lo']:10.5f} {r['le_le2']:10.5f} "
              f"{'YES' if r['lo_eq_le2'] else 'NO':>8} {r['full_gap']:10.5f} {r['n']:5d}")

# --- Trace identities ---
print("\n### Trace identities")
print("\nd=2: tr(K), tr(RK), floor(m/2)²")
print(f"{'m':>3} {'tr(K)':>8} {'tr(RK)':>8} {'⌊m/2⌋²':>8} {'match?':>8}")
for m in range(4, 20):
    K, states = d2_chamber_kernel(m)
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    R = np.zeros((n,n))
    for i, (a,b) in enumerate(states):
        R[i, idx[(m-1-b, m-1-a)]] = 1.0
    K_sym = (K + K.T)/2
    trK = np.trace(K_sym)
    trRK = np.trace(R @ K_sym)
    expected = (m//2)**2
    print(f"{m:3d} {trK:8.0f} {trRK:8.0f} {expected:8d} {'YES' if abs(trRK-expected)<0.5 else 'NO':>8}")

print("\nd=3: tr(K), tr(RK)")
print(f"{'m':>3} {'n':>5} {'tr(K)':>10} {'tr(RK)':>10} {'tr(RK)/n':>10}")
for m in range(4, 10):
    K, states = d3_chamber_kernel(m)
    if len(states) < 3:
        continue
    R = d3_reflection(m, states)
    K_sym = (K + K.T)/2
    trK = np.trace(K_sym)
    trRK = np.trace(R @ K_sym)
    n = len(states)
    print(f"{m:3d} {n:5d} {trK:10.1f} {trRK:10.1f} {trRK/n:10.5f}")

# --- Chamber dimensions ---
print("\n### Chamber dimensions C(m,d) and eigenvalue count patterns")
print(f"{'d':>2} {'m':>3} {'C(m,d)':>8} {'n_even':>7} {'n_odd':>7} {'n_e-n_o':>8}")
for m in [6, 8, 10]:
    for d in [2, 3]:
        n = comb(m, d)
        if d == 2:
            K, states = d2_chamber_kernel(m)
            idx = {s: i for i, s in enumerate(states)}
            R = np.zeros((n,n))
            for i, (a,b) in enumerate(states):
                R[i, idx[(m-1-b, m-1-a)]] = 1.0
        elif d == 3 and m <= 10:
            K, states = d3_chamber_kernel(m)
            R = d3_reflection(m, states)
        else:
            continue
        r = analyze_gap(K, R, d, m)
        if r:
            print(f"{d:2d} {m:3d} {n:8d} {r['n_even']:7d} {r['n_odd']:7d} {r['n_even']-r['n_odd']:8d}")

# --- Recognizable constants ---
print("\n### Recognizable constants search")
print("\nd=3 eigenvalue ratios: testing against known constants")

d3_ratios = []
for m in range(4, 12):
    K, states = d3_chamber_kernel(m)
    if len(states) < 3:
        continue
    R = d3_reflection(m, states)
    r = analyze_gap(K, R, 3, m)
    if r and r['le_lo'] < 100:
        d3_ratios.append((m, r['le_lo']))

if d3_ratios:
    last_m, last_ratio = d3_ratios[-1]
    print(f"\nBest d=3 ratio estimate (m={last_m}): {last_ratio:.8f}")

    # Test against recognizable constants
    candidates = {
        'π': pi,
        'e': np.e,
        '3': 3.0,
        '5': 5.0,
        'φ²': ((1+np.sqrt(5))/2)**2,
        'φ³': ((1+np.sqrt(5))/2)**3,
        '2π/3': 2*pi/3,
        'π/2': pi/2,
        'sqrt(5)': np.sqrt(5),
        '√2+1': np.sqrt(2)+1,
        'ln(3)': np.log(3),
        'ln(5)': np.log(5),
        '2+√3': 2+np.sqrt(3),
        '5/2': 2.5,
        '7/3': 7/3,
        '1+√5': 1+np.sqrt(5),
        '2√2': 2*np.sqrt(2),
        '3+2√2': 3+2*np.sqrt(2),
    }

    print(f"\n{'constant':>12} {'value':>12} {'diff':>12}")
    diffs = []
    for name, val in candidates.items():
        diff = abs(last_ratio - val)
        diffs.append((diff, name, val))
    diffs.sort()
    for diff, name, val in diffs[:10]:
        print(f"{name:>12} {val:12.6f} {diff:12.6f}")

print("\n### d=3 ratio convergence")
for m, ratio in d3_ratios:
    print(f"  m={m:2d}: le/lo = {ratio:.6f}")
