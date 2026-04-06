#!/usr/bin/env python3
"""
algebraic_identity_search.py — Search for the algebraic identity

Instead of working in the compound SVD basis (which doesn't preserve R²=I),
work with the DISCRETE kernel directly and look for polynomial identities
involving the eigenvalues.

KEY QUESTION: Is there a polynomial identity P(le, lo, m, d) = 0 that
forces le/lo → (d+1)/(d-1)?

For d=2: the characteristic polynomial of K_F restricted to R-sectors
might have factors that reveal the ratio.

Also: check if the SECULAR EQUATION has a clean form.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations, combinations
from math import comb
from numpy.polynomial import polynomial as P

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
    for a, P_st in enumerate(states):
        for b, Q in enumerate(states):
            val = 0
            for perm, sgn in zip(perms, perm_signs):
                Qp = tuple(Q[perm[i]] for i in range(d))
                if all(P_st[i] <= Qp[i] for i in range(d)) or \
                   all(Qp[i] <= P_st[i] for i in range(d)):
                    val += sgn
            K[a, b] = val
    K_sym = (K + K.T) / 2
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d-1-j] for j in range(d))
        R[i, idx[reflected]] = 1.0
    return K_sym, R, n

print("=" * 90)
print("SEARCH FOR ALGEBRAIC IDENTITY")
print("=" * 90)

# For d=2: compute le, lo, tr_e, tr_o, and look for relations
d = 2
print(f"\n### d={d}: Exact eigenvalue data")
print(f"{'m':>3} {'le':>12} {'lo':>12} {'le/lo':>10} {'le*lo':>12} {'le+lo':>12} "
      f"{'le²+lo²':>12} {'tr_e':>8} {'tr_o':>8}")

data = []
for m in range(4, 22):
    K, R, n = build(m, d)
    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2
    Ke = Pe @ K @ Pe
    Ko = Po @ K @ Po
    ee = np.sort(eigh(Ke, eigvals_only=True))[::-1]
    eo = np.sort(eigh(Ko, eigvals_only=True))[::-1]
    tol = 1e-8
    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]
    if len(ee_nz) < 1 or len(eo_nz) < 1:
        continue
    le = ee_nz[0]
    lo = eo_nz[0]
    tr_e = np.trace(Ke)
    tr_o = np.trace(Ko)
    data.append((m, le, lo, tr_e, tr_o))
    print(f"{m:3d} {le:12.4f} {lo:12.4f} {le/lo:10.5f} {le*lo:12.4f} {le+lo:12.4f} "
          f"{le**2+lo**2:12.4f} {tr_e:8.1f} {tr_o:8.1f}")

# Look for pattern: le*lo and le+lo as functions of m
print("\n\nPattern search:")
print(f"{'m':>3} {'le*lo':>12} {'le*lo/m²':>12} {'(le+lo)/m':>12} {'le*lo/tr_e':>12}")
for m, le, lo, tr_e, tr_o in data:
    print(f"{m:3d} {le*lo:12.4f} {le*lo/m**2:12.6f} {(le+lo)/m:12.6f} {le*lo/tr_e:12.6f}")

# Check: is le*lo related to tr_e or tr_o?
# For d=2: le*lo should be ≈ (constant)·m² as m→∞
# And le/lo → 3. So le ≈ 3k, lo ≈ k, le*lo ≈ 3k².
# With le+lo = tr_e + tr_o (NO! le+lo ≠ trace, since trace includes all eigenvalues)

# Check: does le satisfy a QUADRATIC equation?
# If le and lo are roots of x² - (le+lo)x + le·lo = 0,
# and le/lo → 3, then le ≈ 3t, lo ≈ t, le+lo ≈ 4t, le·lo ≈ 3t².
# The quadratic is x² - 4tx + 3t² = 0, roots = t and 3t. ✓

# What determines t? t = lo ≈ tr_o/(something).

print("\n\n" + "=" * 90)
print("VIETA'S FORMULAS: le and lo as roots of x² - σ₁x + σ₂ = 0")
print("=" * 90)

# Define σ₁ = le + lo (sum), σ₂ = le * lo (product)
# If le/lo → 3, then σ₁/σ₂ → 4/3 · 1/lo → 4/(3lo)... not clean.
# Better: σ₁² / σ₂ → (le+lo)² / (le·lo) = (1+r)²/r where r = le/lo.
# For r → 3: (1+3)²/3 = 16/3.

print(f"\n{'m':>3} {'σ₁=le+lo':>12} {'σ₂=le·lo':>12} {'σ₁²/σ₂':>10} {'16/3=':>8}")
for m, le, lo, tr_e, tr_o in data:
    s1 = le + lo
    s2 = le * lo
    print(f"{m:3d} {s1:12.4f} {s2:12.4f} {s1**2/s2:10.5f} {16/3:8.5f}")

# σ₁²/σ₂ → 16/3 = (d+1)²/(d-1) for d=2? (3+1)²/(3-1·1) = 16/... hmm.
# Actually for le/lo = r: σ₁²/σ₂ = (1+r)²/r. For r=3: 16/3. ✓

# Can we compute σ₁ and σ₂ independently (without knowing le, lo)?
# σ₁ = le + lo = sum of top eigenvalues in even and odd sectors.
# σ₂ = le * lo = product.

# If there's a determinantal identity: σ₂ = det(something)?
# Or a trace identity: σ₁ = tr(something)?

# Key insight: le = λ₁(K_even), lo = λ₁(K_odd) = λ₂(K_even) (by parity separation).
# So σ₁ = λ₁ + λ₂ of K_even. And σ₂ = λ₁ · λ₂ of K_even.
# These are the first two symmetric functions of the eigenvalues of K_even.

# By Newton's identities: σ₁ = tr(K_even), σ₂ = (tr(K_even)² - tr(K_even²))/2.
# NO! σ₁ is the sum of ALL eigenvalues (= trace), not just the top two.

# For a finite matrix K_even of size n_e × n_e:
# tr(K_even) = sum of ALL eigenvalues = le + Σ other eigenvalues.
# So σ₁ ≠ tr(K_even).

# But: (le + lo) / tr(K_even) might have a clean limit.

print("\n\nRatio (le+lo)/tr_even:")
for m, le, lo, tr_e, tr_o in data:
    print(f"  m={m}: (le+lo)/tr_e = {(le+lo)/tr_e:.6f}")

# For d=3:
print("\n\n" + "=" * 90)
print("d=3: Same analysis")
print("=" * 90)

d = 3
for m in range(4, 11):
    if comb(m, d) > 500:
        break
    K, R, n = build(m, d)
    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2
    ee = np.sort(eigh(Pe @ K @ Pe, eigvals_only=True))[::-1]
    eo = np.sort(eigh(Po @ K @ Po, eigvals_only=True))[::-1]
    tol = 1e-8
    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]
    if len(ee_nz) < 1 or len(eo_nz) < 1:
        continue
    le = ee_nz[0]
    lo = eo_nz[0]
    tr_e = np.trace(Pe @ K)
    s1 = le + lo
    s2 = le * lo
    r = le / lo
    vf = (1+r)**2/r
    print(f"  m={m}: le/lo={r:.5f}, σ₁²/σ₂={(s1**2/s2):.5f}, "
          f"target (d+1)²/(d·(d-1)·something)=? "
          f"(1+r)²/r={vf:.5f}")
