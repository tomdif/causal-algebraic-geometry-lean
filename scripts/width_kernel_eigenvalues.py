#!/usr/bin/env python3
"""
width_kernel_eigenvalues.py — Extract the effective width kernel and its eigenvalue ratio.

KEY INSIGHT: For d=2, the eigenvalue ratio comes from the CENTER Volterra (σ₁/σ₂=3).
For d=3, if the ratio comes from the WIDTH kernel, then the width-symmetric to
width-antisymmetric eigenvalue ratio should be 2.

Compute: project K_F onto a fixed center mode, extract the width kernel,
decompose into width-symmetric and width-antisymmetric, and check the ratio.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations, combinations

def sign_of_perm(p):
    n = len(p)
    return (-1)**sum(1 for i in range(n) for j in range(i+1,n) if p[i] > p[j])

def build_d3(m):
    states = list(combinations(range(m), 3))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    perms = list(permutations(range(3)))
    signs = [sign_of_perm(p) for p in perms]
    K = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            val = 0
            for perm, sgn in zip(perms, signs):
                Qp = tuple(Q[perm[i]] for i in range(3))
                if all(P[i] <= Qp[i] for i in range(3)) or \
                   all(Qp[i] <= P[i] for i in range(3)):
                    val += sgn
            K[a, b] = val
    K_sym = (K + K.T) / 2
    # Width reversal operator W: (x₁,x₂,x₃) → (x₁, x₁+x₃-x₂, x₃)
    # This swaps w₁=x₂-x₁ and w₂=x₃-x₂ while keeping x₁ and x₃ fixed.
    # In terms of ordered triples: W(a,b,c) = (a, a+c-b, c)
    W = np.zeros((n, n))
    for i, s in enumerate(states):
        a, b, c = s
        reflected = (a, a + c - b, c)
        if reflected in idx:
            W[i, idx[reflected]] = 1.0
    return K_sym, W, states, idx, n

def build_d2(m):
    states = list(combinations(range(m), 2))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    K = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            comp = (P[0]<=Q[0] and P[1]<=Q[1]) or (Q[0]<=P[0] and Q[1]<=P[1])
            comp_s = (P[0]<=Q[1] and P[1]<=Q[0]) or (Q[1]<=P[0] and Q[0]<=P[1])
            K[a, b] = int(comp) - int(comp_s)
    K_sym = (K + K.T) / 2
    # R reflection for d=2
    R = np.zeros((n, n))
    for i, (a,b) in enumerate(states):
        R[i, idx[(m-1-b, m-1-a)]] = 1.0
    return K_sym, R, states, idx, n

print("=" * 90)
print("WIDTH KERNEL EIGENVALUE RATIO")
print("=" * 90)

# For d=3: decompose K_F by width-reversal symmetry (w₁ ↔ w₂)
# AND by R-reflection. The R-reflection for d=3 is:
# R(x₁,x₂,x₃) = (m-1-x₃, m-1-x₂, m-1-x₁)
# Width reversal: W(x₁,x₂,x₃) = (x₁, x₁+x₃-x₂, x₃) [swaps w₁ and w₂]
# R = (center flip) ∘ (width reversal): R flips center AND reverses widths.
# So: W = R ∘ (center flip). The width reversal commutes with center flip.

print("\n### d=3: Width reversal eigenvalue ratio")
print(f"{'m':>3} {'n':>5} {'le_wsym':>10} {'le_wasym':>10} {'ratio':>10} {'target':>10}")

for m in range(5, 13):
    K, W, states, idx, n = build_d3(m)

    # R-reflection for d=3
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = (m-1-s[2], m-1-s[1], m-1-s[0])
        R[i, idx[reflected]] = 1.0

    # Width reversal W: check [K, W] = 0?
    comm = np.max(np.abs(K @ W - W @ K))

    # W-symmetric and W-antisymmetric projectors
    Pw_s = (np.eye(n) + W) / 2
    Pw_a = (np.eye(n) - W) / 2

    # K restricted to W-symmetric and W-antisymmetric sectors
    Kws = Pw_s @ K @ Pw_s
    Kwa = Pw_a @ K @ Pw_a

    ews = np.sort(eigh(Kws, eigvals_only=True))[::-1]
    ewa = np.sort(eigh(Kwa, eigvals_only=True))[::-1]

    tol = 1e-8
    ews_nz = ews[np.abs(ews) > tol]
    ewa_nz = ewa[np.abs(ewa) > tol]

    if len(ews_nz) > 0 and len(ewa_nz) > 0:
        ratio = ews_nz[0] / ewa_nz[0]
        print(f"{m:3d} {n:5d} {ews_nz[0]:10.4f} {ewa_nz[0]:10.4f} {ratio:10.5f} {'2.000':>10} [K,W]={comm:.1e}")

    # Also: R-even/odd decomposition
    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2
    ee = np.sort(eigh(Pe @ K @ Pe, eigvals_only=True))[::-1]
    eo = np.sort(eigh(Po @ K @ Po, eigvals_only=True))[::-1]
    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]

    if len(ee_nz) > 0 and len(eo_nz) > 0:
        r_ratio = ee_nz[0] / eo_nz[0]
        print(f"    R-even/odd: {ee_nz[0]:.4f}/{eo_nz[0]:.4f} = {r_ratio:.5f}")

    # KEY: Does W commute with R? If R = center_flip ∘ W, then R and W share eigenvectors.
    # Check: W ∘ R = center_flip (pure center reflection)?
    WR = W @ R
    RW = R @ W
    # Is WR = RW? (i.e., do W and R commute?)
    print(f"    [W,R] = {np.max(np.abs(WR - RW)):.1e}")
    # What is W ∘ R? It should be the pure center flip.
    # W(R(x₁,x₂,x₃)) = W(m-1-x₃, m-1-x₂, m-1-x₁)
    # = (m-1-x₃, (m-1-x₃)+(m-1-x₁)-(m-1-x₂), m-1-x₁)
    # = (m-1-x₃, m-1-x₃+x₂-x₁, m-1-x₁)... hmm, not clean.

# Check: For d=3, does the width-reversal ratio give 2?
# If not, what DOES the width-symmetric/antisymmetric decomposition give?

print("\n\n" + "=" * 90)
print("DECOMPOSITION: R = (center flip) × (width reversal)?")
print("=" * 90)

m = 10
K, W, states, idx, n = build_d3(m)
R = np.zeros((n, n))
for i, s in enumerate(states):
    reflected = (m-1-s[2], m-1-s[1], m-1-s[0])
    R[i, idx[reflected]] = 1.0

# Define center flip C: (x₁,x₂,x₃) → (m-1-x₃, m-1-x₂, m-1-x₁)... that's R itself!
# Actually R for d=3 IS the combination of center flip and width reversal.
# R(x₁,x₂,x₃) = (m-1-x₃, m-1-x₂, m-1-x₁).
# Width reversal: w₁=x₂-x₁→x₃-x₂=w₂, w₂→w₁. ✓ R reverses widths.
# Center: c=(x₁+x₂+x₃)/3 → (3(m-1)-(x₁+x₂+x₃))/3 = (m-1)-c. ✓ R flips center.
# So R DOES flip center AND reverse widths simultaneously.

# The width reversal W: (x₁,x₂,x₃) → (x₁, x₁+x₃-x₂, x₃) keeps center fixed.
# So C := R ∘ W should flip center but not widths.
C = R @ W  # = center flip (only)

# Check: C should satisfy C²=I, [C,K]=0, C flips center, preserves widths
print(f"C² = I? {np.max(np.abs(C@C - np.eye(n))):.1e}")
print(f"[C,K] = 0? {np.max(np.abs(C@K - K@C)):.1e}")
print(f"[W,K] = 0? {np.max(np.abs(W@K - K@W)):.1e}")

# Now decompose K_F into 4 sectors: (C-even/odd) × (W-even/odd)
# R = C·W means R-even = (C-even,W-even) + (C-odd,W-odd)
# R-odd = (C-even,W-odd) + (C-odd,W-even)

Pc_e = (np.eye(n) + C) / 2
Pc_o = (np.eye(n) - C) / 2
Pw_e = (np.eye(n) + W) / 2
Pw_o = (np.eye(n) - W) / 2

# 4 sectors
sectors = {
    'C+W+': Pc_e @ Pw_e,
    'C+W-': Pc_e @ Pw_o,
    'C-W+': Pc_o @ Pw_e,
    'C-W-': Pc_o @ Pw_o,
}

print(f"\n4-sector decomposition (m={m}):")
for name, P in sectors.items():
    Ks = P @ K @ P
    es = np.sort(eigh(Ks, eigvals_only=True))[::-1]
    es_nz = es[np.abs(es) > 1e-8]
    # R-parity: C+W+ and C-W- are R-even; C+W- and C-W+ are R-odd
    r_par = 'R-even' if name in ['C+W+', 'C-W-'] else 'R-odd'
    top = es_nz[0] if len(es_nz) > 0 else 0
    print(f"  {name} ({r_par}): dim={len(es_nz):3d}, top eigenvalue={top:10.4f}")

# The R-EVEN sector = C+W+ ⊕ C-W-. Top of each:
K_cpwp = sectors['C+W+'] @ K @ sectors['C+W+']
K_cmwm = sectors['C-W-'] @ K @ sectors['C-W-']
e_cpwp = np.sort(eigh(K_cpwp, eigvals_only=True))[::-1]
e_cmwm = np.sort(eigh(K_cmwm, eigvals_only=True))[::-1]
tol = 1e-8
print(f"\nR-EVEN = C+W+ ⊕ C-W-:")
print(f"  C+W+ top: {e_cpwp[e_cpwp>tol][0]:.4f}" if any(e_cpwp>tol) else "  C+W+ empty")
print(f"  C-W- top: {e_cmwm[e_cmwm>tol][0]:.4f}" if any(e_cmwm>tol) else "  C-W- empty")

K_cpwm = sectors['C+W-'] @ K @ sectors['C+W-']
K_cmwp = sectors['C-W+'] @ K @ sectors['C-W+']
e_cpwm = np.sort(eigh(K_cpwm, eigvals_only=True))[::-1]
e_cmwp = np.sort(eigh(K_cmwp, eigvals_only=True))[::-1]
print(f"\nR-ODD = C+W- ⊕ C-W+:")
print(f"  C+W- top: {e_cpwm[e_cpwm>tol][0]:.4f}" if any(e_cpwm>tol) else "  C+W- empty")
print(f"  C-W+ top: {e_cmwp[e_cmwp>tol][0]:.4f}" if any(e_cmwp>tol) else "  C-W+ empty")

# The TOP R-even eigenvalue is max(top C+W+, top C-W-)
# The TOP R-odd eigenvalue is max(top C+W-, top C-W+)
le = max(e_cpwp[e_cpwp>tol][0], e_cmwm[e_cmwm>tol][0])
lo_cands = []
if any(e_cpwm > tol): lo_cands.append(e_cpwm[e_cpwm>tol][0])
if any(e_cmwp > tol): lo_cands.append(e_cmwp[e_cmwp>tol][0])
lo = max(lo_cands) if lo_cands else 0

print(f"\nle = {le:.4f}, lo = {lo:.4f}, le/lo = {le/lo:.5f}")
print(f"Target: {4/2:.5f}")
