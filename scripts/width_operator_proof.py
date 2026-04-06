#!/usr/bin/env python3
"""
width_operator_proof.py — Prove the width operator has HO spacing

STRATEGY (Socratic, from first principles):

Q1: What IS the effective width operator?
A1: Fix center c. The kernel K_F restricted to fixed center gives an
    operator K_w on width space. Its spectrum should be HO-like.

Q2: What does "HO-like" mean precisely?
A2: The first excitation has energy ratio (k+2)/k to the ground state,
    where k = d-1 is the number of width variables. AND the first
    excitation is degenerate (symmetric + antisymmetric under reversal).

Q3: What's the SIMPLEST case to check?
A3: d=3 (k=2 widths). Fix center, compute the 2D width operator,
    check if its spectrum has ratio 2.

Q4: What determines the width operator's spectrum?
A4: The comparability condition in width space. Two width configs
    (w₁,w₂) and (w₁',w₂') are "width-comparable" if the full states
    (at the same center) are comparable.

Q5: Can we compute the width operator EXPLICITLY?
A5: Yes! For fixed center c, the kernel on widths is determined by
    the comparability condition restricted to states with that center.

Let's compute this.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import combinations
from math import comb

# ============================================================
# STEP 1: For d=3, decompose the kernel into center slices
# ============================================================

def d3_states_by_center(m):
    """Group d=3 chamber states by center coordinate c = x₁+x₂+x₃."""
    states = list(combinations(range(m), 3))
    by_center = {}
    for s in states:
        c = sum(s)
        if c not in by_center:
            by_center[c] = []
        by_center[c].append(s)
    return by_center

def d3_kernel_entry(P, Q, m):
    """Compute K_F(P,Q) for d=3: antisymmetrized comparability."""
    from itertools import permutations
    perms = list(permutations(range(3)))
    val = 0
    for p in perms:
        inv = sum(1 for i in range(3) for j in range(i+1,3) if p[i] > p[j])
        sgn = (-1)**inv
        Qp = (Q[p[0]], Q[p[1]], Q[p[2]])
        if all(P[i] <= Qp[i] for i in range(3)) or \
           all(Qp[i] <= P[i] for i in range(3)):
            val += sgn
    return val

print("=" * 90)
print("STEP 1: Width operator at fixed center (d=3)")
print("=" * 90)

m = 12
by_center = d3_states_by_center(m)
centers = sorted(by_center.keys())
mid_center = centers[len(centers)//2]

print(f"\nm={m}, centers range: {centers[0]}..{centers[-1]}")
print(f"Middle center c={mid_center}, #states at this center: {len(by_center[mid_center])}")

# For each center, compute the sub-kernel
# At fixed center c, states have (x₁,x₂,x₃) with x₁+x₂+x₃ = c, x₁<x₂<x₃
# Widths: w₁=x₂-x₁, w₂=x₃-x₂. So (w₁,w₂) with w₁,w₂ ≥ 1, w₁+w₂ = range = x₃-x₁

# The sub-kernel at center c: K_sub(P,Q) = K_F(P,Q) for P,Q with same center
# But K_F(P,Q) for P,Q with DIFFERENT centers is also nonzero!
# The "width operator" is NOT the restriction to fixed center.
# It's the EFFECTIVE operator obtained by projecting onto a center mode.

# Better approach: compute the full kernel, project onto the top center mode,
# and see what the induced width operator looks like.

# Actually, the right approach is to use the (c,w) decomposition:
# 1. Compute the full K_F matrix
# 2. Compute the eigenvectors
# 3. Look at the WIDTH dependence of the top eigenvectors
# 4. Extract the effective width operator

# But we already found that the eigenvectors DON'T factorize (R²=0.20).
# So the "effective width operator" isn't well-defined as a separate entity.

# NEW APPROACH: Instead of fixing center, study the REDUCED DENSITY MATRIX
# in width space.

# ============================================================
# STEP 2: The key insight — the QUADRATIC FORM of K near the diagonal
# ============================================================

print("\n\n" + "=" * 90)
print("STEP 2: Quadratic form of the kernel near the diagonal")
print("=" * 90)

print("""
The HO arises from the SECOND-ORDER EXPANSION of the kernel.

For any kernel K(x,y), the eigenvalue equation is:
  ∫ K(x,y) ψ(y) dy = λ ψ(x)

Near the maximum of ψ (the "center" of the eigenfunction),
the kernel can be expanded as:
  K(x,y) ≈ K(x₀,y₀) + first-order terms + (1/2) Hessian terms

For the comparability kernel on the chamber, the "center" of the
eigenfunction is the symmetric point w₁ = w₂ = ... = w_{d-1} = w₀.

The HESSIAN of K at the symmetric point determines the HO frequency.
If the Hessian is isotropic in the width directions with frequency ω,
then the HO eigenvalues are E_n = ω(n + k/2) and the ratio is (k+2)/k.
""")

# ============================================================
# STEP 3: Compute the Hessian of the comparability kernel
# ============================================================

print("=" * 90)
print("STEP 3: Comparability fraction as a function of width asymmetry")
print("=" * 90)

# For d=3, fix total width W = w₁+w₂ and center c.
# Vary the asymmetry δ = w₁-w₂.
# Compute: fraction of states comparable as a function of δ.

# At the symmetric point δ=0: maximum comparability.
# The comparability fraction should DECREASE quadratically with δ.

# For two states P=(x₁,x₂,x₃) and Q=(y₁,y₂,y₃):
# P ≤ Q iff x₁≤y₁, x₂≤y₂, x₃≤y₃.
# In (c, w₁, w₂) coords: x₁=c-(2w₁+w₂)/3, x₂=c+(w₁-w₂)/3, x₃=c+(w₁+2w₂)/3

# For P at (c_P, w₁_P, w₂_P) and Q at (c_Q, w₁_Q, w₂_Q):
# P ≤ Q requires:
# c_Q - c_P ≥ (2(w₁_Q-w₁_P) + (w₂_Q-w₂_P)) / 3
# c_Q - c_P ≥ -((w₁_Q-w₁_P) - (w₂_Q-w₂_P)) / 3
# c_Q - c_P ≥ -((w₁_Q-w₁_P) + 2(w₂_Q-w₂_P)) / 3

# At the symmetric point w₁=w₂=w��� for both P and Q with same center:
# Δw₁ = w₁_Q - w₁_P, Δw₂ = w₂_Q - w₂_P.
# The conditions become:
# 0 ≥ (2Δw₁ + Δw₂)/3  → 2Δw₁ + Δw₂ ≤ 0
# 0 ≥ -(Δw₁ - Δw₂)/3  → Δw₁ ≥ Δw₂
# 0 ≥ -(Δw₁ + 2Δw₂)/3 → Δw₁ + 2Δw₂ ≥ 0

# For P ≤ Q at same center: 2Δw₁+Δw₂ ≤ 0, Δw₁ ≥ Δw₂, Δw₁+2Δw₂ ≥ 0.
# This defines a cone in (Δw₁, Δw₂) space.

# For comparability (P≤Q OR Q≤P): the union of the cone and its opposite.

# The VOLUME of this cone as a fraction of all (Δw₁, Δw₂) in some ball
# determines the "comparability rate." If this rate depends on the
# WIDTH CONFIGURATION (w₁, w₂), then the effective width operator
# has a specific shape.

# KEY REALIZATION: at fixed center, the comparability is determined by
# the WIDTH differences. The kernel K(P,Q) at fixed center depends only
# on (Δw₁, Δw₂), and the comparability cone is INDEPENDENT of (w₁,w₂).

# Wait — but the antisymmetrization involves permutations!
# K_F(P,Q) = Σ_σ sign(σ) [comparable(P, σQ)].
# For σ=id: [P≤Q or Q≤P], which depends on (Δc, Δw₁, Δw₂).
# For σ≠id: [P≤σQ or σQ≤P], where σQ permutes the coordinates.

# For σ=(12) (swap first two): σQ = (y₂,y₁,y₃).
# Comparable means x₁≤y₂, x₂≤y₁, x₃≤y₃ (or reverse).

# In (c,w) coords, σQ has different widths: w₁' = y₁-y₂ < 0 (NOT in the chamber!).
# So σQ is NOT in the chamber. The condition [comparable(P, σQ)] is about
# comparing a chamber point P with a non-chamber point σQ.

# This is where the antisymmetrization creates the nontrivial structure.

# ============================================================
# STEP 4: Direct numerical test — compute the "diagonal" kernel
# ============================================================

print("\n" + "=" * 90)
print("STEP 4: The diagonal kernel K(P,P') for nearby P,P'")
print("=" * 90)

# For d=3, m large enough: compute the kernel matrix element K_F(P,Q)
# for P and Q with the SAME center and total width, varying only δ.

# P = (c-W/2-δ_P/2, c+δ_P/2, c+W/2) approximately
# But these must be integers with strict ordering.

# Let me just compute the actual matrix and look at the structure.

# For d=3, m=12: restrict to states with a specific center value
# and compute the sub-matrix. Then diagonalize by width symmetry.

from itertools import permutations

def d3_full_kernel(m):
    states = list(combinations(range(m), 3))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    perms = list(permutations(range(3)))
    signs = [(-1)**sum(1 for i in range(3) for j in range(i+1,3) if p[i]>p[j]) for p in perms]

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
    return K, states, idx

m = 12
K, states, idx = d3_full_kernel(m)
K_sym = (K + K.T) / 2
n = len(states)

# Group states by (center, total_width)
by_cw = {}
for i, s in enumerate(states):
    c = sum(s)
    W = s[2] - s[0]  # total width
    delta = s[1] - s[0] - (s[2] - s[1])  # w₁ - w₂ = 2x�� - x₁ - x₃
    key = (c, W)
    if key not in by_cw:
        by_cw[key] = []
    by_cw[key].append((i, delta))

# For each (center, total_width) group: compute the sub-kernel
# and see if it has HO structure in the δ variable.

print(f"\nm={m}: {n} states")
print(f"\nSub-kernel structure at selected (center, total_width) slices:")

# Pick a representative slice
for c_target, W_target in [(18, 6), (16, 8), (15, 5)]:
    key = (c_target, W_target)
    if key not in by_cw or len(by_cw[key]) < 3:
        continue
    group = by_cw[key]
    indices = [g[0] for g in group]
    deltas = [g[1] for g in group]
    ng = len(indices)

    # Extract sub-matrix
    sub_K = K_sym[np.ix_(indices, indices)]

    # Diagonalize
    evals = np.sort(np.linalg.eigvalsh(sub_K))[::-1]

    print(f"\n  c={c_target}, W={W_target}: {ng} states, δ values = {deltas}")
    print(f"    Sub-kernel eigenvalues: {evals.round(4)}")
    if ng >= 2:
        print(f"    Ratio λ₁/λ₂: {evals[0]/evals[1]:.4f}" if abs(evals[1]) > 0.01 else "    λ₂ ≈ 0")

# ============================================================
# STEP 5: The CROSS-CENTER kernel and its role
# ============================================================

print("\n\n" + "=" * 90)
print("STEP 5: Cross-center coupling")
print("=" * 90)

# The full kernel couples states at DIFFERENT centers.
# The effective width operator is NOT just the fixed-center sub-kernel.
# It's the result of integrating out the center coordinate.

# Approach: compute the REDUCED width kernel by summing over center pairs.
# K_w(w, w') = Σ_{c,c'} K(c,w; c',w') · f(c) · f(c')
# where f(c) is the top center eigenfunction.

# For a cruder test: just sum K over all center pairs at fixed widths.
# K_w_crude(δ, δ') = Σ_{all pairs with widths δ and δ'} K(P,Q) / normalization

# Group states by their width asymmetry δ
by_delta = {}
for i, s in enumerate(states):
    delta = s[1] - s[0] - (s[2] - s[1])  # w₁ - w₂
    if delta not in by_delta:
        by_delta[delta] = []
    by_delta[delta].append(i)

deltas = sorted(by_delta.keys())
nd = len(deltas)
print(f"\nWidth asymmetry values: {deltas[:10]}...")

# Build reduced width kernel: K_w[δ₁, δ₂] = (1/n₁n₂) Σ K_sym[i,j] over i∈δ₁, j∈δ₂
K_w = np.zeros((nd, nd))
for a, d1 in enumerate(deltas):
    for b, d2 in enumerate(deltas):
        idx1 = by_delta[d1]
        idx2 = by_delta[d2]
        K_w[a, b] = np.sum(K_sym[np.ix_(idx1, idx2)]) / (len(idx1) * len(idx2))

# K_w should have the structure of the effective width operator.
# Under R: δ → -δ. So K_w(δ₁, δ₂) should have a reflection symmetry.

# Build R_w: the reflection on delta space
R_w = np.zeros((nd, nd))
for a, d1 in enumerate(deltas):
    b = deltas.index(-d1) if -d1 in deltas else -1
    if b >= 0:
        R_w[a, b] = 1.0

# Check symmetry
comm = np.max(np.abs(K_w @ R_w - R_w @ K_w))
print(f"\n[R_w, K_w] norm: {comm:.6f}")

# Eigenvalues of K_w
ew = np.sort(np.linalg.eigvalsh((K_w + K_w.T)/2))[::-1]
print(f"Reduced width kernel eigenvalues (top 5): {ew[:5].round(4)}")
if abs(ew[1]) > 0.01:
    print(f"λ₁/λ₂ = {ew[0]/ew[1]:.4f} (target for d=3: 2.0)")

# Project K_w into even and odd under R_w
Pew = (np.eye(nd) + R_w) / 2
Pow = (np.eye(nd) - R_w) / 2

Kwe = Pew @ ((K_w+K_w.T)/2) @ Pew
Kwo = Pow @ ((K_w+K_w.T)/2) @ Pow

ewe = np.sort(eigh(Kwe, eigvals_only=True))[::-1]
ewo = np.sort(eigh(Kwo, eigvals_only=True))[::-1]

tol = 1e-8
ewe_nz = ewe[np.abs(ewe) > tol]
ewo_nz = ewo[np.abs(ewo) > tol]

print(f"\nReduced width kernel — R_w sectors:")
print(f"  Even: {ewe_nz[:5].round(4)}")
print(f"  Odd:  {ewo_nz[:5].round(4)}")
if len(ewe_nz) > 0 and len(ewo_nz) > 0:
    print(f"  Ratio λ_e/λ_o = {ewe_nz[0]/ewo_nz[0]:.4f} (target: 2.0)")

# ============================================================
# STEP 6: Quadratic fit of the reduced kernel
# ============================================================

print("\n\n" + "=" * 90)
print("STEP 6: Quadratic structure of the reduced width kernel")
print("=" * 90)

# K_w(δ₁, δ₂) as a function of δ₁, δ₂.
# If HO: K_w ∝ exp(-α(δ₁²+δ₂²)/2 + β·δ₁·δ₂) or similar.
# Check: is the diagonal K_w(δ,δ) a quadratic function of δ?

print(f"\nDiagonal of reduced width kernel K_w(δ,δ):")
for a, d1 in enumerate(deltas):
    if abs(d1) <= 6:
        print(f"  δ={d1:3d}: K_w(δ,δ) = {K_w[a,a]:.4f}")

# Fit quadratic: K_w(δ,δ) = A - B·δ²
diag_vals = [(d1, K_w[a,a]) for a, d1 in enumerate(deltas) if abs(d1) <= 6]
if len(diag_vals) >= 3:
    ds = np.array([v[0] for v in diag_vals])
    kd = np.array([v[1] for v in diag_vals])
    # Fit: kd = A + B*ds²
    X = np.column_stack([np.ones_like(ds), ds**2])
    coeffs = np.linalg.lstsq(X, kd, rcond=None)[0]
    A, B = coeffs
    residuals = kd - (A + B * ds**2)
    print(f"\n  Quadratic fit: K_w(δ,δ) = {A:.4f} + ({B:.4f})·δ²")
    print(f"  Max residual: {np.max(np.abs(residuals)):.6f}")
    print(f"  B < 0? {'YES — concave (HO-like)' if B < 0 else 'NO — convex'}")
