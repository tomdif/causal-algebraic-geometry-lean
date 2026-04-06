#!/usr/bin/env python3
"""
commutator_continuum.py — Crack the 2/(d-1) asymptotic

The open problem: why does ⟨ψ_e, [K,S] ψ_o⟩ / (λ_o · ⟨ψ_e, S ψ_o⟩) → 2/(d-1)?

Strategy: decompose numerator and denominator separately.
- Numerator: ⟨ψ_e, [K,S] ψ_o⟩ = ⟨ψ_e, K·S·ψ_o⟩ - λ_o·⟨ψ_e, S·ψ_o⟩
- Denominator: λ_o · ⟨ψ_e, S·ψ_o⟩

So the fraction = ⟨ψ_e, K·S·ψ_o⟩/(λ_o·⟨ψ_e, S·ψ_o⟩) - 1

And ⟨ψ_e, K·S·ψ_o⟩ = λ_e·⟨ψ_e, S·ψ_o⟩ (from self-adjointness).
So fraction = λ_e/λ_o - 1 (TAUTOLOGY — this is just the commutator identity).

The real question: can we compute the NUMERATOR and DENOMINATOR independently
from chamber geometry, and show their ratio is 2/(d-1)?

Alternative approach: study [K,S] directly.
[K,S](P,Q) = K(P,Q)·(ΣQ_i - ΣP_i)

In the continuum chamber (the simplex), what does this become?
The chamber is Δ_d = {0 ≤ x_1 < x_2 < ... < x_d ≤ 1} (after scaling).
S = Σx_i. R: x_i ↦ 1-x_{d+1-i}.

The comparability kernel K(P,Q) = 1 iff P ≤ Q or Q ≤ P componentwise.
After antisymmetrization: K_F(P,Q) = Σ_σ sign(σ) K(P, σQ).

[K_F, S] has kernel K_F(P,Q)·(ΣQ_i - ΣP_i).

Key insight: maybe we can compute the TRACE of [K,S]² or related quantities,
and extract 2/(d-1) from a trace/dimension ratio.

Or: study the EIGENVALUES of [K,S] restricted to the top eigenspace.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations, combinations
from math import comb

def sign_of_perm(p):
    n = len(p)
    return (-1)**sum(1 for i in range(n) for j in range(i+1,n) if p[i] > p[j])

def build_all(m, d):
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

    coord_sum = np.array([sum(s) for s in states], dtype=float)
    center = d * (m - 1) / 2.0
    S = np.diag(coord_sum - center)

    K_sym = (K + K.T) / 2
    KS = K_sym @ S - S @ K_sym  # [K, S]

    return K_sym, R, S, KS, states, n

# ============================================================
# APPROACH 1: Study [K,S] as an operator — what are ITS eigenvalues?
# ============================================================
print("=" * 95)
print("APPROACH 1: Eigenvalues of [K,S]")
print("=" * 95)

for d in [2, 3]:
    print(f"\n### d={d}")
    max_m = {2: 20, 3: 10}[d]
    for m in [max_m]:
        K_sym, R, S, KS, states, n = build_all(m, d)
        # [K,S] is antisymmetric (since K is symmetric and S is diagonal/symmetric)
        # Wait: [K,S] = KS - SK. If K=K^T and S=S^T, then [K,S]^T = S^TK^T - K^TS^T = SK-KS = -[K,S].
        # So [K,S] is ANTISYMMETRIC. Its eigenvalues are purely imaginary.
        # The singular values are what matter.
        svs = np.linalg.svd(KS, compute_uv=False)
        print(f"  m={m}: top 5 singular values of [K,S]: {svs[:5].round(4)}")
        print(f"    Frobenius norm of [K,S]: {np.linalg.norm(KS, 'fro'):.4f}")
        print(f"    Frobenius norm of K: {np.linalg.norm(K_sym, 'fro'):.4f}")
        print(f"    Frobenius norm of S: {np.linalg.norm(S, 'fro'):.4f}")
        print(f"    ||[K,S]||_F / (||K||_F · ||S||_F): {np.linalg.norm(KS,'fro')/(np.linalg.norm(K_sym,'fro')*np.linalg.norm(S,'fro')):.6f}")

# ============================================================
# APPROACH 2: Average coordinate displacement under K
# ============================================================
print("\n\n" + "=" * 95)
print("APPROACH 2: Average coordinate displacement ⟨ΣQ_i - ΣP_i⟩ under K")
print("=" * 95)

for d in [2, 3, 4]:
    print(f"\n### d={d}")
    max_m = {2: 25, 3: 12, 4: 8}[d]
    for m in range(d+2, max_m+1):
        if comb(m, d) > 2000:
            break
        K_sym, R, S, KS, states, n = build_all(m, d)

        Pe = (np.eye(n) + R) / 2
        Po = (np.eye(n) - R) / 2

        ee, ve = eigh(Pe @ K_sym @ Pe)
        eo, vo = eigh(Po @ K_sym @ Po)
        idx_e = np.argsort(ee)[::-1]
        idx_o = np.argsort(eo)[::-1]
        psi_e = ve[:, idx_e[0]]
        psi_o = vo[:, idx_o[0]]
        le = ee[idx_e[0]]
        lo = eo[idx_o[0]]

        if lo < 1e-10:
            continue

        # Compute individual terms
        s_inner = np.dot(psi_e, S @ psi_o)  # ⟨ψ_e, S ψ_o⟩
        ks_inner = np.dot(psi_e, KS @ psi_o)  # ⟨ψ_e, [K,S] ψ_o⟩

        # The fraction
        frac = ks_inner / (lo * s_inner) if abs(s_inner) > 1e-15 else float('inf')

        # SEPARATE numerator and denominator, normalized by m
        # ⟨ψ_e, S ψ_o⟩ should scale like m (since S ~ m * centered_coord)
        # ⟨ψ_e, [K,S] ψ_o⟩ should scale like m * λ_o (since [K,S] ~ m * [K, s_normalized])
        # So the fraction should be O(1).

        # Normalize: s_inner / m and ks_inner / (m * lo)
        s_norm = s_inner / m
        ks_norm = ks_inner / (m * lo)

        target = 2.0 / (d - 1)

        if m == max_m - 1 or m == d + 2:
            print(f"  m={m:2d}: frac={frac:.6f} target={target:.4f} "
                  f"⟨S⟩={s_inner:.4f} ⟨[K,S]⟩={ks_inner:.4f} "
                  f"lo={lo:.4f} s/m={s_norm:.4f} ks/(m·lo)={ks_norm:.6f}")

# ============================================================
# APPROACH 3: The key — what is [K,S] in terms of K itself?
# ============================================================
print("\n\n" + "=" * 95)
print("APPROACH 3: Express [K,S] in terms of K and simpler operators")
print("=" * 95)

print("""
[K,S](P,Q) = K(P,Q) · (ΣQ_i - ΣP_i)

For the ANTISYMMETRIZED comparability kernel on the chamber:
K_F(P,Q) = Σ_σ sign(σ) · [comparable(P, σQ)]

The comparability condition P ≤ σQ (componentwise) means:
  P_i ≤ Q_{σ(i)} for all i.

When P ≤ Q (in the product order, not permuted): ΣQ_i ≥ ΣP_i.
When Q ≤ P: ΣP_i ≥ ΣQ_i, so ΣQ_i - ΣP_i ≤ 0.

So [K,S] = K_forward · Δ_+ - K_backward · Δ_-
where K_forward(P,Q) = K(P,Q) for P≤Q, K_backward for Q≤P,
and Δ = |ΣQ_i - ΣP_i|.

Since K_sym = (K + K^T)/2, the forward and backward parts are related by transposition.
""")

# ============================================================
# APPROACH 4: Dimension-counting argument
# ============================================================
print("=" * 95)
print("APPROACH 4: Why 2/(d-1)? Dimension counting")
print("=" * 95)

print("""
The chamber Δ_d has d coordinates x_1 < ... < x_d.
S = Σx_i is ONE coordinate direction (the "center" or "radial" direction).
There are d-1 independent "angular" directions orthogonal to S.

Hypothesis: the commutator [K,S] measures drift in the S-direction.
The eigenvalue λ of K comes from integration over ALL d directions.
The commutator ⟨[K,S]⟩ picks out only the S-component of the drift.
The ratio ⟨[K,S]⟩/λ ~ 1/(number of perpendicular directions) = 1/(d-1)?
But the factor is 2/(d-1), not 1/(d-1).

The "2" might come from: the drift being two-sided (forward + backward),
or from the specific normalization of the eigenvectors.

Alternative: the simplex has d-1 dimensions. The center coordinate S
is a 1-dimensional direction. The drift [K,S] measures how K "pushes"
along this 1D direction. The total push is split among d-1 transverse
directions plus the 1 radial direction. The radial push fraction is
proportional to 1/(d-1), and the factor 2 comes from the antisymmetry
of S under R (each S step contributes to both even and odd sectors).
""")

# ============================================================
# APPROACH 5: Direct computation of the ratio for the CONTINUUM operator
# ============================================================
print("=" * 95)
print("APPROACH 5: Continuum scaling")
print("=" * 95)

# In the continuum limit (m → ∞), the chamber becomes [0,1]^d ∩ {x₁<...<x_d}.
# K becomes an integral operator, S becomes multiplication by Σx_i - d/2.
# The eigenvalues scale as: λ ~ C · m^d (or m^{d-1} or m^{d+1}?).

# Let's check eigenvalue scaling:
for d in [2, 3]:
    print(f"\n### d={d}: Eigenvalue scaling")
    data = []
    max_m = {2: 25, 3: 11}[d]
    for m in range(d+2, max_m+1):
        if comb(m, d) > 2000:
            break
        K_sym, R, S, KS, states, n = build_all(m, d)
        Pe = (np.eye(n) + R) / 2
        Po = (np.eye(n) - R) / 2
        ee = np.sort(eigh(Pe @ K_sym @ Pe, eigvals_only=True))[::-1]
        eo = np.sort(eigh(Po @ K_sym @ Po, eigvals_only=True))[::-1]
        le = ee[0]
        lo = eo[0]
        data.append((m, le, lo))

    if len(data) >= 3:
        ms = [d[0] for d in data]
        les = [d[1] for d in data]
        los = [d[2] for d in data]
        # Fit le ~ C * m^alpha
        from numpy import log
        log_ms = log(ms[-3:])
        log_les = log(les[-3:])
        log_los = log(los[-3:])
        alpha_e = (log_les[-1] - log_les[0]) / (log_ms[-1] - log_ms[0])
        alpha_o = (log_los[-1] - log_los[0]) / (log_ms[-1] - log_ms[0])
        print(f"  le ~ m^{alpha_e:.3f}")
        print(f"  lo ~ m^{alpha_o:.3f}")

        # Also check s_inner scaling
        for m_check in ms[-2:]:
            K_sym, R, S, KS, states, n = build_all(m_check, d)
            Pe = (np.eye(n) + R) / 2
            Po = (np.eye(n) - R) / 2
            ee, ve = eigh(Pe @ K_sym @ Pe)
            eo, vo = eigh(Po @ K_sym @ Po)
            idx_e = np.argsort(ee)[::-1]
            idx_o = np.argsort(eo)[::-1]
            psi_e = ve[:, idx_e[0]]
            psi_o = vo[:, idx_o[0]]
            s_inner = np.dot(psi_e, S @ psi_o)
            ks_inner = np.dot(psi_e, KS @ psi_o)
            lo = eo[idx_o[0]]
            print(f"  m={m_check}: |⟨S⟩|={abs(s_inner):.4f}, |⟨[K,S]⟩|={abs(ks_inner):.4f}, "
                  f"lo={lo:.4f}, |⟨[K,S]⟩|/lo={abs(ks_inner)/lo:.4f}")
