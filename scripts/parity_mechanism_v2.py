#!/usr/bin/env python3
"""
parity_mechanism_v2.py — The commutator mechanism

KEY FINDING: K·S·ψ_o0 ≈ c·ψ_e0 with 97% overlap (d=2), 95% (d=3), 88% (d=4).
where S = Σx_i (centered), which anti-commutes with R: {R,S} = 0.

The eigenvalue gap is controlled by the COMMUTATOR [K,S]:
  (λ_e0 - λ_o0)·⟨ψ_e0, S·ψ_o0⟩ = ⟨ψ_e0, [K,S]·ψ_o0⟩

So: λ_e0/λ_o0 = 1 + ⟨ψ_e0, [K,S]·ψ_o0⟩ / (λ_o0·⟨ψ_e0, S·ψ_o0⟩)

For the ratio to be (d+1)/(d-1), we need this fraction = 2/(d-1).

[K,S] has kernel K(P,Q)·(ΣQ_i - ΣP_i): the "coordinate-sum-weighted" kernel.
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

    # Coordinate sum operator (anti-commutes with R)
    coord_sum = np.array([sum(s) for s in states], dtype=float)
    center = d * (m - 1) / 2.0
    S = np.diag(coord_sum - center)

    return K, R, S, states

print("=" * 95)
print("THE COMMUTATOR MECHANISM")
print("(λ_e0/λ_o0 - 1) = ⟨ψ_e0, [K,S]·ψ_o0⟩ / (λ_o0 · ⟨ψ_e0, S·ψ_o0⟩)")
print("Target: 2/(d-1)")
print("=" * 95)

for d in [2, 3, 4]:
    print(f"\n{'='*60}")
    print(f"d = {d}, target ratio = ({d+1})/({d-1}) = {(d+1)/(d-1):.4f}")
    print(f"target fraction = 2/({d-1}) = {2/(d-1):.4f}")
    print(f"{'='*60}")

    max_m = {2: 25, 3: 12, 4: 9}[d]
    for m in range(d+2, max_m+1):
        n_states = comb(m, d)
        if n_states > 3000:
            break

        K, R, S, states = build(m, d)
        n = len(states)
        K_sym = (K + K.T) / 2
        Pe = (np.eye(n) + R) / 2
        Po = (np.eye(n) - R) / 2

        ee, ve = eigh(Pe @ K_sym @ Pe)
        eo, vo = eigh(Po @ K_sym @ Po)

        idx_e = np.argsort(ee)[::-1]
        idx_o = np.argsort(eo)[::-1]

        psi_e0 = ve[:, idx_e[0]]
        psi_o0 = vo[:, idx_o[0]]
        le = ee[idx_e[0]]
        lo = eo[idx_o[0]]

        if lo < 1e-10:
            continue

        # Compute the commutator terms
        # ⟨ψ_e0, S·ψ_o0⟩
        S_psi_o = S @ psi_o0
        inner_eS = np.dot(psi_e0, S_psi_o)

        # ⟨ψ_e0, [K,S]·ψ_o0⟩ = ⟨ψ_e0, K·S·ψ_o0⟩ - ⟨ψ_e0, S·K·ψ_o0⟩
        KS_psi_o = K_sym @ S_psi_o
        SK_psi_o = S @ (K_sym @ psi_o0)  # = S · (lo · ψ_o0) = lo · S·ψ_o0

        inner_KS = np.dot(psi_e0, KS_psi_o)
        inner_SK = np.dot(psi_e0, SK_psi_o)  # = lo · inner_eS

        commutator_inner = inner_KS - inner_SK

        # The fraction
        if abs(lo * inner_eS) > 1e-15:
            fraction = commutator_inner / (lo * inner_eS)
        else:
            fraction = float('inf')

        # Verify: should equal le/lo - 1
        actual = le/lo - 1
        target = 2.0/(d-1)

        print(f"  m={m:2d}: le/lo-1 = {actual:.6f}  fraction = {fraction:.6f}  "
              f"target = {target:.4f}  |err| = {abs(fraction-actual):.2e}  "
              f"⟨e0,S·o0⟩ = {inner_eS:.4f}")

    print(f"\n  Convergence of le/lo - 1 toward 2/({d-1}) = {2/(d-1):.6f}:")

# ============================================================
# DEEPER: What determines ⟨ψ_e0, [K,S]·ψ_o0⟩ / (λ_o0·⟨ψ_e0, S·ψ_o0⟩)?
# ============================================================
print("\n\n" + "=" * 95)
print("THE DEEPER STRUCTURE: Why does the fraction → 2/(d-1)?")
print("=" * 95)

print("""
The commutator [K,S] has kernel K(P,Q)·(ΣQ_i - ΣP_i).
This is the "coordinate-sum-weighted" kernel.

In the continuum limit, S ≈ d·(m-1)/2 + m·s where s = (x₁+...+x_d)/d - 1/2
is the centered mean coordinate.

[K,S] ∝ m · [K, s] where s is the mean coordinate operator.

The fraction ⟨ψ_e0, [K,s]·ψ_o0⟩ / (λ_o0·⟨ψ_e0, s·ψ_o0⟩) should be O(1)
and equal to 2/(d-1) in the limit.

The KEY insight: s anti-commutes with R, and K·s maps the top odd mode
to the top even mode. The eigenvalue boost is controlled by how much
the kernel K "rewards" the coordinate sum direction.
""")

# Compute the overlap K·S·ψ_o0 with top even mode for larger m
print("Overlap |⟨ψ_e0, K·S·ψ_o0⟩|/||K·S·ψ_o0|| as m grows:")
for d in [2, 3]:
    print(f"\n  d={d}:")
    max_m = {2: 30, 3: 12}[d]
    for m in range(d+2, max_m+1):
        if comb(m, d) > 3000:
            break
        K, R, S, states = build(m, d)
        n = len(states)
        K_sym = (K + K.T) / 2
        Pe = (np.eye(n) + R) / 2
        Po = (np.eye(n) - R) / 2

        ee, ve = eigh(Pe @ K_sym @ Pe)
        eo, vo = eigh(Po @ K_sym @ Po)
        idx_e = np.argsort(ee)[::-1]
        idx_o = np.argsort(eo)[::-1]
        psi_e0 = ve[:, idx_e[0]]
        psi_o0 = vo[:, idx_o[0]]

        KS_psi_o = K_sym @ S @ psi_o0
        KS_even = Pe @ KS_psi_o
        norm_KS = np.linalg.norm(KS_even)
        if norm_KS > 1e-10:
            overlap = abs(np.dot(psi_e0, KS_even)) / norm_KS
            print(f"    m={m:2d}: overlap = {overlap:.6f}")
