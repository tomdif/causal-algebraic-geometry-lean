#!/usr/bin/env python3
"""
commutator_trace.py — Search for a trace-level identity giving 2/(d-1)

The commutator identity is exact but tautological (it's le/lo - 1).
We need to compute the fraction WITHOUT using eigenvectors.

Key idea: maybe trace-level quantities give 2/(d-1) exactly.
Try: tr([K,S]²), tr(K²·S²), tr(K·S·K·S), etc.
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
    return K_sym, R, S, states, n

print("=" * 95)
print("TRACE-LEVEL SEARCH FOR 2/(d-1)")
print("=" * 95)

for d in [2, 3, 4]:
    target = 2.0 / (d - 1)
    print(f"\n### d={d}, target = 2/({d-1}) = {target:.6f}")
    print(f"{'m':>3} {'tr(KS²)':>12} {'tr(K²S²)':>12} {'tr(KSKS)':>12} "
          f"{'tr([K,S]²)':>12} {'tr(K²)':>12} {'tr(S²)':>12} "
          f"{'R1':>10} {'R2':>10} {'R3':>10}")

    for m in range(d+2, min(d+15, 20)):
        if comb(m, d) > 1500:
            break
        K, R, S, states, n = build_all(m, d)
        Pe = (np.eye(n) + R) / 2
        Po = (np.eye(n) - R) / 2

        # Various trace quantities
        KS = K @ S
        SK = S @ K
        comm = KS - SK  # [K,S]
        S2 = S @ S
        K2 = K @ K

        trK = np.trace(K)
        trK2 = np.trace(K2)
        trS2 = np.trace(S2)
        trKS2 = np.trace(K @ S2)
        trK2S2 = np.trace(K2 @ S2)
        trKSKS = np.trace(KS @ KS)
        trComm2 = np.trace(comm @ comm)  # tr([K,S]²) = -tr([K,S]^T [K,S]) since [K,S] is antisymm

        # Try various ratios
        # R1 = tr([K,S]²) / (tr(K²) · tr(S²) / n)
        R1 = trComm2 / (trK2 * trS2 / n) if trK2 * trS2 != 0 else 0

        # R2 = tr([K,S]²) / (2 · tr(K²·S²) - 2·tr(KSKS))... this should be the identity
        # tr([K,S]²) = tr(KSKS) - tr(KS²K) - tr(SK²S) + tr(SKSK)
        # = 2·tr(KSKS) - 2·tr(K²S²) by cyclicity

        # R3 = something involving sectors
        # tr(P_e K S P_o S K P_e) ?
        trPeKSPoSK = np.trace(Pe @ K @ S @ Po @ S @ K)
        R2 = trPeKSPoSK / trK2 if trK2 != 0 else 0

        # Try: tr(P_e · [K,S] · P_o · [K,S]^T · P_e) / tr(P_e · K · P_o · K · P_e)
        # = eigenvalue-squared ratio in the relevant subspace?
        trSector = np.trace(Pe @ comm @ Po @ (-comm) @ Pe)
        trKsector = np.trace(Pe @ K @ Po @ K @ Pe)
        R3 = trSector / trKsector if abs(trKsector) > 1e-10 else 0

        print(f"{m:3d} {trKS2:12.2f} {trK2S2:12.2f} {trKSKS:12.2f} "
              f"{trComm2:12.2f} {trK2:12.2f} {trS2:12.2f} "
              f"{R1:10.4f} {R2:10.6f} {R3:10.6f}")

# ============================================================
# FOCUSED: tr_even(S²) / tr_odd(S²) and similar sector ratios
# ============================================================
print("\n\n" + "=" * 95)
print("SECTOR-RESOLVED TRACE RATIOS")
print("=" * 95)

for d in [2, 3, 4]:
    target = 2.0 / (d - 1)
    print(f"\n### d={d}, target = {target:.4f}")
    print(f"{'m':>3} {'tr_e(S²)/n_e':>14} {'tr_o(S²)/n_o':>14} {'ratio':>10} "
          f"{'tr_e(KS²)/tr_e(K)':>18} {'tr_o(KS²)/tr_o(K)':>18} {'diff':>10}")

    for m in range(d+2, min(d+12, 16)):
        if comb(m, d) > 1500:
            break
        K, R, S, states, n = build_all(m, d)
        Pe = (np.eye(n) + R) / 2
        Po = (np.eye(n) - R) / 2
        S2 = S @ S

        tr_e = np.trace(Pe @ K)
        tr_o = np.trace(Po @ K)
        tr_eS2 = np.trace(Pe @ S2)
        tr_oS2 = np.trace(Po @ S2)
        n_e = np.trace(Pe)
        n_o = np.trace(Po)

        tr_eKS2 = np.trace(Pe @ K @ S2)
        tr_oKS2 = np.trace(Po @ K @ S2)

        ratio_S2 = (tr_eS2/n_e) / (tr_oS2/n_o) if n_o > 0 and tr_oS2 != 0 else 0
        diff_KS2 = tr_eKS2/tr_e - tr_oKS2/tr_o if tr_e != 0 and tr_o != 0 else 0

        print(f"{m:3d} {tr_eS2/n_e:14.4f} {tr_oS2/n_o:14.4f} {ratio_S2:10.4f} "
              f"{tr_eKS2/tr_e if tr_e else 0:18.4f} {tr_oKS2/tr_o if tr_o else 0:18.4f} "
              f"{diff_KS2:10.4f}")

# ============================================================
# THE MEAN DISPLACEMENT: ⟨ΣQ_i - ΣP_i⟩ averaged over comparable pairs
# ============================================================
print("\n\n" + "=" * 95)
print("MEAN DISPLACEMENT: average (ΣQ-ΣP) over comparable pairs weighted by K")
print("=" * 95)

for d in [2, 3, 4]:
    target = 2.0 / (d - 1)
    print(f"\n### d={d}")
    for m in range(d+2, min(d+12, 16)):
        if comb(m, d) > 1500:
            break
        states = list(combinations(range(m), d))
        n = len(states)
        perms = list(permutations(range(d)))
        perm_signs = [sign_of_perm(p) for p in perms]

        # Compute mean |ΣQ-ΣP| over K-weighted pairs
        total_disp = 0.0
        total_K = 0.0
        total_disp_sq = 0.0
        for a, P in enumerate(states):
            sP = sum(P)
            for b, Q in enumerate(states):
                sQ = sum(Q)
                val = 0
                for perm, sgn in zip(perms, perm_signs):
                    Qp = tuple(Q[perm[i]] for i in range(d))
                    if all(P[i] <= Qp[i] for i in range(d)) or \
                       all(Qp[i] <= P[i] for i in range(d)):
                        val += sgn
                if val > 0:
                    total_disp += val * (sQ - sP)
                    total_disp_sq += val * (sQ - sP)**2
                    total_K += val

        mean_disp = total_disp / total_K if total_K > 0 else 0
        mean_disp_sq = total_disp_sq / total_K if total_K > 0 else 0
        rms_disp = mean_disp_sq**0.5

        # Normalize by m
        print(f"  m={m:2d}: mean_disp/m={mean_disp/m:.6f} rms_disp/m={rms_disp/m:.6f} "
              f"rms²/m²={mean_disp_sq/m**2:.6f}")
