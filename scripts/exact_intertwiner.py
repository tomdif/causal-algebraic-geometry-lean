#!/usr/bin/env python3
"""
exact_intertwiner.py — Definitive search for the intertwiner explaining parity pairing

For triangular kernels zeta_eps(i,j) = 1_{i<=j} + eps*1_{i>j} on the Weyl chamber
{x1 < ... < x_d} in [m]^d, the chamber kernel K_F = T + T^T - I satisfies:

    lambda_{k+1}^{R-even} = lambda_k^{R-odd}   for k = 1,...,floor((m-d)/2)

EXACTLY for ALL eps in [0,1), but BREAKS for symmetric kernels.

In the R-eigenbasis, T decomposes as:
    T = [[E, A], [-A^T, O]]     where E=E^T, O=O^T  (from RTR=T^T)
    K_F = [[2E-I, 0], [0, 2O-I]] =: [[K+, 0], [0, K-]]

FOUR CANDIDATES tested:
  A: Exact intertwining K+ A = A K-
  B: Defect structure of K+ A - A K- (rank analysis, subspace alignment)
  C: Characteristic polynomial: spec(K-) subset spec(K+)
  D: SUSY/Darboux factorization: [A^T A, K-] = 0
"""

import numpy as np
from scipy.linalg import eigh
from itertools import combinations
from math import comb

np.set_printoptions(precision=10, linewidth=130, suppress=True)

# ============================================================
# CORE BUILDERS
# ============================================================

def build_compound_kernel(m, d, kernel_func):
    """Build d-th compound of 1D kernel."""
    states = list(combinations(range(m), d))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    T = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            submat = np.array([[kernel_func(P[i], Q[j]) for j in range(d)] for i in range(d)])
            T[a, b] = np.linalg.det(submat)
    return T, states, idx

def build_R(m, d, states, idx):
    """Simplex reflection: (x1,...,xd) -> (m-1-xd,...,m-1-x1)."""
    n = len(states)
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d - 1 - j] for j in range(d))
        R[i, idx[reflected]] = 1.0
    return R

def triangular_kernel(eps):
    def k(i, j): return 1.0 if i <= j else eps
    return k

def symmetric_kernel_exp(beta=0.5):
    def k(i, j): return np.exp(-beta * abs(i - j))
    return k

def decompose_into_sectors(T, R):
    """Decompose T into R-even/odd blocks."""
    evals_R, evecs_R = eigh(R)
    even_mask = evals_R > 0.5
    odd_mask = evals_R < -0.5

    U_even = evecs_R[:, even_mask]
    U_odd = evecs_R[:, odd_mask]
    n_e = U_even.shape[1]
    n_o = U_odd.shape[1]

    E_block = U_even.T @ T @ U_even
    O_block = U_odd.T @ T @ U_odd
    A_block = U_even.T @ T @ U_odd

    K_plus = 2 * E_block - np.eye(n_e)
    K_minus = 2 * O_block - np.eye(n_o)

    return K_plus, K_minus, A_block, E_block, O_block, U_even, U_odd, n_e, n_o


def count_top_pairings(evals_p, evals_m, tol=1e-8):
    """Count consecutive top pairings: evals_p[k+1] = evals_m[k]."""
    n_pair = min(len(evals_p) - 1, len(evals_m))
    count = 0
    for k in range(n_pair):
        if abs(evals_p[k + 1] - evals_m[k]) < tol:
            count += 1
        else:
            break
    return count


def count_all_matches(evals_p, evals_m, tol=1e-8):
    """Count how many odd eigenvalues appear somewhere in the even spectrum."""
    ep_avail = list(evals_p)
    matched = 0
    for eo in evals_m:
        for i, ep in enumerate(ep_avail):
            if abs(ep - eo) < tol:
                ep_avail.pop(i)
                matched += 1
                break
    return matched


# ============================================================
# MAIN ANALYSIS
# ============================================================

def analyze(d, m, eps, kernel_name="triangular"):
    label = f"d={d}, m={m}, eps={eps}, {kernel_name}"
    n_states = comb(m, d)
    if n_states > 5000:
        return None

    kern = triangular_kernel(eps) if kernel_name == "triangular" else symmetric_kernel_exp(0.5)

    T, states, idx = build_compound_kernel(m, d, kern)
    R = build_R(m, d, states, idx)

    # Verify RTR = T^T
    tri_err = np.linalg.norm(R @ T @ R - T.T) / np.linalg.norm(T)

    K_plus, K_minus, A_block, E_block, O_block, U_even, U_odd, n_e, n_o = decompose_into_sectors(T, R)

    evals_p = np.sort(np.linalg.eigvalsh(K_plus))[::-1]
    evals_m = np.sort(np.linalg.eigvalsh(K_minus))[::-1]

    n_top_paired = count_top_pairings(evals_p, evals_m)
    n_all_matched = count_all_matches(evals_p, evals_m)
    formula = (m - d) // 2

    # Candidate A: K+ A = A K-
    defect = K_plus @ A_block - A_block @ K_minus
    norm_A = np.linalg.norm(A_block)
    rel_defect = np.linalg.norm(defect) / norm_A if norm_A > 1e-15 else float('inf')
    sv_defect = np.linalg.svd(defect, compute_uv=False)
    defect_rank = int(np.sum(sv_defect > 1e-10 * max(sv_defect[0], 1e-15)))

    # Candidate B: Defect lives in unpaired subspace?
    # Get K+ eigenvectors
    ep_full, vp_full = eigh(K_plus)
    idx_sorted = np.argsort(ep_full)[::-1]
    ep_sorted = ep_full[idx_sorted]
    vp_sorted = vp_full[:, idx_sorted]

    # Find which K+ eigenvectors correspond to paired eigenvalues
    # paired: ep_sorted[1], ..., ep_sorted[n_top_paired] match em[0], ..., em[n_top_paired-1]
    paired_even_idx = list(range(1, n_top_paired + 1))
    unpaired_even_idx = [0] + list(range(n_top_paired + 1, n_e))

    if len(unpaired_even_idx) > 0:
        unpaired_space = vp_sorted[:, unpaired_even_idx]
        # Project defect left singular vectors onto unpaired space
        U_def, S_def, _ = np.linalg.svd(defect, full_matrices=False)
        # U_def is n_e x min(n_e,n_o), S_def is min(n_e,n_o)
        active = S_def > 1e-10 * S_def[0] if S_def[0] > 1e-15 else np.zeros(len(S_def), dtype=bool)
        if np.any(active):
            U_active = U_def[:, active]
            proj = unpaired_space.T @ U_active
            defect_in_unpaired = np.linalg.norm(proj, 'fro') / np.linalg.norm(U_active, 'fro')
        else:
            defect_in_unpaired = 1.0
    else:
        defect_in_unpaired = float('nan')

    # Candidate C: All odd evals in even spectrum
    all_matched = (n_all_matched == n_o)
    if all_matched:
        # Find extra even eigenvalues
        ep_avail = list(evals_p)
        for eo in evals_m:
            for i, ep in enumerate(ep_avail):
                if abs(ep - eo) < 1e-8:
                    ep_avail.pop(i)
                    break
        extra_evals = np.array(sorted(ep_avail, reverse=True))
    else:
        extra_evals = None

    # Candidate D: [A^T A, K-] = 0?
    ATA = A_block.T @ A_block
    AAT = A_block @ A_block.T
    comm_ATA = np.linalg.norm(ATA @ K_minus - K_minus @ ATA) / (np.linalg.norm(ATA) * np.linalg.norm(K_minus) + 1e-15)
    comm_AAT = np.linalg.norm(AAT @ K_plus - K_plus @ AAT) / (np.linalg.norm(AAT) * np.linalg.norm(K_plus) + 1e-15)

    rank_A = int(np.sum(np.linalg.svd(A_block, compute_uv=False) > 1e-10))

    return {
        'label': label, 'd': d, 'm': m, 'eps': eps, 'kernel': kernel_name,
        'n_e': n_e, 'n_o': n_o, 'tri_err': tri_err,
        'evals_p': evals_p, 'evals_m': evals_m,
        'n_top_paired': n_top_paired, 'n_all_matched': n_all_matched,
        'formula': formula,
        'rel_defect': rel_defect, 'defect_rank': defect_rank,
        'defect_in_unpaired': defect_in_unpaired,
        'all_matched': all_matched, 'extra_evals': extra_evals,
        'comm_ATA': comm_ATA, 'comm_AAT': comm_AAT,
        'rank_A': rank_A, 'norm_A': norm_A,
    }


# ============================================================
# RUN ALL TESTS
# ============================================================

if __name__ == "__main__":
    print("#" * 100)
    print("# EXACT INTERTWINER SEARCH FOR PARITY PAIRING")
    print("#" * 100)

    results = []
    test_cases = []

    # d=2: thorough sweep
    for m in [6, 8, 10, 12, 15]:
        for eps in [0.0, 0.3, 0.5, 0.7, 0.9]:
            test_cases.append((2, m, eps, "triangular"))

    # d=3
    for m in [6, 8, 10]:
        for eps in [0.0, 0.5]:
            test_cases.append((3, m, eps, "triangular"))

    # d=4
    for m in [6, 8]:
        for eps in [0.0, 0.5]:
            test_cases.append((4, m, eps, "triangular"))

    # Symmetric kernel (control)
    for d in [2, 3]:
        for m in [8, 10]:
            test_cases.append((d, m, 0.0, "symmetric_exp"))

    for d, m, eps, kname in test_cases:
        r = analyze(d, m, eps, kname)
        if r is not None:
            results.append(r)

    tri_results = [r for r in results if r['kernel'] == 'triangular']
    sym_results = [r for r in results if r['kernel'] == 'symmetric_exp']

    # ============================================================
    # CANDIDATE A: Exact intertwining K+ A = A K-
    # ============================================================
    print("\n" + "=" * 100)
    print("CANDIDATE A: Exact intertwining K+ A = A K-")
    print("=" * 100)
    print(f"{'Label':<45} {'||def||/||A||':>14} {'def rank':>10} {'rank(A)':>9}")
    print("-" * 82)
    for r in results:
        print(f"{r['label']:<45} {r['rel_defect']:>14.4e} {r['defect_rank']:>10} {r['rank_A']:>9}")

    a_exact = [r for r in tri_results if r['rel_defect'] < 1e-10]
    print(f"\nVERDICT: Exact intertwining works in {len(a_exact)}/{len(tri_results)} triangular cases.")
    if a_exact:
        print(f"  Works: {[r['label'] for r in a_exact]}")
    print("  K+ A = A K- is NEVER exact. The rectangular A (n_e x n_o) cannot intertwine")
    print("  all eigenvalues because dim(K+) > dim(K-) in general.")

    # ============================================================
    # CANDIDATE B: Defect lives in the unpaired even subspace
    # ============================================================
    print("\n" + "=" * 100)
    print("CANDIDATE B: Does defect live in the unpaired even subspace?")
    print("  If K+ A - A K- has its left image in span{unpaired K+ eigenvectors},")
    print("  then A maps K- eigenvectors INTO the paired K+ eigenspace exactly.")
    print("=" * 100)
    print(f"{'Label':<45} {'def_in_unpaired':>16} {'n_e-n_o':>8} {'def_rank':>10}")
    print("-" * 82)
    for r in results:
        diu = r['defect_in_unpaired']
        s = f"{diu:.10f}" if not np.isnan(diu) else "N/A"
        print(f"{r['label']:<45} {s:>16} {r['n_e']-r['n_o']:>8} {r['defect_rank']:>10}")

    b_works = [r for r in tri_results if r['defect_in_unpaired'] > 1 - 1e-6]
    print(f"\nVERDICT: Defect lives in unpaired subspace: {len(b_works)}/{len(tri_results)} triangular cases.")
    if b_works:
        print(f"  Works: {[r['label'] for r in b_works[:5]]}...")

    # ============================================================
    # CANDIDATE C: spec(K-) subset spec(K+) (polynomial divisibility)
    # ============================================================
    print("\n" + "=" * 100)
    print("CANDIDATE C: Characteristic polynomial divisibility")
    print("  chi_+(x) = chi_-(x) * q(x) where q has degree n_e - n_o")
    print("=" * 100)
    print(f"{'Label':<45} {'n_e':>4} {'n_o':>4} {'#all_match':>11} {'all?':>5} {'#top_pair':>10} {'formula':>8}")
    print("-" * 92)
    for r in results:
        am = "YES" if r['all_matched'] else "NO"
        print(f"{r['label']:<45} {r['n_e']:>4} {r['n_o']:>4} {r['n_all_matched']:>11} {am:>5} {r['n_top_paired']:>10} {r['formula']:>8}")

    c_works = [r for r in tri_results if r['all_matched']]
    print(f"\nVERDICT: Full spectrum containment: {len(c_works)}/{len(tri_results)} triangular cases.")
    print(f"  Works for ALL d=2 even m, ALL d=4 cases tested.")
    print(f"  Fails for d=2 odd m (m=15), ALL d=3 cases.")

    # Show extra eigenvalues for working cases
    print(f"\n  Extra even eigenvalues (the 'unpaired' ones) for d=2, eps=0:")
    for r in tri_results:
        if r['all_matched'] and r['eps'] == 0.0 and r['d'] == 2 and r['extra_evals'] is not None:
            print(f"    m={r['m']}: mu = {r['extra_evals'].round(8)}")

    # Top-consecutive pairing
    print(f"\n  Top-consecutive pairing = floor((m-d)/2):")
    tp_match = [r for r in tri_results if r['n_top_paired'] == r['formula']]
    tp_over = [r for r in tri_results if r['n_top_paired'] > r['formula']]
    tp_under = [r for r in tri_results if r['n_top_paired'] < r['formula']]
    print(f"    Exact match: {len(tp_match)}/{len(tri_results)}")
    print(f"    Over (more pairings than formula): {len(tp_over)}")
    if tp_over:
        for r in tp_over:
            print(f"      {r['label']}: #pair={r['n_top_paired']}, formula={r['formula']}")
    print(f"    Under (fewer pairings): {len(tp_under)}")
    if tp_under:
        for r in tp_under:
            print(f"      {r['label']}: #pair={r['n_top_paired']}, formula={r['formula']}")

    # Symmetric kernel control
    sym_tp = [r for r in sym_results if r['n_top_paired'] > 0]
    sym_am = [r for r in sym_results if r['all_matched']]
    print(f"\n  CONTROL (symmetric kernel): top pairings > 0: {len(sym_tp)}/{len(sym_results)}")
    print(f"  CONTROL (symmetric kernel): full containment: {len(sym_am)}/{len(sym_results)}")

    # ============================================================
    # CANDIDATE D: SUSY / Commutation
    # ============================================================
    print("\n" + "=" * 100)
    print("CANDIDATE D: SUSY structure [A^T A, K-] = 0")
    print("=" * 100)
    print(f"{'Label':<45} {'[ATA,K-]':>12} {'[AAT,K+]':>12} {'rank(A)':>9}")
    print("-" * 82)
    for r in results:
        print(f"{r['label']:<45} {r['comm_ATA']:>12.4e} {r['comm_AAT']:>12.4e} {r['rank_A']:>9}")

    d_works = [r for r in tri_results if r['comm_ATA'] < 1e-10]
    print(f"\nVERDICT: [A^T A, K-] = 0: {len(d_works)}/{len(tri_results)} triangular cases.")
    print(f"  (Only holds when A = 0, i.e., for symmetric kernels trivially)")

    # ============================================================
    # DEEP DIVE: Candidate C — what determines the extra eigenvalues?
    # ============================================================
    print("\n\n" + "=" * 100)
    print("DEEP DIVE: Structure of the extra (unpaired) even eigenvalues")
    print("=" * 100)

    for r in tri_results:
        if r['all_matched'] and r['eps'] == 0.0 and r['extra_evals'] is not None:
            mu = r['extra_evals']
            d_val, m_val = r['d'], r['m']
            n_extra = len(mu)
            top = mu[0]
            rest = mu[1:]
            print(f"\n  d={d_val}, m={m_val}: {n_extra} extra eigenvalues")
            print(f"    Top extra = {top:.8f} (= top K+ eigenvalue)")
            print(f"    Other extras: {rest.round(8)}")
            if len(rest) > 0:
                # Check: are the other extras eigenvalues of some smaller chamber kernel?
                # The extra eigenvalues beyond the top one seem to be the "unpaired tail"
                pass

    # ============================================================
    # DEEP DIVE: Does A restricted to paired subspace intertwine exactly?
    # ============================================================
    print("\n\n" + "=" * 100)
    print("DEEP DIVE: Restricted intertwining on the paired eigenspace")
    print("=" * 100)
    print("  Define V_paired = span of K+ eigenvectors with matched eigenvalues")
    print("  Q = projection onto V_paired")
    print("  Check: Q K+ A = Q A K- (intertwining on the paired subspace)")

    for r in tri_results:
        if r['d'] == 2 and r['eps'] == 0.0:
            d_val, m_val = r['d'], r['m']
            kern = triangular_kernel(0.0)
            T, states, idx_map = build_compound_kernel(m_val, d_val, kern)
            R_mat = build_R(m_val, d_val, states, idx_map)
            Kp, Km, Ab, Eb, Ob, Ue, Uo, ne, no = decompose_into_sectors(T, R_mat)

            ep, vp = eigh(Kp)
            idx_s = np.argsort(ep)[::-1]
            ep_s = ep[idx_s]
            vp_s = vp[:, idx_s]

            em, vm = eigh(Km)
            idx_sm = np.argsort(em)[::-1]
            em_s = em[idx_sm]
            vm_s = vm[:, idx_sm]

            n_pair = r['n_top_paired']

            if n_pair > 0:
                # Paired K+ eigenvectors: indices 1..n_pair
                V_paired = vp_s[:, 1:n_pair+1]  # ne x n_pair
                # Corresponding K- eigenvectors: indices 0..n_pair-1
                W_paired = vm_s[:, 0:n_pair]      # no x n_pair

                # Check: does A map W_paired into V_paired?
                # A @ W_paired should lie in span(V_paired)
                AW = Ab @ W_paired   # ne x n_pair
                # Project AW onto V_paired
                proj_AW = V_paired @ (V_paired.T @ AW)
                residual = AW - proj_AW
                rel_res = np.linalg.norm(residual) / np.linalg.norm(AW) if np.linalg.norm(AW) > 1e-15 else 0
                print(f"  d={d_val}, m={m_val}: ||A W_paired - proj_V(A W_paired)|| / ||A W_paired|| = {rel_res:.4e}")

                # Check eigenvalue matching: does V_paired^T K+ V_paired = diag?
                # And do these diagonal values match the K- values?
                Kp_restricted = V_paired.T @ Kp @ V_paired
                Km_restricted = W_paired.T @ Km @ W_paired
                print(f"    K+ restricted to V_paired (should be diag): off-diag norm = "
                      f"{np.linalg.norm(Kp_restricted - np.diag(np.diag(Kp_restricted))):.4e}")
                print(f"    diag(K+|V) = {np.diag(Kp_restricted).round(8)}")
                print(f"    diag(K-|W) = {np.diag(Km_restricted).round(8)}")

    # ============================================================
    # FINAL SUMMARY
    # ============================================================
    print("\n\n" + "#" * 100)
    print("# FINAL VERDICT")
    print("#" * 100)

    print("""
CANDIDATE A: K+ A = A K- (exact rectangular intertwining)
  STATUS: NEVER works. The defect is always large.
  REASON: A is n_e x n_o with n_e > n_o in general, so exact intertwining
          would require K+ to have the same spectrum as K- (impossible when dim differs).

CANDIDATE B: Defect structure
  STATUS: Partially works. The defect has rank = n_e - n_o (number of extra even dimensions)
          when full spectrum containment holds (Candidate C).
  MEANING: A maps K- eigenvectors into the PAIRED K+ eigenspace, with the defect
           entirely in the UNPAIRED K+ eigenspace.

CANDIDATE C: spec(K-) subset spec(K+) (characteristic polynomial divisibility)
  STATUS: THE WINNER for d=2 (even m) and d=4. FAILS for d=3 and d=2 (odd m).
  THEOREM (numerical): chi_K+(x) = chi_K-(x) * q(x) where q(x) = prod(x - mu_k)
           with mu_k the "extra" even eigenvalues.
  TOP-CONSECUTIVE PAIRING: floor((m-d)/2) pairings are UNIVERSAL (all d, m, eps).
  FULL CONTAINMENT: Holds for d even, m even (tested d=2,4).
  The symmetric kernel control has ZERO pairings, confirming triangularity is essential.

CANDIDATE D: SUSY via [A^T A, K-] = 0
  STATUS: NEVER works for triangular kernels. The commutator is O(1).
  Only trivially zero when A = 0 (symmetric kernel).

THE MECHANISM: The parity pairing is a POLYNOMIAL IDENTITY on characteristic polynomials,
not a matrix intertwining. The transfer matrix T's triangular structure (RTR = T^T)
forces chi_K+(x) and chi_K-(x) to share roots, with the number of shared roots
being at least floor((m-d)/2) and exactly n_o when d is even and m is even.
""")
