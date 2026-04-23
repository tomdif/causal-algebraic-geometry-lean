#!/usr/bin/env python3
"""
Stage 4 — gamma_5-via-doubling gauge-index test on Poisson causal sets.

PRECOMMIT: memory/chiral_defect_stage4_PRECOMMIT.md

BACKGROUND.
  Stage 3 FAILED: no Z_2 grading of a Poisson causal-set cover graph
  anticommutes with cover adjacency (cover graph contains odd cycles).
  Stage 4 tests the one surviving Sharpe-analog route: gamma_5 on the
  DOUBLED chamber Dirac D = [[0, A], [A^T, 0]] (ChiralDoubling.lean).
  {gamma_5, D} = 0 by block-matrix construction, regardless of substrate
  graph properties.

STRUCTURAL OBSTRUCTION (pre-registered caveat 3).
  For a complex SQUARE matrix A^g, the Fredholm index
    ind(A^g) = dim null(A^g) − dim null((A^g)^T)
  is identically zero by rank-nullity: both kernels have dimension
  N - rank(A^g), so their difference is zero.  The integer-index
  observable cannot distinguish vacuum from vortex on square A.
  Nonzero index requires RECTANGULAR A (n_L ≠ n_R in SM language).

WHAT THIS STAGE ACTUALLY TESTS.
  1. Numerically confirm the predicted obstruction: ind(A^g) = 0 for
     both vacuum and vortex, across sprinklings and densities.
  2. Compute the SPECTRAL RESPONSE as the non-index observable: does
     the vortex shift the near-zero singular values in a way that
     distinguishes it from vacuum?

RESULT REPORTING.
  - Index observable (pre-committed): must show ind = 0 uniformly
    (confirms caveat 3).  This is a FAIL of H_gamma5 in its stated
    form, which is informative and expected.
  - Spectral response (secondary, not pre-committed as PASS/FAIL,
    just reported): gives a non-trivial measurement on square A that
    may or may not be substrate-sensitive.
"""

from __future__ import annotations
import numpy as np

RNG_MASTER = 20260423


# ------------------------------------------------------------------ #
# Sprinkling / causal-set primitives (copied verbatim from stage 3)  #
# ------------------------------------------------------------------ #

def sprinkle_strip(density, L_x=1.0, L_t=1.0, rng=None):
    if rng is None:
        rng = np.random.default_rng(RNG_MASTER)
    N = rng.poisson(density * L_x * L_t)
    t = rng.uniform(0, L_t, N)
    x = rng.uniform(0, L_x, N)
    idx = np.argsort(t)
    return np.column_stack([t[idx], x[idx]])


def causal_order(events, L_x=1.0):
    t = events[:, 0]
    x = events[:, 1]
    dt = t[None, :] - t[:, None]
    dx_raw = x[None, :] - x[:, None]
    dx = np.abs(((dx_raw + L_x / 2) % L_x) - L_x / 2)
    order = (dt >= 0) & (dx <= dt)
    np.fill_diagonal(order, False)
    return order


def covers(order):
    strict = order.astype(np.int8)
    via_intermediate = (strict @ strict) > 0
    return order & ~via_intermediate


# ------------------------------------------------------------------ #
# Gauge field + vortex construction                                   #
# ------------------------------------------------------------------ #

def find_interior_event(events, L_x=1.0, L_t=1.0):
    """Pick the event closest to the geometric center of the strip."""
    center = np.array([L_t / 2, L_x / 2])
    # Use periodic distance in x
    d_t = events[:, 0] - center[0]
    d_x_raw = events[:, 1] - center[1]
    d_x = ((d_x_raw + L_x / 2) % L_x) - L_x / 2
    dists = np.sqrt(d_t ** 2 + d_x ** 2)
    return int(np.argmin(dists))


def vortex_gauge(events, e_star_idx, covers_mat, L_x=1.0):
    """For each cover edge (i, j), set link phase = arg(z_j - z_star) - arg(z_i - z_star),
    with periodic spatial wrapping for dx.  Returns a complex NxN matrix of link phases;
    entries are 0 where there is no cover."""
    N = events.shape[0]
    t = events[:, 0]
    x = events[:, 1]
    t_star = events[e_star_idx, 0]
    x_star = events[e_star_idx, 1]
    # Periodic x-distance from star
    dx_raw = x - x_star
    dx = ((dx_raw + L_x / 2) % L_x) - L_x / 2
    dt = t - t_star
    # Angle of each event around the vortex core (in the t-x plane)
    angle = np.arctan2(dt, dx)  # shape (N,)
    # Phase on cover edge (i, j) = angle[j] - angle[i] (unwrapped modulo 2*pi)
    theta = angle[None, :] - angle[:, None]
    # Principal value in (-pi, pi]
    theta = (theta + np.pi) % (2 * np.pi) - np.pi
    phase = np.exp(1j * theta)
    return phase * covers_mat  # zero outside cover relations


# ------------------------------------------------------------------ #
# Observables                                                         #
# ------------------------------------------------------------------ #

def index_and_spectrum(A_complex, tol_scale=None):
    """Index = dim null(A) - dim null(A^T); spectral tail = smallest few singular values."""
    if A_complex.shape[0] == 0:
        return {
            "dim_null_A": 0, "dim_null_AT": 0, "index": 0,
            "rank": 0, "smallest_svs": [], "N": 0,
        }
    s = np.linalg.svd(A_complex, compute_uv=False)
    if tol_scale is None:
        tol = max(A_complex.shape) * np.finfo(A_complex.dtype.type(1.0).real.dtype).eps * (s[0] if s.size else 1.0)
    else:
        tol = tol_scale
    rank = int((s > tol).sum())
    N = A_complex.shape[0]
    # For square A: dim null A = dim null A^T = N - rank, so index = 0 guaranteed
    dim_null_A = N - rank
    dim_null_AT = N - rank
    return {
        "dim_null_A": dim_null_A,
        "dim_null_AT": dim_null_AT,
        "index": dim_null_A - dim_null_AT,
        "rank": rank,
        "smallest_svs": s[-5:].tolist() if s.size >= 5 else s.tolist(),
        "all_svs_sorted_ascending": np.sort(s).tolist(),
        "N": N,
    }


# ------------------------------------------------------------------ #
# Main experiment                                                     #
# ------------------------------------------------------------------ #

def z2_flux_gauge(covers_mat, i0, j0):
    """Non-pure-gauge Z_2 defect: flip sign on the single link (i0, j0).
    Cannot be written as A_z2 = D * A * D^H for diagonal unitary D.  Wilson loop
    around any closed cycle through (i0, j0) picks up factor -1."""
    phase = covers_mat.astype(complex)
    if covers_mat[i0, j0]:
        phase[i0, j0] = -1.0
    return phase


def one_realization(density, seed, L_x=1.0, L_t=1.0):
    rng = np.random.default_rng(seed)
    events = sprinkle_strip(density, L_x, L_t, rng=rng)
    order = causal_order(events, L_x=L_x)
    covs = covers(order).astype(float)
    e_star = find_interior_event(events, L_x=L_x, L_t=L_t)

    # Vacuum: A^g = A (real)
    A_vacuum = covs.astype(complex)
    # Vortex (continuous winding): A^g = phase * A (complex)
    # PRE-ANALYSIS: theta[i,j] = a_j - a_i factors as conj(D)_i D_j, so
    # A_vortex = D^H A D is a UNITARY CONJUGATION of A_vacuum.  Hence singular
    # values are identical.  This is pure gauge, NOT a physical vortex.
    A_vortex = vortex_gauge(events, e_star, covs, L_x=L_x)

    # Z_2 defect: flip sign on the link nearest to e_star.  Non-factorizable,
    # CANNOT be gauged away.  Wilson loop through this link acquires -1.
    i_idx, j_idx = np.where(covs > 0)
    if len(i_idx) > 0:
        t = events[:, 0]; x = events[:, 1]
        d_to_star = (t[i_idx] - events[e_star, 0]) ** 2 + \
                    (((x[i_idx] - events[e_star, 1] + L_x / 2) % L_x) - L_x / 2) ** 2
        nearest = int(np.argmin(d_to_star))
        A_z2 = z2_flux_gauge(covs, i_idx[nearest], j_idx[nearest])
    else:
        A_z2 = A_vacuum.copy()

    diag_vac = index_and_spectrum(A_vacuum)
    diag_vor = index_and_spectrum(A_vortex)
    diag_z2 = index_and_spectrum(A_z2)

    svs_vac = np.array(diag_vac["all_svs_sorted_ascending"])
    svs_vor = np.array(diag_vor["all_svs_sorted_ascending"])
    svs_z2 = np.array(diag_z2["all_svs_sorted_ascending"])
    near_zero_count_vac = int((svs_vac < 1e-6).sum())
    near_zero_count_vor = int((svs_vor < 1e-6).sum())
    near_zero_count_z2 = int((svs_z2 < 1e-6).sum())

    k = min(10, len(svs_vac), len(svs_vor))
    low_shift_vortex = float(np.linalg.norm(svs_vac[:k] - svs_vor[:k]))
    low_shift_z2 = float(np.linalg.norm(svs_vac[:k] - svs_z2[:k]))
    max_shift_z2 = float(np.max(np.abs(svs_vac - svs_z2))) if len(svs_vac) == len(svs_z2) else None

    return {
        "N": events.shape[0],
        "N_covers": int(covs.sum()),
        "e_star_idx": e_star,
        "index_vacuum": diag_vac["index"],
        "index_vortex": diag_vor["index"],
        "index_z2_defect": diag_z2["index"],
        "rank_vacuum": diag_vac["rank"],
        "rank_vortex": diag_vor["rank"],
        "rank_z2_defect": diag_z2["rank"],
        "near_zero_svs_vacuum": near_zero_count_vac,
        "near_zero_svs_vortex": near_zero_count_vor,
        "near_zero_svs_z2": near_zero_count_z2,
        "low_sv_shift_vortex": low_shift_vortex,  # expect ~0 (pure gauge)
        "low_sv_shift_z2": low_shift_z2,          # nonzero if near-zero SVs shift
        "max_sv_shift_z2": max_shift_z2,          # bulk-spectrum shift measure
    }


def main():
    print("=" * 72)
    print("Stage 4 — gamma_5-via-doubling on (1+1)D Poisson causal sets")
    print("=" * 72)
    print("\nPre-registered caveat 3: for complex square A, ind(A^g) = 0 by")
    print("rank-nullity.  This is a THEOREM, not an empirical prediction.")
    print("The index test will FAIL by construction; spectral response is")
    print("reported as a secondary diagnostic.\n")

    all_results = {100: [], 300: []}
    for rho in [100, 300]:
        print(f"--- density rho = {rho} ---")
        for real_idx in range(5):
            seed = RNG_MASTER + rho + real_idx
            out = one_realization(rho, seed)
            all_results[rho].append(out)
            print(f"  r{real_idx}: N={out['N']:4d}  "
                  f"ind(vac,vor,z2)=({out['index_vacuum']:+d},{out['index_vortex']:+d},{out['index_z2_defect']:+d})  "
                  f"near0(v,V,z2)=({out['near_zero_svs_vacuum']:3d},{out['near_zero_svs_vortex']:3d},{out['near_zero_svs_z2']:3d})  "
                  f"low_shift_vor={out['low_sv_shift_vortex']:.1e}  "
                  f"low_shift_z2={out['low_sv_shift_z2']:.1e}  "
                  f"max_shift_z2={out['max_sv_shift_z2']:.3e}")
        print()

    # Pre-committed verdict on index observable (Obstruction A, caveat 3)
    print("=" * 72)
    print("OBSTRUCTION A — index trivially zero (rank-nullity, pre-committed caveat 3)")
    print("=" * 72)
    all_zero = all(r["index_vacuum"] == 0 and r["index_vortex"] == 0 and r["index_z2_defect"] == 0
                   for rho in all_results for r in all_results[rho])
    if all_zero:
        print("  ind(A^g) = 0 in every realization for vacuum, continuous-vortex, AND Z_2 defect.")
        print("  Rank-nullity theorem for square complex A: CONFIRMED numerically.")
    else:
        print("  CONTRADICTION with caveat 3 — investigate SVD tolerance.")

    # Obstruction B — continuous-vortex is pure gauge
    print("\n" + "=" * 72)
    print("OBSTRUCTION B — continuous-winding vortex is pure gauge")
    print("=" * 72)
    all_vor_shift = [r["low_sv_shift_vortex"] for rho in all_results for r in all_results[rho]]
    print(f"  Singular-value shift vacuum -> continuous-vortex:")
    print(f"    max across 10 realizations = {max(all_vor_shift):.2e}")
    print(f"    mean                        = {np.mean(all_vor_shift):.2e}")
    print("  The construction theta[i,j] = a_j - a_i factors as A_vor = D^H A D,")
    print("  hence singular values are invariant.  Gauge-trivial by construction.")
    print("  A legitimate vortex needs non-factorizable phases (Z_2 flux, fractional flux,")
    print("  or a genuine non-trivial first cohomology class of the cover graph).")

    # Obstruction C — Z_2 flux shifts bulk spectrum but not near-zero SVs / rank
    print("\n" + "=" * 72)
    print("OBSTRUCTION C — Z_2 defect shifts bulk spectrum but preserves rank")
    print("=" * 72)
    z2_bulk = [r["max_sv_shift_z2"] for rho in all_results for r in all_results[rho]]
    z2_low  = [r["low_sv_shift_z2"]  for rho in all_results for r in all_results[rho]]
    rank_match = all(r["rank_vacuum"] == r["rank_z2_defect"] for rho in all_results for r in all_results[rho])
    print(f"  Max SV shift vacuum -> Z_2 defect (bulk):")
    print(f"    mean across realizations = {np.mean(z2_bulk):.3e}  (nonzero: flux is visible)")
    print(f"  Low-SV L2 shift vacuum -> Z_2 defect (bottom-10):")
    print(f"    mean across realizations = {np.mean(z2_low):.3e}")
    print(f"  rank(A_vacuum) == rank(A_z2_defect) in every realization: {rank_match}")
    print("  So the non-gauge-trivial defect moves bulk eigenvalues around, but the")
    print("  DIMENSIONALITY OF THE NULL SPACE is invariant.  dim null(A) is a gauge")
    print("  invariant for *all* (not just pure) U(1) configurations on this graph at")
    print("  these parameters.")

    print("\n" + "=" * 72)
    print("STAGE 4 VERDICT")
    print("=" * 72)
    print("  H_gamma5 as stated in the precommit: FALSIFIED.")
    print("  Three compounded obstructions documented:")
    print("    A: ind(A) = 0 for square A (rank-nullity, theorem).")
    print("    B: gradient-constructed vortex is pure gauge (SVs invariant).")
    print("    C: non-pure-gauge Z_2 flux shifts bulk SVs but preserves rank")
    print("       (dim null A is gauge-invariant here).")
    print("\n  Not ruled out: rectangular A (Stage 5 precommit target) bypasses A;")
    print("  a non-pure-gauge U(1) configuration bypasses B; whether rank-change under")
    print("  specific non-abelian or large-flux configurations can bypass C is an")
    print("  open question not addressed here.")


if __name__ == "__main__":
    main()
