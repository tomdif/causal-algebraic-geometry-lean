#!/usr/bin/env python3
"""
Stage 3 — bipartite-grading gate for causal-set chiral-defect hypothesis.

CONTEXT.
  The repo's gamma_5 lives on the DOUBLED chamber Dirac
    D = [[0, A], [A^T, 0]],   gamma_5 = [[I, 0], [0, -I]]
  (ChiralDoubling.lean). For the Sharpe-style "vortex gives localized
  chiral zero mode" to even be MEANINGFUL on a 2D causal substrate,
  there must be a natural Z_2 grading Γ of events such that the
  substrate's incidence matrix A (cover relations) approximately
  anticommutes with Γ:  { Γ, A } ≈ 0.

  On regular bipartite lattices (square, hexagonal) rank-parity gives
  EXACT anticommutation. On Poisson sprinklings, covers can jump
  multiple ranks (rank(y) - rank(x) > 1 is possible for x ⋖ y), which
  breaks strict anticommutation. The question: how badly?

  This is a PRECOMMIT GATE. Published result regardless of outcome.

HYPOTHESIS (pre-registered).
  On (1+1)D Poisson sprinklings with typical densities ρ ∈ [50, 500],
  rank-parity grading Γ = diag((-1)^rank) approximately anticommutes
  with cover adjacency A:
    residual(ρ) := ||{Γ, A}||_F / ||A||_F

SUCCESS CRITERION (proceed to vortex test).
  residual(ρ) < 0.1 across ρ ∈ {50, 200, 500}.

FALSIFICATION CRITERION (stop, write up obstruction).
  residual(ρ) > 0.3 at any tested density.

AMBIGUOUS (neither clean).
  0.1 ≤ residual ≤ 0.3 — document and decide case-by-case.
"""

from __future__ import annotations

import numpy as np

RNG = np.random.default_rng(seed=20260423)


def sprinkle_strip(density: float, L_x: float = 1.0, L_t: float = 1.0,
                   rng=RNG) -> np.ndarray:
    """Poisson sprinkling in a (1+1)D Minkowski strip of size L_x × L_t.

    Space periodic (x ~ x + L_x); time open.
    Expected number of events: density * L_x * L_t.
    """
    N = rng.poisson(density * L_x * L_t)
    t = rng.uniform(0.0, L_t, size=N)
    x = rng.uniform(0.0, L_x, size=N)
    idx = np.argsort(t)
    return np.column_stack([t[idx], x[idx]])  # sorted by time


def causal_order(events: np.ndarray, L_x: float = 1.0) -> np.ndarray:
    """Boolean matrix order[i,j] = True iff event i ≤ event j causally.

    Minkowski (1+1)D:   i ≤ j  ⇔  t_j ≥ t_i  AND  |x_j - x_i|_periodic ≤ t_j - t_i.
    Self-relation excluded (strict order for clarity).
    """
    N = events.shape[0]
    t = events[:, 0]; x = events[:, 1]
    dt = t[None, :] - t[:, None]            # dt[i,j] = t_j - t_i
    dx_raw = x[None, :] - x[:, None]
    # Periodic wrap: minimum |dx| over wrap
    dx = np.abs(((dx_raw + L_x / 2) % L_x) - L_x / 2)
    order = (dt >= 0) & (dx <= dt)
    # Mask diagonal (strict)
    np.fill_diagonal(order, False)
    return order


def covers(order: np.ndarray) -> np.ndarray:
    """Cover relations: i ⋖ j iff i < j and no k with i < k < j.

    Returns boolean matrix.
    """
    # order @ order gives pairs with intermediate k: (order @ order)[i, j] > 0
    # iff exists k with i < k and k < j.  But we want STRICT order only.
    strict = order  # already strict (diag masked)
    reachable_via_intermediate = (strict.astype(np.int8) @ strict.astype(np.int8)) > 0
    return strict & ~reachable_via_intermediate


def rank_function(covers_mat: np.ndarray) -> np.ndarray:
    """Longest chain ending at each node (rank = height), topological order.

    Events are sorted by time, so we can process in order.
    """
    N = covers_mat.shape[0]
    rank = np.zeros(N, dtype=int)
    # For each node j, rank[j] = 1 + max(rank[i] for i cover-below j) if any, else 0
    for j in range(N):
        preds = np.where(covers_mat[:, j])[0]
        if len(preds) > 0:
            rank[j] = 1 + int(rank[preds].max())
    return rank


def anticommutation_residual(A: np.ndarray, Gamma_diag: np.ndarray) -> float:
    """||{Γ, A}||_F / ||A||_F, with Γ encoded as its diagonal signature vector."""
    # { Γ, A }_{ij} = Γ_i A_{ij} + A_{ij} Γ_j = (Γ_i + Γ_j) A_{ij}
    sum_signs = Gamma_diag[:, None] + Gamma_diag[None, :]
    anticomm = sum_signs * A
    num = np.linalg.norm(anticomm)
    den = np.linalg.norm(A)
    return float(num / den) if den > 0 else float("inf")


def cover_jump_distribution(covers_mat: np.ndarray, rank: np.ndarray):
    """For each cover i ⋖ j, record (rank[j] - rank[i]).  On regular lattices
    all jumps are 1; on Poisson causal sets higher jumps occur."""
    i_idx, j_idx = np.where(covers_mat)
    jumps = rank[j_idx] - rank[i_idx]
    return jumps


def one_run(density: float, L_x: float, L_t: float, rng):
    events = sprinkle_strip(density, L_x, L_t, rng=rng)
    order = causal_order(events, L_x=L_x)
    covs = covers(order)
    rank = rank_function(covs)
    Gamma = (-1.0) ** rank
    # Symmetric cover adjacency (A = covs + covs^T, so A is the bipartite
    # adjacency if rank-parity works)
    A = covs.astype(float) + covs.astype(float).T
    residual = anticommutation_residual(A, Gamma)
    jumps = cover_jump_distribution(covs, rank)
    return {
        "N_events": events.shape[0],
        "N_covers": int(covs.sum()),
        "rank_max": int(rank.max()),
        "anticomm_residual": residual,
        "jump_counts": np.bincount(jumps, minlength=max(5, int(jumps.max()) + 1)).tolist(),
        "fraction_jumps_eq_1": float((jumps == 1).mean()),
    }


def main():
    print("=" * 70)
    print("Stage 3 — bipartite-grading gate on (1+1)D Poisson causal sets")
    print("=" * 70)

    # Fix spacetime volume; vary density.  Small L to keep compute cheap.
    L_x = L_t = 1.0

    densities = [50, 200, 500]
    n_realizations = 5

    print(f"\nStrip: L_x={L_x}, L_t={L_t}, periodic in x")
    print(f"Realizations per density: {n_realizations}\n")

    summary = {}
    for rho in densities:
        residuals = []
        frac_1 = []
        Ns = []
        for r in range(n_realizations):
            out = one_run(rho, L_x, L_t, rng=RNG)
            residuals.append(out["anticomm_residual"])
            frac_1.append(out["fraction_jumps_eq_1"])
            Ns.append(out["N_events"])
        residuals = np.array(residuals)
        frac_1 = np.array(frac_1)
        Ns = np.array(Ns)
        print(f"density={rho:4d}   N_events mean={Ns.mean():.0f} ± {Ns.std():.0f}   "
              f"residual mean={residuals.mean():.4f} ± {residuals.std():.4f}   "
              f"frac(jump=1) mean={frac_1.mean():.3f}")
        summary[rho] = {
            "residual_mean": float(residuals.mean()),
            "residual_std": float(residuals.std()),
            "frac_jumps_1": float(frac_1.mean()),
        }

    print("\n" + "=" * 70)
    print("Gate decision (pre-committed thresholds)")
    print("=" * 70)
    max_res = max(s["residual_mean"] for s in summary.values())
    print(f"\nmax residual across densities: {max_res:.4f}")
    if max_res < 0.1:
        verdict = "PROCEED — rank-parity is approximately anticommuting. Safe to try vortex test."
    elif max_res > 0.3:
        verdict = "STOP — rank-parity does NOT anticommute on Poisson causal sets. Sharpe mapping has an obstruction on disordered substrates."
    else:
        verdict = "AMBIGUOUS (0.1–0.3) — document and decide manually before proceeding."
    print(f"Verdict: {verdict}")
    print("\nInterpretation hint from jump distribution:")
    print("  On regular bipartite lattices, all covers jump rank by exactly 1.")
    print("  If frac(jump=1) << 1, the 'bipartite' structure is substrate-level broken.")


if __name__ == "__main__":
    main()
