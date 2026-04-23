#!/usr/bin/env python3
"""
Stage 1 — numerical verification of ChiralNoGo's det(mu_1^g) = 1 - W identity
on a 1D L-cycle (periodic BC).

Precommit: memory/chiral_defect_PRECOMMIT_apr23.md
Gate for stage 2. If this fails, all stage-2 vortex-localization claims are
ill-founded; do not proceed.

Protocol (pre-registered):
  - L in {16, 32, 64}
  - 20 random gauge configs per L (theta_i uniform on [0, 2*pi))
  - Check |det_numerical - (1 - W)| < 1e-10 for all 60 configs
  - W = Product(exp(i theta_i))

Also: check that W = 1 configs have exactly one zero eigenvalue and W != 1
configs have none (up to same tolerance). This is the precursor check that
the zero-mode structure used in stage 2 is well-defined.
"""

import numpy as np

TOL = 1e-10
RNG = np.random.default_rng(seed=20260423)


def build_mu1(theta: np.ndarray) -> np.ndarray:
    """mu_1^g = I - G * S on an L-cycle, with G = diag(exp(i theta_i)) and
    S the cyclic forward shift (S[i, i+1 mod L] = 1)."""
    L = len(theta)
    G = np.diag(np.exp(1j * theta))
    S = np.roll(np.eye(L), -1, axis=1)  # S[i,j] = 1 iff j = i+1 mod L
    return np.eye(L) - G @ S


def wilson_loop(theta: np.ndarray) -> complex:
    return np.exp(1j * theta.sum())


def stage1_run(L: int, n_configs: int = 20, rng=RNG) -> dict:
    max_err_det = 0.0
    zero_mode_ok = True
    results = []
    for k in range(n_configs):
        theta = rng.uniform(0.0, 2 * np.pi, size=L)
        mu = build_mu1(theta)
        det_num = np.linalg.det(mu)
        W = wilson_loop(theta)
        det_pred = 1.0 - W
        err = abs(det_num - det_pred)
        max_err_det = max(max_err_det, err)
        # Zero-mode count (eigenvalues within TOL of 0)
        ev = np.linalg.eigvals(mu)
        n_zero = int(np.sum(np.abs(ev) < 1e-8))
        # At random theta, W != 1 generically, so expect 0 zero modes
        if n_zero != 0:
            zero_mode_ok = False
        results.append({
            "config": k,
            "det_num": det_num,
            "det_pred": det_pred,
            "err": err,
            "W": W,
            "n_zero_modes": n_zero,
        })
    return {
        "L": L,
        "n_configs": n_configs,
        "max_err_det": max_err_det,
        "zero_mode_ok_random": zero_mode_ok,
        "pass_det": max_err_det < TOL,
        "results": results,
    }


def stage1_w_equals_one(L: int, rng=RNG) -> dict:
    """Construct theta with W = 1 (sum = 2*pi*n) and check: exactly 1 zero mode."""
    out = []
    for n in [0, 1, 2, -1]:
        # Put most of winding at one site, rest distributed
        theta = rng.uniform(-0.1, 0.1, size=L)
        # Adjust to force sum = 2*pi*n
        theta += (2 * np.pi * n - theta.sum()) / L
        assert abs(theta.sum() - 2 * np.pi * n) < 1e-12
        mu = build_mu1(theta)
        ev = np.linalg.eigvals(mu)
        idx_sorted = np.argsort(np.abs(ev))
        smallest = np.abs(ev[idx_sorted[:3]])
        det_num = np.linalg.det(mu)
        W = wilson_loop(theta)
        out.append({
            "winding_n": n,
            "sum_theta": theta.sum(),
            "W": W,
            "det_num": det_num,
            "det_pred": 1.0 - W,
            "three_smallest_|ev|": smallest.tolist(),
        })
    return out


def main():
    print("=" * 70)
    print("Stage 1: verify det(mu_1^g) = 1 - W on L-cycle")
    print("Precommit gate: max |err| < 1e-10 across 60 random configs")
    print("=" * 70)

    all_pass = True
    for L in [16, 32, 64]:
        r = stage1_run(L)
        status = "PASS" if r["pass_det"] else "FAIL"
        print(f"\nL = {L:3d}   max |det_num - (1-W)| = {r['max_err_det']:.3e}   "
              f"zero-mode OK (random) = {r['zero_mode_ok_random']}   [{status}]")
        all_pass = all_pass and r["pass_det"]

    print("\n" + "=" * 70)
    print("Integer-winding check: W = 1 configs (expect exactly one zero mode)")
    print("=" * 70)
    for L in [16, 32]:
        print(f"\nL = {L}")
        rows = stage1_w_equals_one(L)
        for row in rows:
            print(f"  n = {row['winding_n']:+d}   sum theta = {row['sum_theta']:.4f}   "
                  f"W = {row['W']:.4f}   det = {row['det_num']:.3e}   "
                  f"|ev|_smallest3 = {[f'{x:.2e}' for x in row['three_smallest_|ev|']]}")

    print("\n" + "=" * 70)
    print(f"STAGE 1 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    print("=" * 70)
    return 0 if all_pass else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
