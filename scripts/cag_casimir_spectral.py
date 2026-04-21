"""
Spectral-route test for Casimir 1/a scaling in 2D CAG.

For the 4-connected grid Hasse graph Laplacian on [a] × [L] with Dirichlet
BC on all boundaries, eigenvalues are closed-form:
    λ_{n,k} = 4 sin²(nπ/(2(a+1))) + 4 sin²(kπ/(2(L+1)))
for n = 1..a, k = 1..L.

Analogous to vacuum energy between plates, define
    E(a, L) = (1/2) Σ_{n,k} √λ_{n,k}.

In continuum 1+1 Casimir, E/L → ε_bulk · a + ε_edge + ε_Casimir/a + ...
with ε_Casimir = -π/24 for a massless scalar between plates.

On the lattice, take L → ∞ (large enough to trust thermodynamic limit).
Compute f(a) = lim E(a, L)/L. Fit f(a) = ε_bulk·a + ε_edge + (residual).
The residual should scale as 1/a if the Casimir signature is there.
"""

import math

import numpy as np


def grid_eigs(a: int, L: int):
    """Eigenvalues of the Dirichlet Hasse Laplacian on [a] × [L] (exact)."""
    n = np.arange(1, a + 1, dtype=np.float64)
    k = np.arange(1, L + 1, dtype=np.float64)
    lam_x = 4.0 * np.sin(n * np.pi / (2.0 * (a + 1))) ** 2
    lam_y = 4.0 * np.sin(k * np.pi / (2.0 * (L + 1))) ** 2
    return lam_x[:, None] + lam_y[None, :]


def mode_sum(a: int, L: int) -> float:
    """E(a, L) = (1/2) Σ √λ."""
    return 0.5 * float(np.sum(np.sqrt(grid_eigs(a, L))))


def energy_density(a: int, L: int) -> float:
    """E(a, L) / L, the per-transverse-unit mode sum."""
    return mode_sum(a, L) / L


def main():
    print("Spectral test: grid Laplacian mode sums on [a] × [L].\n")

    # For each a, find f(a) = lim_{L→∞} E(a, L)/L by extrapolating in 1/L.
    a_values = list(range(2, 25))
    L_big = [50, 100, 200, 400, 800]

    # Report convergence at large L for a reference a to pick L.
    print("Convergence of E(a, L)/L vs L at a = 5:")
    for L in L_big:
        print(f"  L={L:>5}: E/L = {energy_density(5, L):.6f}")
    print()

    # Adopt L = 800 as the "thermodynamic limit" approximation. Verify stability.
    L_inf = 800
    f_values = {a: energy_density(a, L_inf) for a in a_values}

    print(f"f(a) := E(a, {L_inf})/{L_inf} for a = 2..{max(a_values)}:")
    for a in a_values:
        print(f"  a={a:>3}: f = {f_values[a]:.6f}")
    print()

    # Fit f(a) = eps_bulk · a + eps_edge + eps_Casimir/a + O(1/a²)
    # Use large-a subset so Casimir is subleading
    large_a = [a for a in a_values if a >= 10]
    xs = np.array(large_a, dtype=np.float64)
    ys = np.array([f_values[a] for a in large_a])

    # Fit with three terms: eps_bulk * a + eps_edge + eps_Cas / a
    A = np.vstack([xs, np.ones_like(xs), 1.0 / xs]).T
    params, *_ = np.linalg.lstsq(A, ys, rcond=None)
    eps_bulk, eps_edge, eps_Cas = params
    pred = A @ params
    r2 = 1 - np.sum((ys - pred) ** 2) / np.sum((ys - ys.mean()) ** 2)

    print(f"Fit f(a) = ε_bulk · a + ε_edge + ε_Casimir / a  on a ≥ 10:")
    print(f"  ε_bulk     = {eps_bulk:.6f}")
    print(f"  ε_edge     = {eps_edge:.6f}")
    print(f"  ε_Casimir  = {eps_Cas:.6f}")
    print(f"  R²         = {r2:.8f}")
    print(f"  Reference (continuum 1+1 massless scalar): ε_Casimir = -π/24 = {-math.pi/24:.6f}")
    print()

    # Residuals: how well does the fit describe the data?
    print("Residuals (f(a) - fit) as a function of a:")
    print(f"{'a':>3} {'f(a)':>12} {'fit(a)':>12} {'residual':>12} {'resid · a':>12} {'resid · a²':>12}")
    for a in a_values:
        f_val = f_values[a]
        fit_val = eps_bulk * a + eps_edge + eps_Cas / a
        resid = f_val - fit_val
        print(f"{a:>3} {f_val:>12.6f} {fit_val:>12.6f} {resid:>12.6e} "
              f"{resid*a:>12.6e} {resid*a*a:>12.6e}")
    print()

    # Alternative: fit with 1/a² term too
    A2 = np.vstack([xs, np.ones_like(xs), 1.0 / xs, 1.0 / xs ** 2]).T
    params2, *_ = np.linalg.lstsq(A2, ys, rcond=None)
    eps_bulk2, eps_edge2, eps_Cas2, eps_next = params2
    pred2 = A2 @ params2
    r22 = 1 - np.sum((ys - pred2) ** 2) / np.sum((ys - ys.mean()) ** 2)
    print(f"Extended fit with 1/a² term:")
    print(f"  ε_bulk     = {eps_bulk2:.6f}")
    print(f"  ε_edge     = {eps_edge2:.6f}")
    print(f"  ε_Casimir  = {eps_Cas2:.6f}")
    print(f"  coeff(1/a²)= {eps_next:.6f}")
    print(f"  R²         = {r22:.10f}")


if __name__ == "__main__":
    main()
