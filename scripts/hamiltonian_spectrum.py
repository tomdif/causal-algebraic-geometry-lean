"""
Module 1 / File 1: Hamiltonian Spectrum from the d=2 Transfer Operator

Compute H = -log(T) where T is the symmetrized comparability operator on the
simplex Sigma = {(u,v) : u,v >= 0, u+v <= 1}.

Method: Chebyshev-Duffy spectral discretization of K_s = (K + K^dag)/2.
  - Duffy transform maps simplex to [0,1]^2
  - Chebyshev-Gauss-Lobatto nodes with Clenshaw-Curtis weights
  - Discrete kernel matrix: K_s[i,j] = comparable(i,j) * w_j
  - Top eigenvalues of K_s give the spectrum
  - Energy levels: E_n = -log(lambda_n / lambda_1)  [DERIVABLE]
  - Mass gap: E_1 = -log(lambda_2/lambda_1)  [DERIVABLE]

Classification:
  - Eigenvalues of T: DERIVABLE (exact computation from kernel)
  - Energy spectrum E_n = -log(lambda_n/lambda_1): DERIVABLE (definition of H)
  - Mass gap identification with 1/xi: DERIVABLE (spectral theory)
"""

import numpy as np
from scipy.linalg import eigh
import time

# ============================================================================
# Chebyshev-Duffy spectral discretization
# ============================================================================

def chebyshev_nodes(N):
    """Chebyshev-Gauss-Lobatto nodes on [0,1]."""
    k = np.arange(N + 1)
    return 0.5 * (1 - np.cos(np.pi * k / N))


def cc_weights(N):
    """Clenshaw-Curtis quadrature weights on [0,1]."""
    if N == 0:
        return np.array([1.0])
    theta = np.pi * np.arange(N + 1) / N
    w = np.zeros(N + 1)
    for k in range(N + 1):
        s = 0.0
        for j in range(1, N // 2 + 1):
            b = 1.0 if 2 * j == N else 2.0
            s += b * np.cos(2 * j * theta[k]) / (4 * j * j - 1)
        w[k] = (2.0 / N) * (1 - s)
        if k == 0 or k == N:
            w[k] /= 2
    return w / 2  # scale from [-1,1] to [0,1]


def build_simplex_grid(N):
    """Build Chebyshev grid on simplex via Duffy transform.
    Duffy: u = xi*(1-eta), v = eta. Jacobian = (1-eta).
    Returns points, weights arrays."""
    xi = chebyshev_nodes(N)
    eta = chebyshev_nodes(N)
    w_xi = cc_weights(N)
    w_eta = cc_weights(N)

    points = []
    weights = []
    for i in range(N + 1):
        for j in range(N + 1):
            u = xi[i] * (1 - eta[j])
            v = eta[j]
            w = w_xi[i] * w_eta[j] * (1 - eta[j])
            if w > 0 and u + v <= 1 + 1e-10:
                points.append((u, v))
                weights.append(w)

    return np.array(points), np.array(weights)


def build_kernel_matrix(points, weights):
    """Build the symmetrized comparability kernel matrix K_s.

    Two points are comparable in the mixed partial order if
    (u' <= u and v' >= v) or (u' >= u and v' <= v).

    K_s[i,j] = comparable(i,j) * w_j (weighted kernel for eigenvalue problem).
    Then symmetrize: K_sym = (K + K^T)/2.
    """
    n = len(points)
    K = np.zeros((n, n))
    for i in range(n):
        u, v = points[i]
        du = points[:, 0] - u
        dv = points[:, 1] - v
        # Comparable: (du <= 0 and dv >= 0) or (du >= 0 and dv <= 0)
        c1 = (du <= 1e-10) & (dv >= -1e-10)
        c2 = (du >= -1e-10) & (dv <= 1e-10)
        comparable = (c1 | c2).astype(float)
        K[i] = comparable * weights

    # Symmetrize
    K_sym = (K + K.T) / 2
    return K_sym


def solve_spectrum(N, n_evals=15):
    """Solve for top eigenvalues of K_s on simplex with grid size N."""
    points, weights = build_simplex_grid(N)
    n = len(points)
    K_sym = build_kernel_matrix(points, weights)

    # Get top n_evals eigenvalues
    n_want = min(n_evals, n)
    evals, evecs = eigh(K_sym, subset_by_index=[n - n_want, n - 1])

    # Sort decreasing
    idx = np.argsort(evals)[::-1]
    evals = evals[idx]
    evecs = evecs[:, idx]

    return evals, evecs, points, weights


# ============================================================================
# Main computation
# ============================================================================

def main():
    N = 30  # grid parameter (gives ~961 points on simplex)
    n_levels = 12
    print("=" * 70)
    print("HAMILTONIAN SPECTRUM FROM d=2 TRANSFER OPERATOR")
    print("=" * 70)
    print()

    t0 = time.time()
    points, weights = build_simplex_grid(N)
    n_pts = len(points)
    print(f"  Grid: N = {N}, {n_pts} points on simplex (Chebyshev-Duffy)")

    K_sym = build_kernel_matrix(points, weights)
    t1 = time.time()
    print(f"  Kernel matrix: {n_pts} x {n_pts}, built in {t1-t0:.2f}s")

    # Get top eigenvalues
    n_want = min(n_levels, n_pts)
    evals, evecs = eigh(K_sym, subset_by_index=[n_pts - n_want, n_pts - 1])
    idx = np.argsort(evals)[::-1]
    evals = evals[idx]
    evecs = evecs[:, idx]
    t2 = time.time()
    print(f"  Eigensolve: {t2-t1:.2f}s")
    print()

    # lambda_comp = eigenvalue of comparability kernel
    # The kernel K_s = (K + K^dag)/2 where K is the indicator kernel
    # For comparability indicator kernel, lambda_comp = eigenvalue of K_s
    lambda_1 = evals[0]
    print(f"  Ground state: lambda_1 = {lambda_1:.12f}")
    print(f"  (Expected: lambda_comp ~ 0.349)")
    print()

    # ---- Energy levels [DERIVABLE] ----
    print("-" * 70)
    print("ENERGY SPECTRUM  [DERIVABLE]")
    print("-" * 70)
    print()
    print("  H = -log(T),  E_n = -log(lambda_n / lambda_1)")
    print("  Energy is measured relative to the ground state (E_1 = 0).")
    print()

    energies = []
    print(f"  {'n':>3}   {'lambda_n':>16}   {'lambda_n/lambda_1':>18}   "
          f"{'E_n':>12}   {'Delta E':>10}")
    print("  " + "-" * 66)

    for k in range(n_want):
        lam = evals[k]
        ratio = lam / lambda_1 if lambda_1 > 0 else 0
        if lam > 0 and lambda_1 > 0:
            E = -np.log(lam / lambda_1)
        else:
            E = float('inf')
        energies.append(E)
        dE = E - energies[k - 1] if k > 0 else 0.0
        print(f"  {k+1:3d}   {lam:16.12f}   {ratio:18.12f}   "
              f"{E:12.6f}   {dE:10.6f}")

    # ---- Mass gap [DERIVABLE] ----
    print()
    print("-" * 70)
    print("MASS GAP  [DERIVABLE]")
    print("-" * 70)
    print()

    if len(energies) >= 2 and energies[1] > 0:
        mass_gap = energies[1]  # E_2 - E_1 = E_2 since E_1 = 0
        xi = 1.0 / mass_gap
        print(f"  Mass gap = E_2 - E_1 = -log(lambda_2/lambda_1)")
        print(f"           = -log({evals[1]:.10f} / {evals[0]:.10f})")
        print(f"           = {mass_gap:.10f}")
        print()
        print(f"  Correlation length xi = 1/mass_gap = {xi:.10f}")
        print()
        print(f"  Expected: xi ~ 0.716 => mass gap ~ 1.396")
        print(f"  Note: exact value depends on boundary conditions and operator variant.")
    print()

    # ---- Energy level spacing analysis ----
    print("-" * 70)
    print("ENERGY LEVEL SPACING  [DERIVABLE]")
    print("-" * 70)
    print()

    if len(energies) >= 4:
        print(f"  {'n':>3}   {'E_n':>12}   {'E_n/E_2':>10}   "
              f"{'gap E_n-E_{n-1}':>16}   {'gap ratio':>10}")
        print("  " + "-" * 58)
        for k in range(n_want):
            ratio_E2 = energies[k] / energies[1] if energies[1] > 0 else 0
            gap_k = energies[k] - energies[k - 1] if k > 0 else 0
            gap_prev = energies[k - 1] - energies[k - 2] if k > 1 else 0
            gap_ratio = gap_k / gap_prev if gap_prev > 0 else 0
            print(f"  {k+1:3d}   {energies[k]:12.6f}   {ratio_E2:10.5f}   "
                  f"{gap_k:16.6f}   {gap_ratio:10.5f}")

        print()
        print("  Gap ratios characterize the potential shape:")
        print("    Constant ratio => exponential (hydrogen-like)")
        print("    Ratio = 1     => linear (harmonic oscillator)")
        print("    Decreasing    => confining potential")

    print()

    # ---- Convergence check ----
    print("-" * 70)
    print("CONVERGENCE CHECK")
    print("-" * 70)
    print()

    for Nk in [15, 20, 25, 30]:
        tk0 = time.time()
        ev_k, _, _, _ = solve_spectrum(Nk, n_evals=5)
        tk1 = time.time()
        if len(ev_k) >= 2 and ev_k[0] > 0 and ev_k[1] > 0:
            gap_k = -np.log(ev_k[1] / ev_k[0])
            print(f"  N={Nk:2d}: lambda_1={ev_k[0]:.10f}, "
                  f"lambda_2={ev_k[1]:.10f}, gap={gap_k:.8f}  [{tk1-tk0:.1f}s]")

    print()

    # ---- Ground state wavefunction on simplex ----
    print("-" * 70)
    print("GROUND STATE WAVEFUNCTION  [DERIVABLE]")
    print("-" * 70)
    print()

    psi0 = evecs[:, 0]
    if psi0[np.argmax(np.abs(psi0))] < 0:
        psi0 = -psi0

    # Normalize
    norm2 = np.sum(psi0**2 * weights)
    psi0_norm = psi0 / np.sqrt(norm2)

    # Expectation values
    u_exp = np.sum(psi0_norm**2 * points[:, 0] * weights)
    v_exp = np.sum(psi0_norm**2 * points[:, 1] * weights)
    gap = 1 - u_exp - v_exp

    print(f"  <u>_{{psi_0}} = {u_exp:.8f}")
    print(f"  <v>_{{psi_0}} = {v_exp:.8f}")
    print(f"  gamma = 1 - <u+v> = {gap:.8f}")
    print(f"  (Expected: gamma ~ 0.276)")
    print()

    # Show wavefunction values at key points
    print("  psi_0 at selected points:")
    print(f"  {'u':>6}  {'v':>6}  {'psi_0':>14}")
    print("  " + "-" * 30)
    sample_idx = np.linspace(0, len(psi0) - 1, 20, dtype=int)
    for i in sample_idx:
        u, v = points[i]
        print(f"  {u:6.3f}  {v:6.3f}  {psi0_norm[i]:14.8f}")

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("  The Hamiltonian H = -log(T) defines the energy spectrum of the")
    print("  d=2 causal algebraic geometry model on the simplex.")
    print()
    print("  - Eigenvalues lambda_n of T:        DERIVABLE (spectral method)")
    print("  - Energy levels E_n = -log(lam_n):  DERIVABLE (definition)")
    print("  - Mass gap = E_2 - E_1:             DERIVABLE (spectral gap)")
    print("  - Correlation length xi = 1/gap:    DERIVABLE (spectral theory)")
    print("  - Hamiltonian H as generator:       DERIVABLE (T = e^{-H})")
    print()


if __name__ == "__main__":
    main()
