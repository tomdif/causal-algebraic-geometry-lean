"""
High-precision Galerkin for K_s via Duffy transform + Chebyshev basis.

Duffy transform: (u,v) → (ξ,η) where u = ξ(1-η), v = η.
Maps simplex Σ → square [0,1]². Jacobian = (1-η).

On the square, use tensor Chebyshev polynomials T_p(2ξ-1) T_q(2η-1).
These are optimally conditioned (spectral convergence, no ill-conditioning).

The integral operator:
(K_s f)(u,v) = (1/2)[(Kf)(u,v) + (K†f)(u,v)]

where K is the comparability indicator kernel.

Strategy: discretize K_s on Chebyshev-Gauss-Lobatto nodes on [0,1]²,
mapped to the simplex via Duffy. This gives spectral convergence.
"""
import numpy as np
from scipy.linalg import eigh
import time

def chebyshev_nodes(N):
    """Chebyshev-Gauss-Lobatto nodes on [0,1]."""
    k = np.arange(N+1)
    x = 0.5 * (1 - np.cos(np.pi * k / N))
    return x

def build_K_duffy(N):
    """Build the comparability kernel matrix on Duffy-mapped Chebyshev grid.

    Duffy: u = ξ(1-η), v = η. Jacobian = (1-η).
    Points on simplex: (u_i, v_i) = (ξ_i(1-η_j), η_j).
    Weight: w_i = w_ξ_i · w_η_j · (1-η_j).
    """
    t0 = time.time()

    # Chebyshev nodes on [0,1]
    xi = chebyshev_nodes(N)
    eta = chebyshev_nodes(N)

    # Clenshaw-Curtis weights on [0,1]
    def cc_weights(N):
        """Clenshaw-Curtis quadrature weights on [0,1]."""
        if N == 0:
            return np.array([1.0])
        theta = np.pi * np.arange(N+1) / N
        w = np.zeros(N+1)
        for k in range(N+1):
            s = 0.0
            for j in range(1, N//2 + 1):
                b = 1.0 if 2*j == N else 2.0
                s += b * np.cos(2*j*theta[k]) / (4*j*j - 1)
            w[k] = (2.0/N) * (1 - s)
            if k == 0 or k == N:
                w[k] /= 2
        return w / 2  # scale from [-1,1] to [0,1]

    w_xi = cc_weights(N)
    w_eta = cc_weights(N)

    # Build grid on simplex
    points = []
    weights = []
    grid_idx = {}  # (i,j) → index

    for i in range(N+1):
        for j in range(N+1):
            u = xi[i] * (1 - eta[j])
            v = eta[j]
            # Duffy weight includes Jacobian (1-η)
            w = w_xi[i] * w_eta[j] * (1 - eta[j])
            if w > 0 and u + v <= 1 + 1e-10:  # on simplex
                grid_idx[(i,j)] = len(points)
                points.append((u, v))
                weights.append(w)

    points = np.array(points)
    weights = np.array(weights)
    n = len(points)

    t1 = time.time()

    # Build comparability kernel
    K = np.zeros((n, n))
    for i in range(n):
        u, v = points[i]
        du = points[:, 0] - u
        dv = points[:, 1] - v
        c1 = (du <= 1e-10) & (dv >= -1e-10)
        c2 = (du >= -1e-10) & (dv <= 1e-10)
        K[i] = ((c1 | c2).astype(float)) * weights  # weighted kernel

    # Symmetrize
    K_sym = (K + K.T) / 2

    t2 = time.time()

    # Eigenvalue problem: K_sym ψ = λ_disc ψ
    # But this is the WEIGHTED eigenvalue problem.
    # The integral operator eigenvalue: λ = eigenvalue of K_sym
    # (weights are already built into K_sym)

    evals, evecs = eigh(K_sym, subset_by_index=[n-1, n-1])
    psi = evecs[:, 0]

    t3 = time.time()

    if psi[n//2] < 0:
        psi = -psi

    # Gap: γ = 1 - ⟨u+v⟩_ψ²w / ⟨1⟩_ψ²w
    psi2w = psi**2 * weights
    norm = np.sum(psi2w)
    gap = 1 - np.dot(points[:, 0] + points[:, 1], psi2w) / norm

    # Eigenvalue of the integral operator
    # The discrete eigenvalue λ_disc relates to the continuous one by:
    # λ_cont = λ_disc (since weights are already incorporated)
    # But we need to be careful: K[i,j] = K_kernel(P_i, P_j) * w_j
    # So K_sym[i,j] = (1/2)(K_kernel(i,j)*w_j + K_kernel(j,i)*w_i)
    # For comparable (i,j): K_sym[i,j] = (w_i + w_j)/2
    # This is NOT exactly the Galerkin matrix.

    # Actually, for the integral operator eigenvalue, the correct formulation is:
    # λ ψ(P_i) = Σ_j K_kernel(P_i, P_j) ψ(P_j) w_j
    # This is: K_weighted ψ = λ ψ where K_weighted[i,j] = K_kernel(i,j) * w_j

    # Let me redo with the CORRECT formulation
    K_correct = np.zeros((n, n))
    for i in range(n):
        u, v = points[i]
        du = points[:, 0] - u
        dv = points[:, 1] - v
        c1 = (du <= 1e-10) & (dv >= -1e-10)
        c2 = (du >= -1e-10) & (dv <= 1e-10)
        comparable = (c1 | c2).astype(float)
        K_correct[i] = comparable * weights  # K(P_i, P_j) * w_j

    # Symmetrize for K_s: K_s = (K + K†)/2
    # K†[i,j] = K_kernel(P_j, P_i) * w_j = comparable(j,i) * w_j = comparable(i,j) * w_j
    # So K† = K_correct for symmetric kernel! K_correct is already K_s.
    # Actually K_correct[i,j] = comparable(i,j) * w_j which is NOT symmetric in i,j.
    # K†_correct[i,j] = comparable(j,i) * w_j = comparable(i,j) * w_j = K_correct[i,j].
    # Hmm wait, K†[i,j] in the discrete sense: (K†ψ)(P_i) = Σ_j K_kernel(P_j, P_i) ψ(P_j) w_j
    # = Σ_j comparable(j,i) * ψ(P_j) * w_j = Σ_j comparable(i,j) * ψ(P_j) * w_j = (Kψ)(P_i)
    # So K = K† for the comparability kernel! It's already self-adjoint.

    # The eigenvalue of K_correct gives λ_comp directly.
    evals2, evecs2 = eigh(K_correct, subset_by_index=[n-1, n-1])
    psi2_vec = evecs2[:, 0]
    if psi2_vec[n//2] < 0:
        psi2_vec = -psi2_vec

    # But K_correct is not symmetric! For the eigenvalue, use the symmetrized version.
    K_s = (K_correct + K_correct.T) / 2
    evals3, evecs3 = eigh(K_s, subset_by_index=[n-1, n-1])
    psi3 = evecs3[:, 0]
    if psi3[n//2] < 0:
        psi3 = -psi3

    psi3_2w = psi3**2 * weights
    norm3 = np.sum(psi3_2w)
    gap3 = 1 - np.dot(points[:, 0] + points[:, 1], psi3_2w) / norm3

    # The eigenvalue of K_s = (K+K†)/2 = comparability/2
    # λ_s = evals3[-1]
    # λ_comp = 2 * λ_s
    lambda_s = evals3[-1]
    lambda_comp = 2 * lambda_s

    t4 = time.time()

    return {
        'N': N, 'n': n,
        'lambda_s': lambda_s, 'lambda_comp': lambda_comp,
        'gap': gap3,
        'times': (t1-t0, t2-t1, t3-t2, t4-t3),
    }

# ============================================================
print("=" * 75)
print("CHEBYSHEV-DUFFY SPECTRAL METHOD — K_s ON SIMPLEX")
print("=" * 75)
print()
print("Duffy: u = ξ(1-η), v = η maps simplex → [0,1]²")
print("Chebyshev-Gauss-Lobatto nodes + Clenshaw-Curtis weights")
print()

prev_lam = 0
prev_gap = 0

for N in [5, 8, 10, 12, 15, 18, 20, 25, 30, 35, 40]:
    r = build_K_duffy(N)
    dlam = abs(r['lambda_comp'] - prev_lam) if prev_lam > 0 else 0
    dgap = abs(r['gap'] - prev_gap) if prev_gap > 0 else 0

    tt = r['times']
    print(f"  N={r['N']:3d}: n={r['n']:5d}, λ_comp={r['lambda_comp']:.11f}, "
          f"γ={r['gap']:.10f}, Δλ={dlam:.2e}, Δγ={dgap:.2e} "
          f"[{sum(tt):.1f}s]")

    prev_lam = r['lambda_comp']
    prev_gap = r['gap']

print()
print(f"  Known: λ_comp ≈ 0.34916495, γ ≈ 0.27641374")
