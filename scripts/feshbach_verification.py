"""
feshbach_verification.py — Verify the Feshbach identification numerically

For the discrete chamber K_F at finite m:
1. Compute the R-odd sector
2. Take top d-1 eigenmodes as V_d
3. Compute Feshbach map F(λ*) = A - λ*I - B(C-λ*I)^{-1}B^T
4. Verify F(λ*) ≈ J_d - λ*I as m → ∞

This confirms the bottleneck lemma before we formalize.
"""
import numpy as np
from itertools import combinations
from fractions import Fraction

def build_chamber_kernel(d, m):
    """Build K_F on the Weyl chamber {x₁ < ... < x_d} ⊂ [m]^d."""
    # Enumerate chamber states
    states = list(combinations(range(m), d))
    n = len(states)

    # Transfer matrix T(i,j) = 1 if i <= j
    def T(i, j):
        return 1.0 if i <= j else 0.0

    # K_F(P,Q) = det(T(p_a, q_b)) + det(T(q_a, p_b))
    # This is Λ^d(T) + Λ^d(T)^T evaluated at chamber points
    K = np.zeros((n, n))
    for ip, P in enumerate(states):
        for iq, Q in enumerate(states):
            # Forward: det(T(p_a, q_b))
            mat_fwd = np.array([[T(P[a], Q[b]) for b in range(d)] for a in range(d)])
            # Backward: det(T(q_a, p_b))
            mat_bwd = np.array([[T(Q[a], P[b]) for b in range(d)] for a in range(d)])
            K[ip, iq] = np.linalg.det(mat_fwd) + np.linalg.det(mat_bwd)
            if ip == iq:
                K[ip, iq] -= 1  # Subtract identity

    return K, states

def build_reflection(d, m, states):
    """Build the R-reflection matrix: R(x₁,...,x_d) = (m-1-x_d,...,m-1-x₁)."""
    n = len(states)
    state_to_idx = {s: i for i, s in enumerate(states)}
    R = np.zeros((n, n))
    for i, P in enumerate(states):
        RP = tuple(sorted([m - 1 - P[d - 1 - k] for k in range(d)]))
        if RP in state_to_idx:
            j = state_to_idx[RP]
            R[i, j] = 1.0
    return R

def extract_r_odd_sector(K, R):
    """Project onto the R-odd sector."""
    n = K.shape[0]
    P_odd = (np.eye(n) - R) / 2  # R-odd projector

    # Get basis of R-odd sector
    evals, evecs = np.linalg.eigh(P_odd)
    odd_mask = evals > 0.5  # eigenvalue 1 = R-odd
    odd_basis = evecs[:, odd_mask]

    # Project K onto R-odd sector
    K_odd = odd_basis.T @ K @ odd_basis
    return K_odd, odd_basis

def feshbach_map(K_odd, n_visible, lam_star):
    """Compute Feshbach map F(λ*) for the top n_visible modes.

    K_odd = [[A, B], [B^T, C]] on V ⊕ Q
    F(λ*) = A - λ*I - B(C - λ*I)^{-1}B^T
    """
    n = K_odd.shape[0]

    # Diagonalize K_odd to identify top eigenmodes
    evals, evecs = np.linalg.eigh(K_odd)
    idx = np.argsort(-evals)  # descending
    evals = evals[idx]
    evecs = evecs[:, idx]

    # Top n_visible eigenmodes form V_d
    V_basis = evecs[:, :n_visible]
    Q_basis = evecs[:, n_visible:]

    # Block decomposition
    A = V_basis.T @ K_odd @ V_basis  # n_visible × n_visible
    B = V_basis.T @ K_odd @ Q_basis  # n_visible × (n-n_visible)
    C = Q_basis.T @ K_odd @ Q_basis  # (n-n_visible) × (n-n_visible)

    # Feshbach map
    n_complement = n - n_visible
    C_shifted = C - lam_star * np.eye(n_complement)

    try:
        C_inv = np.linalg.inv(C_shifted)
        F = A - lam_star * np.eye(n_visible) - B @ C_inv @ B.T
        return F, A, B, C, evals
    except np.linalg.LinAlgError:
        return None, A, B, C, evals

def jacobi_defect(d, lam_star):
    """Build J_d - λ*I for the Jacobi family."""
    n = d - 1
    J = np.zeros((n, n))

    # Diagonal
    diag = [1/3] + [2/5] * (d - 3) + [1/5] if d >= 3 else []
    for i in range(n):
        J[i, i] = diag[i] - lam_star

    # Subdiagonal
    C_int = 3 / (10 * (d - 2)) if d > 2 else 0
    x = lam_star - 2/5 - C_int
    b1_sq = 1 / (5 * (d + 1))
    C_last = lam_star - 1/5

    if n >= 2:
        b1 = np.sqrt(abs(b1_sq))
        J[0, 1] = b1
        J[1, 0] = b1

    if n >= 3:
        b_int = np.sqrt(abs(C_int * x))
        for k in range(1, n - 1):
            J[k, k+1] = b_int
            J[k+1, k] = b_int

        # Last coupling
        b_last_sq = C_last * x
        if b_last_sq > 0:
            b_last = np.sqrt(b_last_sq)
            J[n-2, n-1] = b_last
            J[n-1, n-2] = b_last

    return J

# ============================================================
# MAIN COMPUTATION
# ============================================================

print("=" * 70)
print("FESHBACH VERIFICATION: F_d(λ*) → J_d - λ*I as m → ∞")
print("=" * 70)

for d in [3, 4, 5]:
    lam_star = (d - 1) / (d + 1)
    J_def = jacobi_defect(d, lam_star)

    print(f"\n{'='*70}")
    print(f"  d = {d},  λ* = {d-1}/{d+1} = {lam_star:.6f}")
    print(f"{'='*70}")

    print(f"\n  Target: J_d - λ*I =")
    n_vis = d - 1
    for i in range(n_vis):
        row = "    [" + ", ".join(f"{J_def[i,j]:+.6f}" for j in range(n_vis)) + "]"
        print(row)

    for m in [8, 12, 16, 20, 25, 30]:
        if m <= d:
            continue
        try:
            K, states = build_chamber_kernel(d, m)
            R = build_reflection(d, m, states)
            K_odd, odd_basis = extract_r_odd_sector(K, R)

            F, A, B, C, evals_odd = feshbach_map(K_odd, d - 1, lam_star)

            if F is None:
                print(f"\n  m={m}: C-λ*I singular (complement not invertible)")
                continue

            # Compare F with J_def
            error = np.max(np.abs(F - J_def))

            # Also get the top few odd eigenvalues
            top_even_eval = np.max(np.linalg.eigvalsh(K))
            ratio = top_even_eval / evals_odd[0] if evals_odd[0] > 0 else float('inf')

            print(f"\n  m={m}: (chamber size {len(states)}, odd sector {K_odd.shape[0]})")
            print(f"    Top odd eigenvalues: {evals_odd[:3]}")
            print(f"    le/lo ratio: {ratio:.6f}  (target: {(d+1)/(d-1):.6f})")
            print(f"    Feshbach F(λ*):")
            for i in range(n_vis):
                row = "      [" + ", ".join(f"{F[i,j]:+.6f}" for j in range(n_vis)) + "]"
                print(row)
            print(f"    Max |F - (J_d-λ*I)|: {error:.2e}")

        except Exception as e:
            print(f"\n  m={m}: Error — {e}")

# ============================================================
# CONVERGENCE ANALYSIS
# ============================================================

print("\n\n" + "=" * 70)
print("CONVERGENCE OF FESHBACH DIAGONAL ENTRIES")
print("=" * 70)

for d in [3, 4, 5]:
    lam_star = (d - 1) / (d + 1)
    print(f"\n  d={d}, λ*={lam_star:.4f}")
    print(f"  Target diagonal: {[1/3-lam_star] + [2/5-lam_star]*(d-3) + [1/5-lam_star]}")

    for m in [10, 15, 20, 25, 30]:
        if m <= d:
            continue
        try:
            K, states = build_chamber_kernel(d, m)
            R = build_reflection(d, m, states)
            K_odd, _ = extract_r_odd_sector(K, R)
            F, _, _, _, _ = feshbach_map(K_odd, d - 1, lam_star)
            if F is not None:
                diag = [F[i,i] for i in range(d-1)]
                print(f"    m={m}: diag(F) = {[f'{x:.6f}' for x in diag]}")
        except:
            pass
