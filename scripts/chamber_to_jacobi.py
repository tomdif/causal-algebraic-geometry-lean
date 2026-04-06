"""
chamber_to_jacobi.py — Prove the Chamber-to-Jacobi identification for general d

The R-odd sector of K_F in the continuum limit is the Jacobi matrix J_d.

PROOF STRATEGY:
1. Compute the 1D Volterra overlap matrix C (exact rational × 2/π)
2. Compute compound overlaps det(C[I,J]) for top R-odd modes
3. Build the normalized R-odd block matrix
4. Show it equals the Jacobi family J_d

The key insight: everything reduces to determinants of the Cauchy-type matrix C.
"""

from fractions import Fraction
from itertools import combinations
import numpy as np

# ============================================================
# EXACT RATIONAL COMPUTATION
# ============================================================

def C_entry(k, j):
    """
    Rational part of Volterra overlap: C_kj such that
    <u_k, v_j> = (2/π) * C_kj

    C_kk = 1/(2k-1)
    C_kj = 1/(k+j-1)  if k+j even, k≠j  [same parity]
    C_kj = 1/(k-j)    if k+j odd         [different parity]
    """
    if k == j:
        return Fraction(1, 2*k - 1)
    if (k + j) % 2 == 0:  # same parity
        return Fraction(1, k + j - 1)
    else:  # different parity
        return Fraction(1, k - j)

def det_exact(M):
    """Exact determinant of a matrix of Fractions using cofactor expansion."""
    n = len(M)
    if n == 0:
        return Fraction(1)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0]*M[1][1] - M[0][1]*M[1][0]
    # LU-style elimination for efficiency
    M = [row[:] for row in M]  # copy
    det = Fraction(1)
    for col in range(n):
        # Find pivot
        pivot_row = None
        for row in range(col, n):
            if M[row][col] != 0:
                pivot_row = row
                break
        if pivot_row is None:
            return Fraction(0)
        if pivot_row != col:
            M[col], M[pivot_row] = M[pivot_row], M[col]
            det *= -1
        det *= M[col][col]
        pivot = M[col][col]
        for row in range(col + 1, n):
            if M[row][col] != 0:
                factor = M[row][col] / pivot
                for k in range(col, n):
                    M[row][k] -= factor * M[col][k]
    return det

def compound_overlap(I, J):
    """det(C[I,J]) where I,J are tuples of 1-based indices."""
    d = len(I)
    M = [[C_entry(I[a], J[b]) for b in range(d)] for a in range(d)]
    return det_exact(M)

def sigma_tilde(I):
    """Compound SV (rational part): Π_{k∈I} 1/(2k-1)."""
    result = Fraction(1)
    for k in I:
        result *= Fraction(1, 2*k - 1)
    return result

def r_parity(I):
    """R-parity: (-1)^{Σ(i_k - k)} for 1-indexed I."""
    return sum(I[k] - (k+1) for k in range(len(I))) % 2

# ============================================================
# IDENTIFY TOP R-ODD MODES
# ============================================================

def top_r_odd_modes(d, n_modes=None):
    """
    Find the top R-odd compound modes ordered by singular value.

    For dimension d, search through compound indices I = (i₁,...,i_d)
    with 1 ≤ i₁ < i₂ < ... < i_d, and select those with odd R-parity.
    Order by σ_I (descending).
    """
    if n_modes is None:
        n_modes = d - 1  # The Jacobi block is (d-1)×(d-1)

    # Search range: indices up to 2d+10 should be plenty
    max_idx = 3*d + 5

    candidates = []
    for I in combinations(range(1, max_idx + 1), d):
        if r_parity(I) == 1:  # R-odd
            sv = sigma_tilde(I)
            candidates.append((sv, I))

    # Sort by SV descending (larger σ = more important)
    candidates.sort(key=lambda x: -float(x[0]))

    return [(sv, I) for sv, I in candidates[:n_modes]]

# ============================================================
# BUILD THE R-ODD BLOCK
# ============================================================

def build_r_odd_block(d, modes=None):
    """
    Build the R-odd block matrix of K_F in the compound Volterra basis.

    K_F = Σ_I σ_I (|φ_I⟩⟨ψ_I| + |ψ_I⟩⟨φ_I|)

    In the {φ_I} basis:
    (K_F)_{IJ} = σ_I · det(C[I,J]) + σ_J · det(C[J,I])

    For R-sector analysis, we use R-adapted vectors:
    |I±⟩ = |φ_I⟩ ± ε_I |ψ_I⟩  where ε_I = (-1)^{S(I)}

    The R-even eigenvalue in mode I: λ_I^+ = σ_I(1 + M_{II})
    The R-odd eigenvalue structure: more complex, involves cross-overlaps.
    """
    if modes is None:
        modes = top_r_odd_modes(d)

    n = len(modes)

    # The key object: the overlap matrix restricted to R-odd modes
    # For R-odd modes, the effective block comes from:
    # B_{IJ} = σ_I * M_{IJ} + σ_J * M_{JI}
    # where M_{IJ} = det(C[I,J])

    B = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        si, Ii = modes[i]
        for j in range(n):
            sj, Ij = modes[j]
            Mij = compound_overlap(Ii, Ij)
            Mji = compound_overlap(Ij, Ii)
            B[i][j] = si * Mij + sj * Mji

    return B

def print_matrix(M, label=""):
    """Print a matrix of fractions nicely."""
    if label:
        print(f"\n{label}:")
    n = len(M)
    for i in range(n):
        row = "  [" + ", ".join(f"{M[i][j]}" for j in range(n)) + "]"
        print(row)

def print_float_matrix(M, label=""):
    """Print a matrix as floats."""
    if label:
        print(f"\n{label}:")
    n = len(M)
    for i in range(n):
        row = "  [" + ", ".join(f"{float(M[i][j]):.8f}" for j in range(n)) + "]"
        print(row)

# ============================================================
# NORMALIZE AND EXTRACT JACOBI FORM
# ============================================================

def normalize_block(B, d):
    """
    The raw block B has entries σ_I·M_IJ + σ_J·M_JI.

    The top R-even eigenvalue is approximately:
    λ_even ≈ 2·σ_E·M_EE  where E = (1,...,d)

    The R-odd block eigenvalue divided by λ_even gives the Jacobi entries.
    """
    E = tuple(range(1, d+1))
    M_EE = compound_overlap(E, E)
    s_E = sigma_tilde(E)
    lambda_even = 2 * s_E * M_EE

    print(f"  Top R-even mode: E = {E}")
    print(f"  σ_E = {s_E} = {float(s_E):.10f}")
    print(f"  M_EE = det(C[E,E]) = {M_EE} = {float(M_EE):.10f}")
    print(f"  λ_even ≈ 2·σ_E·M_EE = {lambda_even} = {float(lambda_even):.10f}")

    n = len(B)
    J = [[B[i][j] / lambda_even for j in range(n)] for i in range(n)]
    return J, lambda_even

# ============================================================
# MAIN COMPUTATION
# ============================================================

print("=" * 70)
print("CHAMBER-TO-JACOBI IDENTIFICATION")
print("=" * 70)

for d in range(3, 9):
    print(f"\n{'='*70}")
    print(f"  d = {d}")
    print(f"{'='*70}")

    # Top R-even mode
    E = tuple(range(1, d+1))
    print(f"\n  R-even ground state: E = {E}")
    print(f"  σ_E = {sigma_tilde(E)}")
    print(f"  M_EE = {compound_overlap(E, E)}")

    # Top R-odd modes
    modes = top_r_odd_modes(d, d - 1)
    print(f"\n  Top {d-1} R-odd modes (by σ_I):")
    for sv, I in modes:
        print(f"    I={I}, σ_I={sv}, R-parity={r_parity(I)}")

    # Build the raw block
    B = build_r_odd_block(d, modes)
    print_matrix(B, "  Raw R-odd block B = σ_I·M_IJ + σ_J·M_JI")
    print_float_matrix(B, "  (as floats)")

    # Normalize by λ_even
    J_approx, lam_e = normalize_block(B, d)
    print_matrix(J_approx, "  Normalized block J = B/λ_even")
    print_float_matrix(J_approx, "  (as floats)")

    # Eigenvalues
    n = len(B)
    B_float = np.array([[float(B[i][j]) for j in range(n)] for i in range(n)])
    evals = sorted(np.linalg.eigvalsh(B_float), reverse=True)
    print(f"\n  R-odd block eigenvalues: {[f'{e:.10f}' for e in evals]}")
    print(f"  Top R-odd eigenvalue: {evals[0]:.10f}")
    print(f"  λ_even (approx): {float(lam_e):.10f}")
    print(f"  Ratio λ_odd/λ_even: {evals[0]/float(lam_e):.10f}")
    print(f"  Target (d-1)/(d+1) = {(d-1)/(d+1):.10f}")

    # Compare with Jacobi family
    target_lambda = Fraction(d-1, d+1)
    print(f"\n  Jacobi family target eigenvalue: {target_lambda} = {float(target_lambda):.10f}")

    # Expected Jacobi diagonal: {1/3, 2/5, ..., 2/5, 1/5}
    if d >= 3:
        jacobi_diag = [Fraction(1,3)] + [Fraction(2,5)]*(d-3) + [Fraction(1,5)]
        print(f"  Expected Jacobi diagonal: {jacobi_diag}")
        actual_diag = [J_approx[i][i] for i in range(n)]
        print(f"  Actual normalized diagonal: {actual_diag}")
        print(f"  Match: {all(abs(float(actual_diag[i]) - float(jacobi_diag[i])) < 1e-10 for i in range(n))}")

print("\n" + "=" * 70)
print("ANALYSIS COMPLETE")
print("=" * 70)

# ============================================================
# DEEPER ANALYSIS: What makes it Jacobi?
# ============================================================

print("\n\n" + "=" * 70)
print("STRUCTURAL ANALYSIS: WHY IS IT JACOBI?")
print("=" * 70)

for d in [3, 4, 5, 6]:
    print(f"\n--- d = {d} ---")
    E = tuple(range(1, d+1))
    modes = top_r_odd_modes(d, d + 2)  # Get extra modes

    n_modes = min(d + 1, len(modes))
    print(f"  Top {n_modes} R-odd modes:")

    # Compute the full overlap matrix between R-odd modes
    for i in range(n_modes):
        si, Ii = modes[i]
        overlaps = []
        for j in range(n_modes):
            sj, Ij = modes[j]
            Mij = compound_overlap(Ii, Ij)
            overlaps.append(f"M[{Ii},{Ij}]={Mij}")
        print(f"  Mode {Ii}: {', '.join(overlaps[:4])}")

# ============================================================
# KEY IDENTITY: Compute σ_I*M_IJ/σ_E*M_EE ratios
# ============================================================

print("\n\n" + "=" * 70)
print("KEY IDENTITY: Normalized overlaps")
print("=" * 70)

for d in [3, 4, 5, 6, 7]:
    print(f"\n--- d = {d} ---")
    E = tuple(range(1, d+1))
    s_E = sigma_tilde(E)
    M_EE = compound_overlap(E, E)
    norm = s_E * M_EE  # = σ_E * M_EE

    modes = top_r_odd_modes(d, d - 1)

    for i, (si, Ii) in enumerate(modes):
        M_II = compound_overlap(Ii, Ii)
        M_EI = compound_overlap(E, Ii)
        M_IE = compound_overlap(Ii, E)

        # Self-overlap ratio
        self_ratio = si * M_II / norm

        # Cross with even mode
        cross_EI = s_E * M_EI / norm  # = M_EI/M_EE
        cross_IE = si * M_IE / norm

        print(f"  Mode {Ii}:")
        print(f"    σ_I = {si}")
        print(f"    M_II = {M_II}")
        print(f"    σ_I*M_II / σ_E*M_EE = {self_ratio} = {float(self_ratio):.10f}")
        print(f"    M_EI/M_EE = {M_EI/M_EE} = {float(M_EI/M_EE):.10f}")

# ============================================================
# THE CRITICAL TEST: Is the block exactly tridiagonal?
# ============================================================

print("\n\n" + "=" * 70)
print("TRIDIAGONAL TEST")
print("=" * 70)

for d in [3, 4, 5, 6, 7]:
    print(f"\n--- d = {d} ---")

    modes = top_r_odd_modes(d, d - 1)
    B = build_r_odd_block(d, modes)
    n = len(B)

    # Check off-tridiagonal entries
    max_off = Fraction(0)
    for i in range(n):
        for j in range(n):
            if abs(i - j) > 1:
                val = abs(B[i][j])
                if val > max_off:
                    max_off = val

    print(f"  Block size: {n}×{n}")
    print(f"  Max |B[i,j]| for |i-j|>1: {max_off} = {float(max_off):.2e}")
    if max_off == 0:
        print(f"  >>> EXACTLY TRIDIAGONAL! <<<")
    else:
        print(f"  Not exactly tridiagonal (but may be approximately)")

    # Print the block
    print(f"  Diagonal: {[B[i][i] for i in range(n)]}")
    print(f"  Subdiagonal: {[B[i][i+1] for i in range(n-1)]}")
    print(f"  Superdiagonal: {[B[i+1][i] for i in range(n-1)]}")
