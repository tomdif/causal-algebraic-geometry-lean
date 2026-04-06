#!/usr/bin/env python3
"""
continuum_eigenvalue_ratio.py — Compute the CONTINUUM eigenvalue ratio
using the explicit Volterra overlap matrix.

K_F in the compound SVD basis has entries:
  H_{IJ} = σ_I · M_{JI} + σ_J · M_{IJ} - δ_{IJ}

where M_{IJ} = det(A[I,J]) and A_kj = ⟨u_k, v_j⟩ (explicit Volterra overlaps).

This is the EXACT continuum limit. The eigenvalue ratio should be (d+1)/(d-1)
as the basis size (truncation) increases.
"""

import numpy as np
from itertools import combinations
from math import pi

def A_overlap(k, j):
    """Volterra overlap A_kj = ⟨u_k, v_j⟩. 1-indexed."""
    if k == j:
        return 2.0 / ((2*k - 1) * pi)
    if (k + j) % 2 == 0:  # same parity
        return 2.0 / ((k + j - 1) * pi)
    else:  # different parity
        return 2.0 / ((j - k) * pi)

def compound_sv(I):
    """Compound singular value σ_I = Π σ_k for k in I."""
    return np.prod([2.0 / ((2*k - 1) * pi) for k in I])

def compound_overlap(I, J):
    """M_IJ = det(A[I,J])."""
    d = len(I)
    mat = np.array([[A_overlap(I[a], J[b]) for b in range(d)] for a in range(d)])
    return np.linalg.det(mat)

def R_parity(I):
    """R-parity of compound mode I: (-1)^{S(I)} where S = sum of (k-1) for k in I."""
    S = sum(k - 1 for k in I)
    return (-1)**S

print("=" * 90)
print("CONTINUUM EIGENVALUE RATIO FROM COMPOUND SVD OVERLAP MATRIX")
print("=" * 90)

for d in [2, 3, 4]:
    target = (d + 1) / (d - 1)
    print(f"\n### d={d}, target = ({d+1})/({d-1}) = {target:.6f}")

    # Generate compound modes: d-element subsets of {1, 2, ..., N}
    for N in [6, 8, 10, 14, 20]:
        if d > 3 and N > 10:
            continue
        subsets = list(combinations(range(1, N + 1), d))
        ns = len(subsets)

        if ns > 500:
            continue

        # Compute compound SVs, overlaps, R-parities
        svs = [compound_sv(I) for I in subsets]
        pars = [R_parity(I) for I in subsets]

        # Build K_F matrix: H_{ab} = σ_a · M_{ba} + σ_b · M_{ab} - δ_{ab}
        # But this is in the LEFT compound basis {φ_I}.
        # The φ_I are orthonormal, so this is the matrix of K_F.
        H = np.zeros((ns, ns))
        for a in range(ns):
            for b in range(ns):
                M_ba = compound_overlap(subsets[b], subsets[a])
                M_ab = compound_overlap(subsets[a], subsets[b])
                H[a, b] = svs[a] * M_ba + svs[b] * M_ab
                if a == b:
                    H[a, b] -= 1.0

        # Build R-sector projectors
        # R maps φ_I to ε_I ψ_I. In the φ basis, R is NOT diagonal.
        # But we can build R from the overlap: R_{IJ} = ε_I · M_{IJ}
        # (since R φ_I = ε_I ψ_I, and ⟨φ_J, ψ_I⟩ = M_{JI})
        # Wait: ⟨φ_J, R φ_I⟩ = ε_I ⟨φ_J, ψ_I⟩ = ε_I M_{JI}.
        R_mat = np.zeros((ns, ns))
        for a in range(ns):
            for b in range(ns):
                R_mat[a, b] = pars[b] * compound_overlap(subsets[a], subsets[b])

        # Check R² ≈ I
        R2_err = np.max(np.abs(R_mat @ R_mat - np.eye(ns)))

        # R-sector eigenvalues
        Pe = (np.eye(ns) + R_mat) / 2
        Po = (np.eye(ns) - R_mat) / 2

        He = Pe @ H @ Pe
        Ho = Po @ H @ Po

        ee = np.sort(np.linalg.eigvalsh((He + He.T)/2))[::-1]
        eo = np.sort(np.linalg.eigvalsh((Ho + Ho.T)/2))[::-1]

        tol = 1e-8
        ee_nz = ee[np.abs(ee) > tol]
        eo_nz = eo[np.abs(eo) > tol]

        if len(ee_nz) > 0 and len(eo_nz) > 0 and eo_nz[0] > tol:
            ratio = ee_nz[0] / eo_nz[0]
            print(f"  N={N:2d} ({ns:4d} modes): le={ee_nz[0]:10.6f} lo={eo_nz[0]:10.6f} "
                  f"ratio={ratio:10.6f} R²err={R2_err:.2e}")
        else:
            print(f"  N={N:2d} ({ns:4d} modes): degenerate or negative eigenvalues. "
                  f"R²err={R2_err:.2e}")
