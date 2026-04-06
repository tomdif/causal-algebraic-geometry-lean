#!/usr/bin/env python3
"""
Chamber Spectral Theory vs Biological Differentiation Data
===========================================================

Tests three predictions from the chamber spectral theory:

  1. Spectral gap:  gamma_d = ln((d+1)/(d-1))  for d-stage irreversible pathway
  2. Parity pairing:  lambda_2^even = lambda_1^odd
  3. Spectral remainder is Mobius-Chebyshev

Tests on:
  A) Real scRNA-seq data (Paul et al. 2015 myeloid progenitors, via scanpy)
  B) Synthetic branching differentiation trajectory
  C) Explicit layered DAG with known d

Author: Thomas DiFiore, 2026-04-04
"""

import numpy as np
from scipy import sparse
from scipy.spatial.distance import pdist, squareform
from scipy.linalg import eigh
import warnings
warnings.filterwarnings("ignore")

np.set_printoptions(precision=8, linewidth=120)

# ============================================================
# UTILITIES
# ============================================================

def build_knn_graph(X, k=15):
    """Build k-nearest-neighbor adjacency (symmetric) from data matrix X."""
    from scipy.spatial.distance import cdist
    D = cdist(X, X, metric='euclidean')
    n = D.shape[0]
    W = np.zeros((n, n))
    for i in range(n):
        idx = np.argsort(D[i])[1:k+1]  # exclude self
        for j in idx:
            # Gaussian kernel with adaptive bandwidth
            sigma = D[i, idx[-1]]  # distance to k-th neighbor
            W[i, j] = np.exp(-D[i, j]**2 / (2 * sigma**2))
    # symmetrize
    W = (W + W.T) / 2
    return W


def diffusion_pseudotime(W, root_idx=0):
    """Compute diffusion pseudotime from a similarity matrix W.

    Uses the first nontrivial eigenvector of the diffusion operator
    as a proxy for pseudotime, oriented so root has smallest value.
    """
    n = W.shape[0]
    D_diag = np.sum(W, axis=1)
    D_diag[D_diag == 0] = 1e-10
    D_inv_sqrt = np.diag(1.0 / np.sqrt(D_diag))
    # Normalized Laplacian's eigenvectors = diffusion coordinates
    L_sym = np.eye(n) - D_inv_sqrt @ W @ D_inv_sqrt
    vals, vecs = eigh(L_sym)
    # First nontrivial eigenvector (skip constant)
    ptime = vecs[:, 1]
    # Orient so root has smallest pseudotime
    if ptime[root_idx] > np.median(ptime):
        ptime = -ptime
    # Rescale to [0, 1]
    ptime = (ptime - ptime.min()) / (ptime.max() - ptime.min() + 1e-15)
    return ptime


def build_triangular_transition(W, pseudotime):
    """Build directed transition matrix: T(i,j) = W(i,j) if pt(i) < pt(j), else 0.

    This enforces the causal/triangular structure zeta_epsilon.
    """
    n = W.shape[0]
    T = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if pseudotime[i] < pseudotime[j]:
                T[i, j] = W[i, j]
    # Row-normalize to get transition probabilities
    row_sums = T.sum(axis=1)
    row_sums[row_sums == 0] = 1.0
    T = T / row_sums[:, np.newaxis]
    return T


def build_triangular_transition_fast(W, pseudotime):
    """Vectorized version of build_triangular_transition."""
    n = W.shape[0]
    mask = pseudotime[:, None] < pseudotime[None, :]  # (i,j): pt(i) < pt(j)
    T = W * mask.astype(float)
    row_sums = T.sum(axis=1, keepdims=True)
    row_sums[row_sums == 0] = 1.0
    T = T / row_sums
    return T


def compute_chamber_kernel(T, mode="symmetric"):
    """Compute the chamber kernel from directed transition matrix T.

    mode="KF":  K_F = T + T^T - I
    mode="symmetric":  K = (T + T^T) / 2
    """
    n = T.shape[0]
    if mode == "KF":
        return T + T.T - np.eye(n)
    else:
        return (T + T.T) / 2


def compute_reflection_operator(pseudotime):
    """Build reflection operator R based on pseudotime reversal.

    R maps cell i to the cell with pseudotime closest to (1 - pt(i)).
    This is a permutation matrix.
    """
    n = len(pseudotime)
    R = np.zeros((n, n))
    reflected = 1.0 - pseudotime
    for i in range(n):
        j = np.argmin(np.abs(pseudotime - reflected[i]))
        R[i, j] = 1.0
    return R


def r_sector_eigenvalues(K, R, n_eigs=20):
    """Project K onto R-even and R-odd sectors, compute eigenvalues.

    R-even: P_+ = (I + R) / 2
    R-odd:  P_- = (I - R) / 2
    K_even = P_+ K P_+,  K_odd = P_- K P_-
    """
    n = K.shape[0]
    I = np.eye(n)
    P_plus = (I + R) / 2
    P_minus = (I - R) / 2

    K_even = P_plus @ K @ P_plus
    K_odd = P_minus @ K @ P_minus

    vals_even = np.sort(np.linalg.eigvalsh(K_even))[::-1]
    vals_odd = np.sort(np.linalg.eigvalsh(K_odd))[::-1]

    # Filter out near-zero eigenvalues (from projection)
    tol = 1e-10
    vals_even_nz = vals_even[np.abs(vals_even) > tol]
    vals_odd_nz = vals_odd[np.abs(vals_odd) > tol]

    return vals_even_nz, vals_odd_nz


def spectral_analysis(K, R, d_theory, label=""):
    """Full spectral analysis: compare with chamber theory predictions."""
    print(f"\n{'='*70}")
    print(f"  SPECTRAL ANALYSIS: {label}")
    print(f"{'='*70}")

    # Full spectrum
    vals_full = np.sort(np.linalg.eigvalsh(K))[::-1]
    print(f"\n  Full spectrum (top 10): {vals_full[:10]}")

    if len(vals_full) >= 2 and vals_full[0] > 0:
        gap_full = vals_full[0] - vals_full[1]
        ratio_full = vals_full[0] / vals_full[1] if vals_full[1] != 0 else float('inf')
        print(f"  Spectral gap (lambda_1 - lambda_2): {gap_full:.8f}")
        print(f"  Eigenvalue ratio lambda_1/lambda_2:  {ratio_full:.8f}")

    # R-sector eigenvalues
    vals_even, vals_odd = r_sector_eigenvalues(K, R)

    n_show = min(8, len(vals_even), len(vals_odd))
    print(f"\n  R-even eigenvalues (top {n_show}): {vals_even[:n_show]}")
    print(f"  R-odd  eigenvalues (top {n_show}): {vals_odd[:n_show]}")

    # -----------------------------------------------------------
    # PREDICTION 1: Spectral gap gamma_d = ln((d+1)/(d-1))
    # -----------------------------------------------------------
    print(f"\n  --- PREDICTION 1: Spectral gap ---")
    gamma_theory = np.log((d_theory + 1) / (d_theory - 1)) if d_theory > 1 else float('inf')
    print(f"  Theory (d={d_theory}): gamma_d = ln(({d_theory}+1)/({d_theory}-1)) = {gamma_theory:.8f}")

    if len(vals_even) >= 1 and len(vals_odd) >= 1:
        le1 = vals_even[0]
        lo1 = vals_odd[0]
        if lo1 != 0:
            ratio_eo = le1 / lo1
            print(f"  Measured: lambda_1^even / lambda_1^odd = {le1:.8f} / {lo1:.8f} = {ratio_eo:.8f}")
            theory_ratio = (d_theory + 1) / (d_theory - 1) if d_theory > 1 else float('inf')
            print(f"  Theory ratio (d+1)/(d-1) = {theory_ratio:.8f}")
            if theory_ratio != float('inf'):
                pct_err = abs(ratio_eo - theory_ratio) / theory_ratio * 100
                print(f"  Percentage error: {pct_err:.2f}%")

    # Also check: ln(le1/lo1) vs gamma_d
    if len(vals_even) >= 1 and len(vals_odd) >= 1 and vals_odd[0] > 0 and vals_even[0] > 0:
        gap_measured = np.log(vals_even[0] / vals_odd[0])
        print(f"  Measured gap ln(le1/lo1) = {gap_measured:.8f}")
        print(f"  Theory gap gamma_d      = {gamma_theory:.8f}")
        if gamma_theory != float('inf') and gamma_theory != 0:
            pct_err2 = abs(gap_measured - gamma_theory) / gamma_theory * 100
            print(f"  Percentage error: {pct_err2:.2f}%")

    # -----------------------------------------------------------
    # PREDICTION 2: Parity pairing lambda_2^even = lambda_1^odd
    # -----------------------------------------------------------
    print(f"\n  --- PREDICTION 2: Parity pairing ---")
    if len(vals_even) >= 2 and len(vals_odd) >= 1:
        le2 = vals_even[1]
        lo1 = vals_odd[0]
        print(f"  lambda_2^even = {le2:.8f}")
        print(f"  lambda_1^odd  = {lo1:.8f}")
        if lo1 != 0:
            rel_diff = abs(le2 - lo1) / abs(lo1) * 100
            print(f"  Relative difference: {rel_diff:.2f}%")
            match = "YES" if rel_diff < 5 else ("MARGINAL" if rel_diff < 20 else "NO")
            print(f"  Match: {match}")

    # -----------------------------------------------------------
    # PREDICTION 3: Mobius-Chebyshev remainder
    # -----------------------------------------------------------
    print(f"\n  --- PREDICTION 3: Mobius-Chebyshev structure ---")
    # The Mobius-Chebyshev prediction: eigenvalues in each sector should
    # follow a Chebyshev-like spacing after the leading eigenvalue.
    if len(vals_even) >= 4:
        # Check if even-sector eigenvalues have Chebyshev spacing
        # Chebyshev nodes on [a,b]: x_k = (a+b)/2 + (b-a)/2 * cos(pi*(2k-1)/(2n))
        top_even = vals_even[:min(8, len(vals_even))]
        if top_even[0] > 0 and len(top_even) >= 3:
            # Normalized gaps
            gaps = np.diff(top_even)  # should be negative (decreasing)
            gap_ratios = gaps[1:] / gaps[:-1] if np.all(gaps[:-1] != 0) else np.array([])
            print(f"  Even sector eigenvalue gaps: {gaps[:6]}")
            if len(gap_ratios) > 0:
                print(f"  Gap ratios (consecutive): {gap_ratios[:5]}")
                # For Chebyshev, gap ratios should be approximately constant
                if len(gap_ratios) >= 2:
                    gap_ratio_std = np.std(gap_ratios[:5]) / (np.mean(np.abs(gap_ratios[:5])) + 1e-15)
                    print(f"  Gap ratio coefficient of variation: {gap_ratio_std:.4f}")
                    print(f"  (Small CV suggests regular spacing, consistent with Chebyshev)")

    # -----------------------------------------------------------
    # INFER d from data
    # -----------------------------------------------------------
    print(f"\n  --- INFERRED d from spectral data ---")
    if len(vals_even) >= 1 and len(vals_odd) >= 1 and vals_odd[0] > 0 and vals_even[0] > 0:
        r = vals_even[0] / vals_odd[0]
        if r > 1:
            # r = (d+1)/(d-1) => d = (r+1)/(r-1)
            d_inferred = (r + 1) / (r - 1)
            print(f"  From le1/lo1 = {r:.6f}: d_inferred = (r+1)/(r-1) = {d_inferred:.4f}")
            print(f"  Nearest integer d = {round(d_inferred)}")
        else:
            print(f"  Ratio le1/lo1 = {r:.6f} <= 1, cannot infer d")

    return vals_even, vals_odd


# ============================================================
# TEST A: Real scRNA-seq data (Paul et al. 2015)
# ============================================================

def test_real_scrna():
    """Test with Paul et al. 2015 myeloid progenitor scRNA-seq data."""
    print("\n" + "#"*70)
    print("#  TEST A: Real scRNA-seq Data (Paul et al. 2015)")
    print("#"*70)

    try:
        import scanpy as sc
        print("  Loading Paul et al. 2015 dataset via scanpy...")
        adata = sc.datasets.paul15()
        print(f"  Loaded: {adata.n_obs} cells, {adata.n_vars} genes")

        # Preprocessing
        sc.pp.normalize_total(adata, target_sum=1e4)
        sc.pp.log1p(adata)
        sc.pp.pca(adata, n_comps=50)
        X_pca = adata.obsm['X_pca'][:, :30]  # top 30 PCs

        # Subsample for computational feasibility
        n_sub = min(500, adata.n_obs)
        idx = np.random.choice(adata.n_obs, n_sub, replace=False)
        X_sub = X_pca[idx]

        print(f"  Using {n_sub} cells, {X_sub.shape[1]} PCs")

        # Build kNN graph
        W = build_knn_graph(X_sub, k=15)

        # Pseudotime (use cell closest to HSC cluster as root)
        # Paul15 clusters: try to find HSC-like cells
        root = 0  # default
        if 'paul15_clusters' in adata.obs.columns:
            clusters = adata.obs['paul15_clusters'].values[idx]
            # Look for stem-like cluster
            for cname in ['HSC', 'CMP', 'Ery', '1']:
                mask = np.array([cname.lower() in str(c).lower() for c in clusters])
                if np.any(mask):
                    root = np.where(mask)[0][0]
                    print(f"  Root cell from cluster '{cname}' at index {root}")
                    break

        ptime = diffusion_pseudotime(W, root_idx=root)
        T = build_triangular_transition_fast(W, ptime)
        K = compute_chamber_kernel(T, mode="symmetric")
        R = compute_reflection_operator(ptime)

        # The myeloid pathway has ~4 major stages:
        # HSC -> CMP -> GMP/MEP -> terminal (Mono/Gran/Ery/Mega)
        d_theory = 4

        spectral_analysis(K, R, d_theory, label="Paul et al. 2015 myeloid scRNA-seq")
        return True

    except ImportError:
        print("  scanpy not available. Skipping real data test.")
        print("  Install with: pip install scanpy")
        return False
    except Exception as e:
        print(f"  Error loading real data: {e}")
        return False


# ============================================================
# TEST B: Synthetic Branching Differentiation Trajectory
# ============================================================

def test_synthetic_trajectory(N=500, d=3, noise_frac=0.10, n_genes=50):
    """Synthetic differentiation trajectory with d stages and branching."""
    print("\n" + "#"*70)
    print(f"#  TEST B: Synthetic Branching Trajectory (N={N}, d={d} stages)")
    print("#"*70)

    np.random.seed(42)

    # Create cells at d stages with branching at stage d//2
    cells_per_stage = N // d
    stage_labels = []
    branch_labels = []
    positions = []  # "true pseudotime" position

    for s in range(d):
        for c in range(cells_per_stage):
            stage_labels.append(s)
            # Branch assignment: after midpoint, cells split into 2 branches
            if s >= d // 2:
                branch = c % 2
            else:
                branch = 0
            branch_labels.append(branch)
            # Position along trajectory with jitter
            pos = s + np.random.uniform(0, 0.8)
            positions.append(pos)

    stage_labels = np.array(stage_labels)
    branch_labels = np.array(branch_labels)
    positions = np.array(positions)
    n = len(positions)

    # Generate gene expression: stage-dependent + branch-dependent + noise
    X = np.zeros((n, n_genes))
    for i in range(n):
        s = stage_labels[i]
        b = branch_labels[i]
        # Stage-dependent genes (gradual activation/silencing)
        for g in range(n_genes // 2):
            # Gene g activates at stage g * d / (n_genes//2)
            activation_stage = g * d / (n_genes // 2)
            X[i, g] = max(0, s - activation_stage) + np.random.normal(0, 0.3)
        # Branch-dependent genes
        for g in range(n_genes // 2, n_genes):
            if b == 0:
                X[i, g] = s * 0.5 + np.random.normal(0, 0.3)
            else:
                X[i, g] = -s * 0.3 + np.random.normal(0, 0.3)

    print(f"  Generated {n} cells across {d} stages, {n_genes} genes")
    print(f"  Stage distribution: {np.bincount(stage_labels)}")

    # Build kNN graph
    W = build_knn_graph(X, k=15)

    # Use true positions for pseudotime (best case for theory test)
    ptime = (positions - positions.min()) / (positions.max() - positions.min())

    # Build triangular transition matrix
    T = build_triangular_transition_fast(W, ptime)

    # Check triangularity
    n_upper = np.sum(T > 0)
    n_lower = 0
    for i in range(n):
        for j in range(n):
            if ptime[i] > ptime[j] and T[i, j] > 0:
                n_lower += 1
    print(f"  Transition matrix: {n_upper} nonzero entries, {n_lower} violating triangularity")

    # Chamber kernel
    K = compute_chamber_kernel(T, mode="symmetric")
    R = compute_reflection_operator(ptime)

    spectral_analysis(K, R, d, label=f"Synthetic trajectory (d={d}, N={n})")

    # Also test with KF kernel
    K_F = compute_chamber_kernel(T, mode="KF")
    spectral_analysis(K_F, R, d, label=f"Synthetic trajectory K_F mode (d={d}, N={n})")


# ============================================================
# TEST C: Explicit Layered DAG
# ============================================================

def test_explicit_dag(d=4, nodes_per_layer=10):
    """Test with an explicit layered DAG where structure is exact."""
    print("\n" + "#"*70)
    print(f"#  TEST C: Explicit Layered DAG (d={d}, {nodes_per_layer} nodes/layer)")
    print("#"*70)

    n = d * nodes_per_layer
    layer = np.repeat(np.arange(d), nodes_per_layer)

    # Build zeta: zeta(i,j) = 1 if layer(i) <= layer(j)
    # This is the incidence algebra zeta function on the layered poset
    zeta = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if layer[i] <= layer[j]:
                zeta[i, j] = 1.0

    # Normalize rows
    row_sums = zeta.sum(axis=1, keepdims=True)
    row_sums[row_sums == 0] = 1.0
    T = zeta / row_sums

    # Pseudotime from layer
    ptime = layer.astype(float) / (d - 1)
    # Add tiny jitter to break ties
    ptime = ptime + np.random.uniform(0, 1e-6, n)
    ptime = (ptime - ptime.min()) / (ptime.max() - ptime.min())

    # Chamber kernel
    K = compute_chamber_kernel(T, mode="symmetric")
    R = compute_reflection_operator(ptime)

    spectral_analysis(K, R, d, label=f"Layered DAG (d={d}, n={n})")

    # Also test the raw zeta matrix spectrum directly
    print(f"\n  --- Raw zeta matrix analysis ---")
    K_zeta = (zeta + zeta.T) / 2
    R_zeta = compute_reflection_operator(layer.astype(float) / max(1, d - 1) +
                                          np.random.uniform(0, 1e-6, n))
    vals_e, vals_o = r_sector_eigenvalues(K_zeta, R_zeta)
    n_show = min(6, len(vals_e), len(vals_o))
    print(f"  Zeta R-even top {n_show}: {vals_e[:n_show]}")
    print(f"  Zeta R-odd  top {n_show}: {vals_o[:n_show]}")
    if len(vals_e) >= 1 and len(vals_o) >= 1 and vals_o[0] > 0:
        r = vals_e[0] / vals_o[0]
        d_inf = (r + 1) / (r - 1) if r > 1 else float('inf')
        print(f"  le1/lo1 = {r:.6f}, inferred d = {d_inf:.4f} (true d = {d})")


def test_explicit_dag_small():
    """Tiny DAGs where everything can be computed by hand."""
    print("\n" + "#"*70)
    print("#  TEST C2: Small Explicit DAGs (hand-checkable)")
    print("#"*70)

    for d in [2, 3, 4, 5, 6, 8, 10]:
        n = d  # one node per layer
        # zeta(i,j) = 1 if i <= j (upper triangular ones matrix)
        zeta = np.zeros((n, n))
        for i in range(n):
            for j in range(n):
                if i <= j:
                    zeta[i, j] = 1.0

        # Symmetrize
        K = (zeta + zeta.T) / 2  # K(i,j) = 1 if i<=j or j<=i, so K = all 1s with weight 1
        # Actually K(i,j) = (zeta(i,j) + zeta(j,i))/2
        # zeta(i,j) = 1 if i<=j, zeta(j,i) = 1 if j<=i
        # So K(i,j) = 1 if i<=j, 0.5 if i==j... no:
        # K(i,j) = (1{i<=j} + 1{j<=i})/2
        #         = 1 if i==j, 0.5 if i!=j (since exactly one of i<j, j<i holds)
        # Wait: 1{i<=j} + 1{j<=i} = 1 + 1{i==j}. So K(i,j) = 1 if i==j, 0.5 if i!=j.
        # Hmm, that's (0.5)*ones + 0.5*I. Eigenvalues: 0.5*n + 0.5 (once), 0.5 (n-1 times).

        # Let's use the row-normalized version instead
        row_sums = zeta.sum(axis=1, keepdims=True)
        T = zeta / row_sums
        K = (T + T.T) / 2

        # Reflection: reverse the ordering
        R = np.zeros((n, n))
        for i in range(n):
            R[i, n - 1 - i] = 1.0

        vals_even, vals_odd = r_sector_eigenvalues(K, R)

        gamma_theory = np.log((d + 1) / (d - 1)) if d > 1 else float('inf')

        ratio_str = "N/A"
        gap_str = "N/A"
        d_inf_str = "N/A"

        if len(vals_even) >= 1 and len(vals_odd) >= 1 and vals_odd[0] > 0 and vals_even[0] > 0:
            r = vals_even[0] / vals_odd[0]
            gap_meas = np.log(r)
            ratio_str = f"{r:.6f}"
            gap_str = f"{gap_meas:.6f}"
            if r > 1:
                d_inf = (r + 1) / (r - 1)
                d_inf_str = f"{d_inf:.2f}"

        # Parity pairing check
        parity_str = "N/A"
        if len(vals_even) >= 2 and len(vals_odd) >= 1 and vals_odd[0] != 0:
            rel = abs(vals_even[1] - vals_odd[0]) / abs(vals_odd[0]) * 100
            parity_str = f"{rel:.1f}%"

        print(f"  d={d:2d}: le1/lo1={ratio_str:>12s}  "
              f"ln(ratio)={gap_str:>12s}  "
              f"gamma_theory={gamma_theory:>10.6f}  "
              f"d_inferred={d_inf_str:>8s}  "
              f"parity_diff={parity_str:>8s}")


def test_explicit_dag_exponential_kernel():
    """Layered DAG with exponential decay kernel (more physical)."""
    print("\n" + "#"*70)
    print("#  TEST C3: Layered DAG with Exponential Kernel")
    print("#"*70)

    for d in [3, 4, 5, 6, 8]:
        m = 20  # nodes per layer
        n = d * m
        layer = np.repeat(np.arange(d), m)

        # Exponential kernel: T(i,j) = exp(-|layer(i)-layer(j)|) if layer(i) <= layer(j)
        T = np.zeros((n, n))
        for i in range(n):
            for j in range(n):
                if layer[i] <= layer[j]:
                    T[i, j] = np.exp(-abs(layer[i] - layer[j]))

        # Row normalize
        row_sums = T.sum(axis=1, keepdims=True)
        row_sums[row_sums == 0] = 1.0
        T = T / row_sums

        K = (T + T.T) / 2

        # Reflection
        ptime = layer.astype(float) / max(1, d - 1) + np.random.uniform(0, 1e-8, n)
        R = compute_reflection_operator(ptime)

        vals_even, vals_odd = r_sector_eigenvalues(K, R)

        gamma_theory = np.log((d + 1) / (d - 1))

        ratio_str = "N/A"
        gap_str = "N/A"
        d_inf_str = "N/A"
        parity_str = "N/A"

        if len(vals_even) >= 1 and len(vals_odd) >= 1 and vals_odd[0] > 0 and vals_even[0] > 0:
            r = vals_even[0] / vals_odd[0]
            gap_meas = np.log(r)
            ratio_str = f"{r:.6f}"
            gap_str = f"{gap_meas:.6f}"
            if r > 1:
                d_inf = (r + 1) / (r - 1)
                d_inf_str = f"{d_inf:.2f}"

        if len(vals_even) >= 2 and len(vals_odd) >= 1 and vals_odd[0] != 0:
            rel = abs(vals_even[1] - vals_odd[0]) / abs(vals_odd[0]) * 100
            parity_str = f"{rel:.1f}%"

        print(f"  d={d:2d} (n={n:3d}): le1/lo1={ratio_str:>12s}  "
              f"ln(ratio)={gap_str:>12s}  "
              f"gamma_theory={gamma_theory:>10.6f}  "
              f"d_inferred={d_inf_str:>8s}  "
              f"parity_diff={parity_str:>8s}")


def test_pure_triangular_matrix():
    """Test with the pure d x d upper-triangular all-ones matrix.

    This is the simplest possible triangular/causal kernel:
    T(i,j) = 1 if i <= j, row-normalized.
    The theory should apply most cleanly here.
    """
    print("\n" + "#"*70)
    print("#  TEST D: Pure d x d Upper-Triangular (Row-Normalized)")
    print("#"*70)
    print("  This is the minimal test: T = row-normalized upper triangular ones.")
    print("  Theory: gamma_d = ln((d+1)/(d-1))\n")

    results = []
    for d in range(2, 16):
        # T(i,j) = 1/(d-i) if j >= i, else 0  (row-normalized)
        T = np.zeros((d, d))
        for i in range(d):
            for j in range(i, d):
                T[i, j] = 1.0 / (d - i)

        K = (T + T.T) / 2

        # Exact reflection: reverse order
        R = np.zeros((d, d))
        for i in range(d):
            R[i, d - 1 - i] = 1.0

        vals = np.sort(np.linalg.eigvalsh(K))[::-1]
        vals_even, vals_odd = r_sector_eigenvalues(K, R)

        gamma_theory = np.log((d + 1) / (d - 1))

        le1 = vals_even[0] if len(vals_even) > 0 else 0
        lo1 = vals_odd[0] if len(vals_odd) > 0 else 0

        if lo1 > 0 and le1 > 0:
            ratio = le1 / lo1
            gap = np.log(ratio)
            d_inf = (ratio + 1) / (ratio - 1) if ratio > 1 else float('inf')
        else:
            ratio = float('nan')
            gap = float('nan')
            d_inf = float('nan')

        # Parity pairing
        le2 = vals_even[1] if len(vals_even) > 1 else float('nan')
        parity_diff = abs(le2 - lo1) / abs(lo1) * 100 if lo1 != 0 and not np.isnan(le2) else float('nan')

        results.append((d, ratio, gap, gamma_theory, d_inf, parity_diff))

        print(f"  d={d:2d}: le1={le1:>10.6f}  lo1={lo1:>10.6f}  "
              f"le1/lo1={ratio:>10.6f}  ln(ratio)={gap:>10.6f}  "
              f"gamma_theory={gamma_theory:>10.6f}  d_inf={d_inf:>8.2f}  "
              f"parity={parity_diff:>6.1f}%")

    print("\n  Summary:")
    print(f"  {'d':>4s}  {'gap_measured':>12s}  {'gap_theory':>12s}  {'ratio':>8s}  {'d_inferred':>10s}")
    print(f"  {'-'*4}  {'-'*12}  {'-'*12}  {'-'*8}  {'-'*10}")
    for d, ratio, gap, gamma, d_inf, par in results:
        print(f"  {d:4d}  {gap:12.6f}  {gamma:12.6f}  {gap/gamma if gamma else 0:8.4f}  {d_inf:10.2f}")


# ============================================================
# TEST E: Noisy triangular kernel (realistic bio scenario)
# ============================================================

def test_noisy_triangular(d=4, noise_level=0.1, N=200):
    """Test with triangular kernel + noise (mimicking real bio data)."""
    print("\n" + "#"*70)
    print(f"#  TEST E: Noisy Triangular Kernel (d={d}, noise={noise_level}, N={N})")
    print("#"*70)

    np.random.seed(123)

    # Assign cells to layers
    cells_per_layer = N // d
    layer = np.repeat(np.arange(d), cells_per_layer)
    n = len(layer)

    # Clean triangular kernel with exponential decay
    T_clean = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if layer[i] <= layer[j]:
                T_clean[i, j] = np.exp(-0.5 * abs(layer[i] - layer[j]))

    # Add noise (some backward transitions)
    noise = np.random.uniform(0, noise_level, (n, n))
    T_noisy = T_clean + noise

    # Zero diagonal, row normalize
    np.fill_diagonal(T_noisy, 0)
    row_sums = T_noisy.sum(axis=1, keepdims=True)
    row_sums[row_sums == 0] = 1.0
    T_noisy = T_noisy / row_sums

    # Also make a "cleaned" version where we enforce triangularity after adding noise
    ptime = layer.astype(float) / max(1, d - 1) + np.random.uniform(0, 1e-6, n)
    ptime = (ptime - ptime.min()) / (ptime.max() - ptime.min())

    T_cleaned = T_noisy.copy()
    mask = ptime[:, None] >= ptime[None, :]
    T_cleaned[mask] = 0
    row_sums2 = T_cleaned.sum(axis=1, keepdims=True)
    row_sums2[row_sums2 == 0] = 1.0
    T_cleaned = T_cleaned / row_sums2

    R = compute_reflection_operator(ptime)

    # Test noisy version
    K_noisy = (T_noisy + T_noisy.T) / 2
    print(f"\n  With noise (NOT triangular-enforced):")
    spectral_analysis(K_noisy, R, d, label=f"Noisy kernel (noise={noise_level})")

    # Test cleaned version
    K_clean = (T_cleaned + T_cleaned.T) / 2
    print(f"\n  With noise but triangularity re-enforced:")
    spectral_analysis(K_clean, R, d, label=f"Cleaned kernel (noise={noise_level})")


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    print("="*70)
    print("  CHAMBER SPECTRAL THEORY: BIOLOGICAL DIFFERENTIATION TEST")
    print("="*70)
    print()
    print("  Predictions:")
    print("    1. Spectral gap gamma_d = ln((d+1)/(d-1))")
    print("    2. Parity pairing: lambda_2^even = lambda_1^odd")
    print("    3. Mobius-Chebyshev spectral remainder")
    print()

    # Test D first (pure, cleanest test)
    test_pure_triangular_matrix()

    # Test C2: small explicit DAGs
    test_explicit_dag_small()

    # Test C3: exponential kernel on layered DAG
    test_explicit_dag_exponential_kernel()

    # Test B: synthetic trajectory
    test_synthetic_trajectory(N=300, d=3, noise_frac=0.1)
    test_synthetic_trajectory(N=400, d=4, noise_frac=0.1)

    # Test C: larger explicit DAG
    test_explicit_dag(d=4, nodes_per_layer=15)

    # Test E: noisy triangular
    test_noisy_triangular(d=4, noise_level=0.05, N=200)
    test_noisy_triangular(d=4, noise_level=0.20, N=200)

    # Test A: real scRNA-seq (if available)
    test_real_scrna()

    print("\n" + "="*70)
    print("  DONE. Review the numbers above honestly.")
    print("="*70)
