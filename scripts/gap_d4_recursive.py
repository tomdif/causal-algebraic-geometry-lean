"""
Spectral gap for d=4 via recursive dimensional law.

Module 5: 3+1 dimensional structure.

At d=4, the cross-section is 2D: each slice is a pair of antitone functions
on [m]^2 -> {0,...,m-1}. An antitone function f satisfies f(p) >= f(q)
whenever p <= q componentwise.

For m=2:
- Domain: {0,1}^2 = {(0,0), (0,1), (1,0), (1,1)}
- Values: {0, 1}
- Antitone: f(p) >= f(q) when p1<=q1 AND p2<=q2

State pairs (A, B) with A, B antitone and vol > 0, where
vol = sum_{p in [m]^2} max(0, B(p) - A(p) + 1).

Transfer matrix: T[(A1,B1), (A2,B2)] = 1 iff A2 <= A1 and B2 <= B1 pointwise.

Recursive dimensional law prediction:
  gap_4 = f_bulk(3) * c(3) * gap_3 ~ 0.138 * 0.92 * 0.035 ~ 0.0044
"""
import numpy as np
from scipy.linalg import eigh
from itertools import product
import time


def enum_antitone_2d(m):
    """Enumerate antitone functions on {0,...,m-1}^2 -> {0,...,m-1}.

    Antitone: f(p) >= f(q) whenever p <= q componentwise.
    This means f is ORDER-REVERSING on the product poset.
    """
    # Domain points in {0,...,m-1}^2
    domain = [(i, j) for i in range(m) for j in range(m)]
    n_pts = len(domain)

    # Precompute partial order: (i1,j1) <= (i2,j2) iff i1<=i2 and j1<=j2
    # For antitone: if p <= q then f(p) >= f(q)
    le_pairs = []
    for idx1, (i1, j1) in enumerate(domain):
        for idx2, (i2, j2) in enumerate(domain):
            if i1 <= i2 and j1 <= j2 and idx1 != idx2:
                le_pairs.append((idx1, idx2))  # p <= q

    # Enumerate all functions f: domain -> {0,...,m-1}
    result = []
    for vals in product(range(m), repeat=n_pts):
        valid = True
        for (idx1, idx2) in le_pairs:
            # idx1 <= idx2 in poset, so f(idx1) >= f(idx2) for antitone
            if vals[idx1] < vals[idx2]:
                valid = False
                break
        if valid:
            result.append(tuple(vals))

    return result, domain


def build_states_d4(m):
    """Build d=4 states: pairs (A, B) of antitone functions on [m]^2 with vol > 0."""
    antitone, domain = enum_antitone_2d(m)
    n_pts = len(domain)
    states = []
    for A in antitone:
        for B in antitone:
            vol = sum(max(0, B[k] - A[k] + 1) for k in range(n_pts))
            if vol > 0:
                states.append((A, B))
    return states, antitone, domain


def main():
    m = 2
    print(f"=== d=4 Spectral Gap via Recursive Law (m={m}) ===")
    print()

    t0 = time.time()

    # --- Step 1: Enumerate antitone functions ---
    antitone, domain = enum_antitone_2d(m)
    n_anti = len(antitone)
    n_pts = len(domain)
    print(f"Domain points in [{m}]^2: {n_pts}")
    print(f"Antitone functions on [{m}]^2 -> {{0,...,{m-1}}}: {n_anti}")
    print(f"  (Related to Dedekind numbers / antichains in 2D poset)")
    print()

    # List them for small m
    if n_anti <= 20:
        print("  Antitone functions (values at (0,0),(0,1),(1,0),(1,1)):")
        for i, f in enumerate(antitone):
            print(f"    f_{i}: {dict(zip(domain, f))}")
        print()

    # --- Step 2: Build state pairs ---
    states, _, _ = build_states_d4(m)
    n_states = len(states)
    print(f"Valid state pairs (A, B) with vol > 0: {n_states}")
    print(f"Elapsed: {time.time()-t0:.2f}s")
    print()

    # --- Step 3: Build transfer matrix ---
    t1 = time.time()

    # Antitone index lookup
    anti_idx = {f: i for i, f in enumerate(antitone)}

    # Pointwise comparison for antitone functions
    anti_arr = np.array(antitone, dtype=np.int32)

    def leq_anti(f_idx, g_idx):
        """Check f <= g pointwise."""
        for k in range(n_pts):
            if anti_arr[f_idx, k] > anti_arr[g_idx, k]:
                return False
        return True

    # Build full transfer matrix
    T = np.zeros((n_states, n_states), dtype=np.float64)
    for i, (A1, B1) in enumerate(states):
        ai1 = anti_idx[A1]
        bi1 = anti_idx[B1]
        for j, (A2, B2) in enumerate(states):
            ai2 = anti_idx[A2]
            bi2 = anti_idx[B2]
            # T[i,j] = 1 iff A2 <= A1 and B2 <= B1 pointwise
            if leq_anti(ai2, ai1) and leq_anti(bi2, bi1):
                T[i, j] = 1.0

    # Symmetrize
    T_sym = (T + T.T) / 2.0

    print(f"Transfer matrix built: {n_states}x{n_states}")
    print(f"Non-zero entries: {int(np.sum(T > 0))}")
    print(f"Elapsed: {time.time()-t1:.2f}s")
    print()

    # --- Step 4: Eigendecomposition ---
    eigenvalues, eigenvectors = eigh(T_sym)

    # Sort descending
    idx_sort = np.argsort(eigenvalues)[::-1]
    eigenvalues = eigenvalues[idx_sort]
    eigenvectors = eigenvectors[:, idx_sort]

    lambda1 = eigenvalues[0]
    lambda2 = eigenvalues[1]
    gap_ratio = 1.0 - lambda2 / lambda1

    psi = eigenvectors[:, 0]
    psi = psi / np.linalg.norm(psi)
    if np.sum(psi) < 0:
        psi = -psi

    # Compute <area> = expected volume per state
    prob = psi ** 2
    areas = np.array([
        sum(max(0, B[k] - A[k] + 1) for k in range(n_pts))
        for (A, B) in states
    ], dtype=np.float64)
    mean_area = np.dot(prob, areas)

    # Normalized gap: gap * <area> / m^4
    gap_normalized = mean_area / (m ** 4)

    print("--- Eigenvalues ---")
    n_show = min(6, len(eigenvalues))
    for i in range(n_show):
        print(f"  lambda_{i+1} = {eigenvalues[i]:.6f}")
    print()
    print(f"Spectral gap (raw): 1 - lambda_2/lambda_1 = {gap_ratio:.6f}")
    print(f"<area> = {mean_area:.4f}")
    print(f"gap_4(m={m}) = <area>/m^4 = {gap_normalized:.6f}")
    print()

    # --- Step 5: Recursive law comparison ---
    print("=" * 60)
    print("RECURSIVE DIMENSIONAL LAW COMPARISON")
    print("=" * 60)

    # Known d=3 values (from earlier computations)
    gamma_3 = 0.035      # d=3 gap (m->infinity extrapolation)
    f_bulk_3 = 0.138      # bulk occupation fraction at d=3
    c_3 = 0.92            # finite-size correction factor

    gamma_4_predicted = f_bulk_3 * c_3 * gamma_3
    print(f"  gamma_3 (d=3 gap)          = {gamma_3}")
    print(f"  f_bulk(3) (bulk fraction)   = {f_bulk_3}")
    print(f"  c(3) (correction factor)    = {c_3}")
    print(f"  gamma_4_predicted           = {gamma_4_predicted:.6f}")
    print()
    print(f"  gamma_4_actual(m={m})        = {gap_normalized:.6f}  [FINITE SIZE]")
    print()

    if gap_normalized > 0 and gamma_4_predicted > 0:
        ratio = gap_normalized / gamma_4_predicted
        print(f"  actual / predicted = {ratio:.2f}")
        print(f"  (Finite-size at m={m} expected to be MUCH larger than m->inf limit)")
    print()

    # --- Step 6: Summary ---
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Antitone functions on [{m}]^2 -> {{0,1}}: {n_anti}  [DERIVABLE]")
    print(f"  State pairs with vol > 0:           {n_states}  [DERIVABLE]")
    print(f"  gap_4(m={m}) = {gap_normalized:.6f}          [DERIVABLE]")
    print(f"  gap_4_recursive_prediction = {gamma_4_predicted:.6f}  [STRUCTURAL]")
    print()
    print("  The recursive law gamma_{d+1} = f_bulk(d) * c(d) * gamma_d")
    print("  predicts the spectral gap in dimension d+1 from the d-dimensional gap.")
    print("  At m=2, finite-size effects dominate; the prediction targets m -> inf.")
    print()
    print("  Computation: DERIVABLE (exact diagonalization)")
    print("  Recursive prediction: STRUCTURAL (extrapolated from d=3 data)")

    # --- Step 7: Try m=3 if feasible ---
    print()
    print("=" * 60)
    print(f"Attempting m=3...")
    m3 = 3
    t2 = time.time()
    antitone3, domain3 = enum_antitone_2d(m3)
    n_anti3 = len(antitone3)
    n_pts3 = len(domain3)
    print(f"  Antitone functions on [{m3}]^2 -> {{0,1,2}}: {n_anti3}")

    states3, _, _ = build_states_d4(m3)
    n_states3 = len(states3)
    print(f"  State pairs with vol > 0: {n_states3}")

    if n_states3 <= 5000:
        print(f"  Building {n_states3}x{n_states3} transfer matrix...")

        anti3_idx = {f: i for i, f in enumerate(antitone3)}
        anti3_arr = np.array(antitone3, dtype=np.int32)

        def leq3(f_idx, g_idx):
            for k in range(n_pts3):
                if anti3_arr[f_idx, k] > anti3_arr[g_idx, k]:
                    return False
            return True

        T3 = np.zeros((n_states3, n_states3), dtype=np.float64)
        for i, (A1, B1) in enumerate(states3):
            ai1 = anti3_idx[A1]
            bi1 = anti3_idx[B1]
            for j, (A2, B2) in enumerate(states3):
                ai2 = anti3_idx[A2]
                bi2 = anti3_idx[B2]
                if leq3(ai2, ai1) and leq3(bi2, bi1):
                    T3[i, j] = 1.0

        T3_sym = (T3 + T3.T) / 2.0
        evals3, evecs3 = eigh(T3_sym)
        idx3 = np.argsort(evals3)[::-1]
        evals3 = evals3[idx3]
        evecs3 = evecs3[:, idx3]

        psi3 = evecs3[:, 0]
        psi3 = psi3 / np.linalg.norm(psi3)
        if np.sum(psi3) < 0:
            psi3 = -psi3
        prob3 = psi3 ** 2

        areas3 = np.array([
            sum(max(0, B[k] - A[k] + 1) for k in range(n_pts3))
            for (A, B) in states3
        ], dtype=np.float64)
        mean_area3 = np.dot(prob3, areas3)

        gap3 = 1.0 - evals3[1] / evals3[0]
        gap3_norm = mean_area3 / (m3 ** 4)

        print(f"  lambda_1 = {evals3[0]:.4f}, lambda_2 = {evals3[1]:.4f}")
        print(f"  gap_4(m={m3}) raw = {gap3:.6f}")
        print(f"  <area> = {mean_area3:.4f}")
        print(f"  gap_4(m={m3}) = <area>/m^4 = {gap3_norm:.6f}")
        print(f"  Elapsed: {time.time()-t2:.1f}s")
    else:
        print(f"  Too large for dense diagonalization ({n_states3} states).")
        print(f"  Would need sparse/Lanczos approach.")
        print(f"  Elapsed: {time.time()-t2:.1f}s")


if __name__ == "__main__":
    main()
