"""
Matter-gravity decomposition of the d=3 eigenvector.

Module 4: Matter fields from causal geometry.

The d=3 eigenvector psi on states (a,b) decomposes into:
- Width w(j) = b(j) - a(j) + 1: the GEOMETRIC degree of freedom (gravity sector)
- Center a(j) = lower boundary: the MATTER degree of freedom

At m=5 (14700 states), we compute:
1. The joint distribution P(w, a) from psi^2 at bulk position j=2
2. Mutual information I(w; a) between geometry and matter
3. Entropy decomposition H(total) = H(w) + H(a|w) + I(w; a)

Key question: does matter decouple from geometry?
- I(w;a) ~ 0: geometry and matter are independent (decoupling)
- I(w;a) ~ H(a): matter is fully determined by geometry (no freedom)
- Expectation from 91% Markov finding: weak coupling (I small)
"""
import numpy as np
from scipy.linalg import eigh
from numba import njit, prange
from scipy.sparse.linalg import LinearOperator, eigsh
import time


def enum_noninc(m):
    """Enumerate nonincreasing functions on {0,...,m-1} -> {0,...,m-1}."""
    result = []
    def gen(prefix, max_val, remaining):
        if remaining == 0:
            result.append(tuple(prefix)); return
        for v in range(max_val + 1):
            gen(prefix + [v], v, remaining - 1)
    for first in range(m):
        gen([first], first, m - 1)
    return result


def build_states_d3(m):
    """Build d=3 states: pairs (a,b) of nonincreasing functions with vol > 0."""
    noninc = enum_noninc(m)
    states = []
    for a in noninc:
        for b in noninc:
            vol = sum(max(0, b[j] - a[j] + 1) for j in range(m))
            if vol > 0:
                states.append((a, b))
    return states, noninc


@njit(cache=True)
def build_pred_matrix(noninc_arr, nf, m):
    """Boolean predecessor matrix: pred[i,j] = True iff noninc[j] <= noninc[i]."""
    pred = np.zeros((nf, nf), dtype=np.bool_)
    for i in range(nf):
        for j in range(nf):
            below = True
            for k in range(m):
                if noninc_arr[j, k] > noninc_arr[i, k]:
                    below = False
                    break
            pred[i, j] = below
    return pred


@njit(parallel=True, cache=True)
def prefix_sum_below(V_grid, pred, nf):
    """Factored prefix sum: sum over (a',b') <= (a,b)."""
    G = np.zeros((nf, nf))
    for ai in prange(nf):
        for bi in range(nf):
            total = 0.0
            for bj in range(nf):
                if pred[bi, bj]:
                    total += V_grid[ai, bj]
            G[ai, bi] = total
    Y = np.zeros((nf, nf))
    for bi in prange(nf):
        for ai in range(nf):
            total = 0.0
            for aj in range(nf):
                if pred[ai, aj]:
                    total += G[aj, bi]
            Y[ai, bi] = total
    return Y


@njit(parallel=True, cache=True)
def prefix_sum_above(V_grid, succ, nf):
    """Factored suffix sum: sum over (a',b') >= (a,b)."""
    G = np.zeros((nf, nf))
    for ai in prange(nf):
        for bi in range(nf):
            total = 0.0
            for bj in range(nf):
                if succ[bi, bj]:
                    total += V_grid[ai, bj]
            G[ai, bi] = total
    Y = np.zeros((nf, nf))
    for bi in prange(nf):
        for ai in range(nf):
            total = 0.0
            for aj in range(nf):
                if succ[ai, aj]:
                    total += G[aj, bi]
            Y[ai, bi] = total
    return Y


def main():
    m = 5
    print(f"=== Matter-Gravity Decomposition (d=3, m={m}) ===")
    print()

    # --- Step 1: Build states and transfer operator ---
    t0 = time.time()
    states, noninc = build_states_d3(m)
    n_states = len(states)
    nf = len(noninc)
    print(f"Nonincreasing functions: {nf}")
    print(f"Valid state pairs: {n_states}")

    # Map each noninc function to an index
    noninc_idx = {f: i for i, f in enumerate(noninc)}

    # Build arrays for state indexing
    a_indices = np.array([noninc_idx[s[0]] for s in states])
    b_indices = np.array([noninc_idx[s[1]] for s in states])

    # Build grid validity mask
    valid_grid = np.full((nf, nf), -1, dtype=np.int64)
    for idx, (a, b) in enumerate(states):
        ai = noninc_idx[a]
        bi = noninc_idx[b]
        valid_grid[ai, bi] = idx

    noninc_arr = np.array(noninc, dtype=np.int32)
    pred = build_pred_matrix(noninc_arr, nf, m)
    succ = pred.T.copy()

    print(f"Predecessor matrix built in {time.time()-t0:.1f}s")

    # --- Step 2: Eigenvector via Lanczos ---
    t1 = time.time()

    def matvec(v):
        V_grid = np.zeros((nf, nf))
        for idx in range(n_states):
            V_grid[a_indices[idx], b_indices[idx]] = v[idx]
        Y_below = prefix_sum_below(V_grid, pred, nf)
        Y_above = prefix_sum_above(V_grid, succ, nf)
        Y_sym = (Y_below + Y_above) / 2.0
        result = np.zeros(n_states)
        for idx in range(n_states):
            result[idx] = Y_sym[a_indices[idx], b_indices[idx]]
        return result

    op = LinearOperator((n_states, n_states), matvec=matvec, dtype=np.float64)
    eigenvalues, eigenvectors = eigsh(op, k=2, which='LM')

    idx_max = np.argmax(eigenvalues)
    lambda1 = eigenvalues[idx_max]
    psi = eigenvectors[:, idx_max]
    psi = psi / np.linalg.norm(psi)

    # Ensure positive (Perron-Frobenius)
    if np.sum(psi) < 0:
        psi = -psi

    lambda2 = eigenvalues[1 - idx_max]
    gap_ratio = 1.0 - lambda2 / lambda1
    print(f"Eigenvector computed in {time.time()-t1:.1f}s")
    print(f"lambda_1 = {lambda1:.4f}, lambda_2 = {lambda2:.4f}, gap = {gap_ratio:.6f}")
    print()

    # --- Step 3: Extract width and center at bulk position j=2 ---
    j_bulk = 2  # Middle position for m=5
    prob = psi ** 2  # Born rule distribution

    # For each state, extract w(j_bulk) and a(j_bulk)
    width_vals = np.zeros(n_states, dtype=int)
    center_vals = np.zeros(n_states, dtype=int)
    for idx, (a, b) in enumerate(states):
        w = max(0, b[j_bulk] - a[j_bulk] + 1)
        width_vals[idx] = w
        center_vals[idx] = a[j_bulk]

    # --- Step 4: Joint distribution P(w, a) ---
    w_max = m + 1
    a_max = m
    P_joint = np.zeros((w_max, a_max))
    for idx in range(n_states):
        w = width_vals[idx]
        a = center_vals[idx]
        P_joint[w, a] += prob[idx]

    # Marginals
    P_w = P_joint.sum(axis=1)    # P(width)
    P_a = P_joint.sum(axis=0)    # P(center)

    print("--- Width distribution P(w) [GEOMETRY sector] ---")
    for w in range(w_max):
        if P_w[w] > 1e-12:
            print(f"  w={w}: P={P_w[w]:.6f}")

    print()
    print("--- Center distribution P(a) [MATTER sector] ---")
    for a in range(a_max):
        if P_a[a] > 1e-12:
            print(f"  a={a}: P={P_a[a]:.6f}")

    # --- Step 5: Entropy and mutual information ---
    # H(w) = gravitational entropy
    H_w = 0.0
    for w in range(w_max):
        if P_w[w] > 1e-15:
            H_w -= P_w[w] * np.log(P_w[w])

    # H(a) = total matter entropy
    H_a = 0.0
    for a in range(a_max):
        if P_a[a] > 1e-15:
            H_a -= P_a[a] * np.log(P_a[a])

    # H(w, a) = joint entropy
    H_joint = 0.0
    for w in range(w_max):
        for a in range(a_max):
            if P_joint[w, a] > 1e-15:
                H_joint -= P_joint[w, a] * np.log(P_joint[w, a])

    # Mutual information I(w; a) = H(w) + H(a) - H(w, a)
    I_wa = H_w + H_a - H_joint

    # Conditional entropy H(a|w) = H(w,a) - H(w)
    H_a_given_w = H_joint - H_w

    print()
    print("=" * 60)
    print("ENTROPY DECOMPOSITION (nats)")
    print("=" * 60)
    print(f"  H(w)   = {H_w:.6f}   [gravitational entropy - STRUCTURAL]")
    print(f"  H(a)   = {H_a:.6f}   [total matter entropy - STRUCTURAL]")
    print(f"  H(a|w) = {H_a_given_w:.6f}   [matter entropy given geometry]")
    print(f"  H(w,a) = {H_joint:.6f}   [joint entropy]")
    print(f"  I(w;a) = {I_wa:.6f}   [mutual information]")
    print()

    # --- Step 6: Decomposition quality ---
    if H_a > 1e-15:
        coupling_ratio = I_wa / H_a
    else:
        coupling_ratio = 0.0

    print("=" * 60)
    print("DECOMPOSITION QUALITY")
    print("=" * 60)
    print(f"  I(w;a) / H(a) = {coupling_ratio:.6f}")
    print()
    if coupling_ratio < 0.05:
        print("  --> DECOUPLED: geometry and matter are nearly independent")
        print("      Width (geometry) and center (matter) evolve separately.")
    elif coupling_ratio < 0.3:
        print("  --> WEAKLY COUPLED: mild geometry-matter interaction")
        print("      Consistent with 91% Markov reduction (hidden_variable.py).")
    elif coupling_ratio < 0.7:
        print("  --> MODERATELY COUPLED: significant geometry-matter correlation")
    else:
        print("  --> STRONGLY COUPLED: matter mostly determined by geometry")

    print()
    print("--- Interpretation ---")
    print("  width w = b - a + 1  -->  GEOMETRY sector (local volume/area)")
    print("  center a             -->  MATTER sector (position in target space)")
    print("  Decoupling means matter propagates on a fixed geometric background,")
    print("  as in QFT on curved spacetime. Coupling means backreaction.")
    print()

    # --- Step 7: Width-resolved center entropy ---
    print("--- Width-resolved matter entropy H(a|w=fixed) ---")
    for w in range(w_max):
        if P_w[w] > 1e-12:
            H_cond = 0.0
            for a in range(a_max):
                p_cond = P_joint[w, a] / P_w[w] if P_w[w] > 1e-15 else 0
                if p_cond > 1e-15:
                    H_cond -= p_cond * np.log(p_cond)
            n_support = sum(1 for a in range(a_max) if P_joint[w, a] > 1e-12)
            H_max = np.log(n_support) if n_support > 1 else 0
            print(f"  w={w}: H(a|w)={H_cond:.4f}, support={n_support}, "
                  f"H_max={H_max:.4f}, efficiency={H_cond/H_max:.3f}" if H_max > 0
                  else f"  w={w}: H(a|w)={H_cond:.4f}, support={n_support} (single state)")

    print()
    print("Labels: width = geometry (STRUCTURAL), center = matter (STRUCTURAL)")
    print("Status: DERIVABLE (computed from d=3 transfer matrix eigenvector)")


if __name__ == "__main__":
    main()
