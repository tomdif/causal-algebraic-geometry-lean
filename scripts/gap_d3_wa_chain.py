"""
d=3 gap via the REDUCED (w, a) chain.

The full d=3 transfer matrix at height m has O(C(2m-1,m)^2) states — millions
at m=7.  The (w, a) chain collapses each configuration to just its contact
width w and top-of-stack value a, giving O(m^2) states — tractable to m=100+.

CAVEAT: this is the COMBINATORIAL width chain.  Its stationary distribution
gives the unweighted width distribution (f_occ -> 1, not 0.138).  The spectral
gap from this chain is NOT the physical gamma_3.  What it DOES give is the
correlation length of the combinatorial kernel K_comb.

States
------
  (w, a) with w in {1, ..., m}, a in {0, ..., m - w}   [active contact]
  (0, a)       with a in {1, ..., m - 1}                [gap / zero-width]

For w >= 1 the configuration has contact columns at positions
a, a+1, ..., a+w-1  (0-indexed within a row of m columns).

Transitions (w, a) -> (w', a')
------------------------------
Active -> active (w >= 1, w' >= 1):
  The new contact interval [a', a'+w'-1] must be a sub-interval of [0, m-1]
  and must have SOME overlap with the old [a, a+w-1].
  Actually the correct rule: in each row, any contiguous block of columns
  can be chosen independently — but the CHAIN couples successive rows via
  the constraint that the NEW block must touch at least one column of the OLD
  block (causal connectivity in d=3).

  More precisely: a column c is "reachable" if it was occupied in the previous
  row OR adjacent to an occupied column.  The new block [a', a'+w'-1] must
  lie inside the reachable zone [max(0, a-1), min(m-1, a+w)].

  Transition probability: uniform over all valid (w', a') blocks.

Active -> gap (w >= 1, w' = 0):
  The new row can have zero contact columns.  This happens with a certain
  probability in the uniform model.

Gap -> anything (w = 0):
  From a gap state (0, a) the "previous contact" information is lost.
  We model this by saying the gap state transitions uniformly to all
  valid (w', a') for the NEXT row (memoryless after a gap).

Implementation
--------------
We build the transition matrix T where T[j, i] = Prob(state j | state i),
then symmetrize S = (T + T^T) / 2 and find its spectrum.

The number of valid next blocks from (w, a):
  Reachable zone: [lo, hi] = [max(0, a-1), min(m-1, a+w)]
  Zone length: L = hi - lo + 1
  Number of contiguous blocks in a zone of length L = L*(L+1)/2
  Plus the empty block (w'=0) = 1
  Total choices = L*(L+1)/2 + 1

For (w', a') with w' >= 1: valid iff [a', a'+w'-1] subset [lo, hi].
  This means a' >= lo and a'+w'-1 <= hi, i.e. a' in [lo, hi-w'+1].
  Count for given w': hi - w' + 1 - lo + 1 = L - w' + 1.

For w' = 0: always 1 choice.

Gap state (0, a): we say any block in [0, m-1] is valid (full freedom).
  Total choices = m*(m+1)/2 + 1.
"""

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh
from scipy.linalg import eigh
import sys
import time


def build_states(m):
    """Return list of states (w, a) and index map."""
    states = []
    idx = {}
    # Active states: w >= 1, a in [0, m-w]
    for w in range(1, m + 1):
        for a in range(0, m - w + 1):
            idx[(w, a)] = len(states)
            states.append((w, a))
    # Gap states: w = 0, a in [1, m-1]
    # a here is a "memory" parameter — after a gap we lose memory,
    # so we use a single gap state.
    idx[(0, 0)] = len(states)
    states.append((0, 0))
    return states, idx


def reachable_zone(w, a, m):
    """Return (lo, hi) of reachable columns from state (w, a)."""
    if w == 0:
        return (0, m - 1)
    lo = max(0, a - 1)
    hi = min(m - 1, a + w)
    return (lo, hi)


def valid_next_blocks(lo, hi):
    """Yield all valid (w', a') blocks within zone [lo, hi], plus (0, 0)."""
    L = hi - lo + 1
    yield (0, 0)  # gap
    for wp in range(1, L + 1):
        for ap in range(lo, hi - wp + 2):
            yield (wp, ap)


def count_next_blocks(lo, hi):
    """Number of valid next states from a zone [lo, hi]."""
    L = hi - lo + 1
    return L * (L + 1) // 2 + 1  # +1 for gap


def build_transition_matrix(m, use_sparse=False):
    """Build transition matrix T where T[j, i] = P(j | i)."""
    states, idx = build_states(m)
    n = len(states)

    if use_sparse:
        rows, cols, data = [], [], []
    else:
        T = np.zeros((n, n))

    for i, (w, a) in enumerate(states):
        lo, hi = reachable_zone(w, a, m)
        total = count_next_blocks(lo, hi)
        for (wp, ap) in valid_next_blocks(lo, hi):
            if (wp, ap) in idx:
                j = idx[(wp, ap)]
                prob = 1.0 / total
                if use_sparse:
                    rows.append(j)
                    cols.append(i)
                    data.append(prob)
                else:
                    T[j, i] += prob

    if use_sparse:
        T = sparse.csr_matrix((data, (rows, cols)), shape=(n, n))

    return T, states, idx, n


def analyze(m, use_sparse=False):
    """Build chain, symmetrize, find spectrum, report statistics."""
    t0 = time.time()
    T, states, idx, n = build_transition_matrix(m, use_sparse=use_sparse)

    # Symmetrize
    if use_sparse:
        S = (T + T.T) / 2.0
    else:
        S = (T + T.T) / 2.0

    # Find top eigenvalues
    k_eig = min(6, n - 2)
    if use_sparse and n > 50:
        vals, vecs = eigsh(S, k=k_eig, which='LM')
        order = np.argsort(-vals)
        vals = vals[order]
        vecs = vecs[:, order]
    else:
        if use_sparse:
            S = S.toarray()
        vals, vecs = eigh(S)
        order = np.argsort(-vals)
        vals = vals[order]
        vecs = vecs[:, order]

    lam1 = vals[0]
    lam2 = vals[1] if len(vals) > 1 else 0.0

    # Principal eigenvector (squared = stationary-like distribution)
    psi = vecs[:, 0]
    psi2 = psi ** 2
    psi2 /= psi2.sum()

    # Width distribution
    pi_w = np.zeros(m + 1)
    for i, (w, a) in enumerate(states):
        pi_w[w] += psi2[i]

    f_occ = 1.0 - pi_w[0]
    mean_w = sum(psi2[i] * w for i, (w, a) in enumerate(states))
    mean_w_over_m = mean_w / m

    # Correlation length
    ratio = lam2 / lam1 if lam1 > 0 else 0.0
    if abs(ratio) < 1.0 and ratio > 0:
        xi = -1.0 / np.log(ratio)
    else:
        xi = np.inf

    elapsed = time.time() - t0

    return {
        'm': m,
        'n_states': n,
        'lam1': lam1,
        'lam2': lam2,
        'ratio': ratio,
        'xi': xi,
        'f_occ': f_occ,
        'mean_w': mean_w,
        'mean_w_over_m': mean_w_over_m,
        'pi_w': pi_w,
        'time': elapsed,
    }


def main():
    m_values = [5, 10, 20, 50, 100]

    # Also compute small-m values for comparison
    m_small = [2, 3, 4, 5, 6, 7, 8]

    print("=" * 80)
    print("d=3 (w,a) CHAIN — COMBINATORIAL WIDTH KERNEL")
    print("=" * 80)
    print()

    # ---- Small-m detailed table ----
    print("--- Small m (dense solver) ---")
    print(f"{'m':>4} {'#states':>8} {'lam1':>10} {'lam2':>10} "
          f"{'lam2/lam1':>10} {'xi':>8} {'f_occ':>8} {'<w>/m':>8} {'time':>7}")
    print("-" * 80)

    small_results = []
    for m in m_small:
        r = analyze(m, use_sparse=False)
        small_results.append(r)
        print(f"{r['m']:>4d} {r['n_states']:>8d} {r['lam1']:>10.6f} {r['lam2']:>10.6f} "
              f"{r['ratio']:>10.6f} {r['xi']:>8.3f} {r['f_occ']:>8.5f} "
              f"{r['mean_w_over_m']:>8.5f} {r['time']:>7.2f}s")

    print()

    # ---- Large-m table ----
    print("--- Large m (sparse solver for m >= 20) ---")
    print(f"{'m':>4} {'#states':>8} {'lam1':>10} {'lam2':>10} "
          f"{'lam2/lam1':>10} {'xi':>8} {'f_occ':>8} {'<w>/m':>8} {'time':>7}")
    print("-" * 80)

    large_results = []
    for m in m_values:
        use_sp = (m >= 20)
        r = analyze(m, use_sparse=use_sp)
        large_results.append(r)
        print(f"{r['m']:>4d} {r['n_states']:>8d} {r['lam1']:>10.6f} {r['lam2']:>10.6f} "
              f"{r['ratio']:>10.6f} {r['xi']:>8.3f} {r['f_occ']:>8.5f} "
              f"{r['mean_w_over_m']:>8.5f} {r['time']:>7.2f}s")

    print()

    # ---- Extrapolation ----
    print("--- Extrapolation (linear in 1/m) ---")
    ms = np.array([r['m'] for r in large_results], dtype=float)
    inv_m = 1.0 / ms

    # Fit <w>/m = a + b/m
    wm = np.array([r['mean_w_over_m'] for r in large_results])
    if len(ms) >= 2:
        coeffs_w = np.polyfit(inv_m, wm, 1)
        print(f"  <w>/m = {coeffs_w[1]:.6f} + {coeffs_w[0]:.4f} / m")
        print(f"  <w>/m (m -> inf) = {coeffs_w[1]:.6f}")

    # Fit f_occ = c + d/m
    focc = np.array([r['f_occ'] for r in large_results])
    if len(ms) >= 2:
        coeffs_f = np.polyfit(inv_m, focc, 1)
        print(f"  f_occ = {coeffs_f[1]:.6f} + {coeffs_f[0]:.4f} / m")
        print(f"  f_occ (m -> inf) = {coeffs_f[1]:.6f}")

    # Fit ratio = e + f/m
    ratios = np.array([r['ratio'] for r in large_results])
    if len(ms) >= 2:
        coeffs_r = np.polyfit(inv_m, ratios, 1)
        print(f"  lam2/lam1 = {coeffs_r[1]:.6f} + {coeffs_r[0]:.4f} / m")
        print(f"  lam2/lam1 (m -> inf) = {coeffs_r[1]:.6f}")
        if 0 < coeffs_r[1] < 1:
            xi_inf = -1.0 / np.log(coeffs_r[1])
            print(f"  xi (m -> inf) = {xi_inf:.4f}")

    print()

    # ---- Width distribution at selected m ----
    print("--- Width distribution pi(w) at m=10 ---")
    r10 = [r for r in large_results if r['m'] == 10]
    if r10:
        r = r10[0]
        for w in range(r['m'] + 1):
            bar = '#' * int(r['pi_w'][w] * 100)
            print(f"  w={w:>3d}: {r['pi_w'][w]:.5f}  {bar}")

    print()

    # ---- Comparison note ----
    print("=" * 80)
    print("INTERPRETATION")
    print("=" * 80)
    print("""
The (w,a) chain is the COMBINATORIAL width chain, NOT the physical d=3
transfer matrix.  Key differences:

1. The physical d=3 transfer counts ALL pairs of nonincreasing functions
   (a, b) with b <= a pointwise — O(C(2m-1,m)^2) states.
   The (w,a) chain collapses to O(m^2) states by tracking only the
   width and left endpoint of the contact interval.

2. The stationary distribution of the (w,a) chain gives f_occ -> 1
   (almost surely occupied), whereas the PHYSICAL gap has f_occ ~ 0.138.

3. The spectral gap of the (w,a) chain measures the mixing rate of
   the COMBINATORIAL kernel, not the physical correlation length.

4. The (w,a) chain IS useful for:
   - Verifying that the combinatorial kernel has the expected structure
     (flat below diagonal, linear above, self-loop ~ 1/2)
   - Computing the combinatorial width distribution efficiently
   - Providing a LOWER BOUND on mixing (physical chain mixes slower)
""")


if __name__ == '__main__':
    main()
