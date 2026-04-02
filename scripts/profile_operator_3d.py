"""
Full (w,a) profile operator for d=3 spectral theory.

State space at grid size m:
  - (w, a) with w = 1,...,m and a = 0,...,m-w  (occupied interval [a, a+w-1])
  - (0, a) with a = 1,...,m-1                   (empty: b < a, averaged over b)
  Total states = m(m+1)/2 + (m-1)

Transition: (w,a) -> (w',a') counts lattice-compatible sub-intervals.
Symmetrize T_sym = (T + T^T)/2, then extract principal eigenvector h(w,a).

Observables:
  gap_wa      = sum h^2(w,a) * w / (m^2 * sum h^2)
  f_occ_wa    = sum_{w>0} h^2(w,a) / sum h^2
  gamma_slice = gap_wa / f_occ_wa
"""

import numpy as np
from scipy.sparse.linalg import eigsh
from scipy.linalg import eigh
import sys


def build_state_space(m):
    """
    Enumerate (w, a) states.
    Returns list of (w, a) and the index map.
    """
    states = []
    index_map = {}

    # Occupied states: w >= 1, a in [0, m-w], b = a + w - 1
    for w in range(1, m + 1):
        for a in range(0, m - w + 1):
            idx = len(states)
            states.append((w, a))
            index_map[(w, a)] = idx

    # Empty states: w = 0, a in [1, m-1] (meaning b < a, averaged over b in [0, a-1])
    for a in range(1, m):
        idx = len(states)
        states.append((0, a))
        index_map[(0, a)] = idx

    n = len(states)
    # Check: n = m(m+1)/2 + (m-1)
    expected = m * (m + 1) // 2 + (m - 1)
    assert n == expected, f"n={n} != expected={expected}"
    return states, index_map, n


def count_transitions_occupied_to_occupied(w, a, wp, ap, m):
    """
    From state (w, a) with b = a + w - 1,
    to state (wp, ap) with bp = ap + wp - 1.

    Constraint: the new interval [ap, bp] must be contained in [0, b] = [0, a+w-1],
    AND ap <= a (the new lower bound doesn't exceed the old one).

    Actually the d=3 causal constraint is: a' <= a AND b' <= b (componentwise).
    So ap <= a and ap + wp - 1 <= a + w - 1, i.e., ap <= a and wp <= w + (a - ap).

    The number of valid transitions is 1 if the constraint is satisfied, 0 otherwise.
    But we need to think about what "transition count" means.

    In the transfer matrix, the entry T[(w',a'), (w,a)] counts the number of
    pairs (a_new, b_new) with a_new = ap, b_new = ap + wp - 1 that satisfy
    a_new <= a and b_new <= b. This is either 0 or 1 since (w',a') determines
    (a_new, b_new) uniquely.

    So T[(wp,ap), (w,a)] = 1 if ap <= a and ap + wp - 1 <= a + w - 1, else 0.
    """
    b = a + w - 1
    bp = ap + wp - 1
    if ap <= a and bp <= b:
        return 1.0
    return 0.0


def count_transitions_occupied_to_empty(w, a, ap_empty, m):
    """
    From state (w, a) with b = a + w - 1,
    to state (0, ap_empty) meaning b' < ap_empty with b' <= b.

    For empty state (0, ap_empty): we need some b' < ap_empty and b' <= b,
    and the "a" of the new state is ap_empty meaning the new interval is empty
    above position ap_empty.

    The constraint is: ap_empty <= a (causal: new a <= old a) ... but wait,
    for empty states (0, ap_empty), a_new = ap_empty with b_new < a_new.
    The causal constraint is a_new <= a_old and b_new <= b_old.
    Since b_new can be anything in [0, ap_empty - 1], and b_new <= b_old = a + w - 1,
    the number of valid b_new values is min(ap_empty, b + 1) if ap_empty <= a + 1,
    but we also need ap_empty <= a (for the a-constraint... actually let me reconsider).

    In the full transfer matrix, each state is (a_func, b_func) where a, b are
    nonincreasing functions. In the 1D projection (profile), a state is just
    (a_scalar, b_scalar) with a <= b (occupied) or b < a (empty).

    Transition (a, b) -> (a', b'): requires a' <= a, b' <= b.

    From (w, a_val) meaning interval [a_val, a_val + w - 1]:
      a_old = a_val, b_old = a_val + w - 1

    To (0, ap_empty) meaning b' < ap_empty, averaged over valid b':
      a_new = ap_empty, b_new in {0, 1, ..., ap_empty - 1}
      Constraint: ap_empty <= a_val and b_new <= b_old = a_val + w - 1

    Number of valid b_new = min(ap_empty, a_val + w) = min(ap_empty, b_old + 1)

    Since ap_empty <= a_val <= a_val + w - 1 = b_old, we have ap_empty <= b_old,
    so min(ap_empty, b_old + 1) = ap_empty.

    But wait, we need ap_empty >= 1 (by state space definition).
    And we need ap_empty <= a_val for the causal constraint on a.

    So the count = ap_empty if ap_empty <= a_val, else 0.

    However, the empty state (0, ap_empty) already averages over b_new in [0, ap_empty-1].
    So the transition weight should be the count divided by ap_empty (the number of
    b_new values in the empty state), giving weight 1 if ap_empty <= a_val.

    Actually, let me reconsider. The transition matrix entry T[new_state, old_state]
    should count the number of new configurations that are <= old configuration.
    For empty state (0, ap_empty), the new config is any (a', b') with a' = ap_empty
    and b' in [0, ap_empty - 1]. Each such pair is a separate configuration.

    But the empty state (0, ap_empty) is an AGGREGATE of ap_empty configurations.
    So we need to be careful about normalization.

    Approach: treat (0, ap_empty) as representing the average over its ap_empty
    sub-states. Then:
    - T[(0,ap), (w,a)] = (# valid b' for this transition) / ap  ... if ap <= a
    - Since all ap values of b' are valid when ap <= a, this gives weight 1.

    For consistency, transitions FROM (0, ap) also average:
    - From (0, ap) to (w', a'): average over b_old in [0, ap-1] of
      the count of valid transitions.
    """
    if ap_empty > a:
        return 0.0
    # All ap_empty choices of b' are valid (since ap_empty <= a <= b)
    # Normalized by ap_empty (the degeneracy of the empty state)
    return 1.0


def count_transitions_empty_to_occupied(ap_empty, wp, ap_new, m):
    """
    From state (0, ap_empty): a_old = ap_empty, b_old averaged over [0, ap_empty-1].
    To state (wp, ap_new) with bp_new = ap_new + wp - 1.

    Constraint: ap_new <= ap_empty and bp_new <= b_old.

    Average over b_old in [0, ap_empty - 1]:
      For each b_old, the transition exists iff ap_new <= ap_empty and bp_new <= b_old.
      So b_old >= bp_new = ap_new + wp - 1.

    Number of valid b_old = max(0, ap_empty - 1 - bp_new + 1) = max(0, ap_empty - bp_new)
                          = max(0, ap_empty - ap_new - wp + 1)

    Normalized by ap_empty:
      weight = max(0, ap_empty - ap_new - wp + 1) / ap_empty
    """
    if ap_new > ap_empty:
        return 0.0
    bp_new = ap_new + wp - 1
    valid_b_old = max(0, ap_empty - bp_new)
    return valid_b_old / ap_empty


def count_transitions_empty_to_empty(ap_old, ap_new, m):
    """
    From state (0, ap_old): a_old = ap_old, b_old averaged over [0, ap_old-1].
    To state (0, ap_new): a_new = ap_new, b_new averaged over [0, ap_new-1].

    Constraint: ap_new <= ap_old, b_new <= b_old.

    Average over b_old in [0, ap_old-1] and b_new in [0, ap_new-1]:
      For each (b_old, b_new): valid iff b_new <= b_old.
      Number of valid pairs = sum_{b_old=0}^{ap_old-1} min(b_old+1, ap_new)

    If ap_new <= ap_old (required), then:
      = sum_{b_old=0}^{ap_new-1} (b_old + 1) + sum_{b_old=ap_new}^{ap_old-1} ap_new
      = ap_new*(ap_new+1)/2 + (ap_old - ap_new) * ap_new

    Normalized by ap_old * ap_new (product of degeneracies):
      weight = [ap_new*(ap_new+1)/2 + (ap_old - ap_new)*ap_new] / (ap_old * ap_new)
             = [(ap_new+1)/2 + (ap_old - ap_new)] / ap_old
             = [(ap_new+1)/2 + ap_old - ap_new] / ap_old
             = [ap_old - ap_new/2 + 1/2] / ap_old
             = 1 - (ap_new - 1) / (2 * ap_old)
    """
    if ap_new > ap_old:
        return 0.0
    numerator = ap_new * (ap_new + 1) / 2.0 + (ap_old - ap_new) * ap_new
    denom = ap_old * ap_new
    return numerator / denom


def build_transition_matrix(m):
    """Build the full transition matrix T[new, old] for grid size m."""
    states, index_map, n = build_state_space(m)
    T = np.zeros((n, n))

    for j, (w_old, a_old) in enumerate(states):
        for i, (w_new, a_new) in enumerate(states):
            if w_old > 0 and w_new > 0:
                T[i, j] = count_transitions_occupied_to_occupied(
                    w_old, a_old, w_new, a_new, m)
            elif w_old > 0 and w_new == 0:
                T[i, j] = count_transitions_occupied_to_empty(
                    w_old, a_old, a_new, m)
            elif w_old == 0 and w_new > 0:
                T[i, j] = count_transitions_empty_to_occupied(
                    a_old, w_new, a_new, m)
            else:  # both empty
                T[i, j] = count_transitions_empty_to_empty(
                    a_old, a_new, m)

    return T, states, index_map, n


def analyze_profile_operator(m, gap_full=None, verbose=False):
    """Build and analyze the (w,a) profile operator at grid size m."""
    T, states, index_map, n = build_transition_matrix(m)

    # Symmetrize
    T_sym = 0.5 * (T + T.T)

    # Compute principal eigenvector
    if n <= 500:
        evals, evecs = eigh(T_sym)
        idx_sort = np.argsort(evals)[::-1]
        psi = evecs[:, idx_sort[0]]
        lam1 = evals[idx_sort[0]]
        lam2 = evals[idx_sort[1]] if n > 1 else 0.0
    else:
        evals, evecs = eigsh(T_sym, k=min(6, n - 1), which='LM', tol=1e-12)
        idx_sort = np.argsort(evals)[::-1]
        psi = evecs[:, idx_sort[0]]
        lam1 = evals[idx_sort[0]]
        lam2 = evals[idx_sort[1]] if len(evals) > 1 else 0.0

    # Ensure positive orientation
    if psi.sum() < 0:
        psi = -psi

    psi2 = psi ** 2
    norm2 = psi2.sum()

    # Extract observables
    widths = np.array([s[0] for s in states], dtype=float)

    gap_wa = np.dot(psi2, widths) / (m * norm2)
    # Note: gap normalized by m (single dimension), not m^2

    f_occ = sum(psi2[i] for i in range(n) if states[i][0] > 0) / norm2

    gamma_slice = gap_wa / f_occ if f_occ > 0 else 0.0

    # Also compute gap normalized by m^2 for comparison with full d=3
    gap_wa_m2 = np.dot(psi2, widths) / (m ** 2 * norm2)

    error = abs(gap_wa - gap_full) / gap_full if gap_full else float('nan')
    error_m2 = abs(gap_wa_m2 - gap_full) / gap_full if gap_full else float('nan')

    if verbose:
        print(f"\n  === m = {m}, n_states = {n} ===")
        print(f"  lambda_1 = {lam1:.6f}, lambda_2 = {lam2:.6f}")
        print(f"  gap_wa (w/m)   = {gap_wa:.6f}")
        print(f"  gap_wa (w/m^2) = {gap_wa_m2:.6f}")
        print(f"  f_occ          = {f_occ:.6f}")
        print(f"  gamma_slice    = {gamma_slice:.6f}")
        if gap_full:
            print(f"  gap_full       = {gap_full:.6f}")
            print(f"  error (w/m)    = {error:.4f}")
            print(f"  error (w/m^2)  = {error_m2:.4f}")

        # Show top eigenvector components
        idx_top = np.argsort(psi2)[::-1][:min(10, n)]
        print(f"\n  Top eigenvector components:")
        for k in idx_top:
            w, a = states[k]
            print(f"    (w={w}, a={a}): h = {psi[k]:.6f}, h^2/norm = {psi2[k]/norm2:.6f}")

    return {
        'm': m, 'n': n, 'lam1': lam1, 'lam2': lam2,
        'gap_wa': gap_wa, 'gap_wa_m2': gap_wa_m2,
        'f_occ': f_occ, 'gamma_slice': gamma_slice,
        'gap_full': gap_full, 'error': error, 'error_m2': error_m2,
        'psi': psi, 'psi2': psi2, 'states': states, 'norm2': norm2,
    }


def plot_continuum_shape(results_list):
    """Rescale h(w,a) to h(s=w/m, u=a/m) and plot."""
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
    except ImportError:
        print("\n  [matplotlib not available, skipping plots]")
        return

    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()

    for idx, res in enumerate(results_list[:6]):
        m = res['m']
        states = res['states']
        psi2 = res['psi2']
        norm2 = res['norm2']
        ax = axes[idx]

        s_vals = []
        u_vals = []
        h2_vals = []
        for k, (w, a) in enumerate(states):
            s_vals.append(w / m)
            u_vals.append(a / m)
            h2_vals.append(psi2[k] / norm2)

        sc = ax.scatter(s_vals, u_vals, c=h2_vals, s=max(1, 50 // m),
                       cmap='hot', vmin=0)
        ax.set_xlabel('s = w/m')
        ax.set_ylabel('u = a/m')
        ax.set_title(f'm = {m} (n = {res["n"]})')
        ax.set_xlim(-0.05, 1.05)
        ax.set_ylim(-0.05, 1.05)
        plt.colorbar(sc, ax=ax, label='h^2')

    plt.suptitle('(w,a) Profile Operator: Continuum Shape h^2(s, u)', fontsize=14)
    plt.tight_layout()
    outpath = '/Users/thomasdifiore/causal-algebraic-geometry-lean/scripts/profile_operator_3d.png'
    plt.savefig(outpath, dpi=150)
    print(f"\n  Plot saved to {outpath}")


def main():
    print("=" * 75)
    print("d=3 (w,a) PROFILE OPERATOR: Full Spectral Analysis")
    print("=" * 75)

    # Known full d=3 transfer matrix gaps (from gap_d3_fast.py and related)
    gap_full_known = {
        3: 0.377,
        4: 0.291,
        5: 0.240,
    }

    m_values = [3, 4, 5, 6, 10, 20, 50]
    results = []

    for m in m_values:
        gf = gap_full_known.get(m, None)
        res = analyze_profile_operator(m, gap_full=gf, verbose=True)
        results.append(res)

    # Print comparison table
    print("\n" + "=" * 95)
    print("COMPARISON TABLE")
    print("=" * 95)
    print(f"{'m':>4} | {'n_states':>8} | {'gap_wa(w/m)':>11} | {'gap_wa(w/m2)':>12} "
          f"| {'gap_full':>8} | {'err(w/m)':>8} | {'err(w/m2)':>9} "
          f"| {'f_occ':>7} | {'gamma':>7}")
    print("-" * 95)
    for res in results:
        gf_str = f"{res['gap_full']:.4f}" if res['gap_full'] else "   --  "
        err_str = f"{res['error']:.4f}" if res['gap_full'] else "  --  "
        err2_str = f"{res['error_m2']:.4f}" if res['gap_full'] else "  --  "
        print(f"{res['m']:>4} | {res['n']:>8} | {res['gap_wa']:>11.6f} | {res['gap_wa_m2']:>12.6f} "
              f"| {gf_str:>8} | {err_str:>8} | {err2_str:>9} "
              f"| {res['f_occ']:>7.4f} | {res['gamma_slice']:>7.4f}")

    # Scaling analysis
    print("\n" + "=" * 75)
    print("SCALING ANALYSIS: gap_wa vs 1/m")
    print("=" * 75)
    ms = np.array([r['m'] for r in results], dtype=float)
    gaps = np.array([r['gap_wa'] for r in results])
    gaps_m2 = np.array([r['gap_wa_m2'] for r in results])

    # Fit gap_wa ~ C / m^alpha
    if len(ms) >= 3:
        log_m = np.log(ms)
        log_g = np.log(gaps)
        log_g_m2 = np.log(gaps_m2)

        # Linear fit in log-log
        coeffs = np.polyfit(log_m, log_g, 1)
        alpha, log_C = -coeffs[0], coeffs[1]
        print(f"  gap_wa(w/m)  ~ {np.exp(log_C):.4f} / m^{alpha:.4f}")

        coeffs2 = np.polyfit(log_m, log_g_m2, 1)
        alpha2, log_C2 = -coeffs2[0], coeffs2[1]
        print(f"  gap_wa(w/m2) ~ {np.exp(log_C2):.4f} / m^{alpha2:.4f}")

    # Eigenvalue ratio analysis
    print("\n" + "=" * 75)
    print("EIGENVALUE ANALYSIS")
    print("=" * 75)
    for res in results:
        ratio = res['lam2'] / res['lam1'] if res['lam1'] > 0 else 0
        print(f"  m={res['m']:>3}: lam1={res['lam1']:>12.4f}, lam2={res['lam2']:>12.4f}, "
              f"lam2/lam1={ratio:.6f}")

    # Plot continuum shape
    plot_continuum_shape(results)

    print("\n" + "=" * 75)
    print("DONE")
    print("=" * 75)


if __name__ == '__main__':
    main()
