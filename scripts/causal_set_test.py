#!/usr/bin/env python3
"""
causal_set_test.py — Test chamber spectral theory against causal set theory

The connection: In causal set theory, the fundamental object is a finite poset
with causal matrix zeta(x,y) = 1 if x <= y. This is the order kernel from
chamber spectral theory.

The chamber kernel K_F = Lambda^d(zeta) + Lambda^d(zeta^T) - I operates on
the Weyl chamber (ordered d-tuples). The spectral theory predicts:
  1. Gap law: le/lo = (d+1)/(d-1)
  2. Parity pairing: lambda_2^even = lambda_1^odd
  3. Spectral containment

We test these predictions on:
  (1) Regular lattices [m] (sanity check)
  (2) 1+1D Minkowski sprinklings
  (3) 2+1D Minkowski sprinklings
  (4) Random DAGs (no geometry)
  (5) Benincasa-Dowker d'Alembertian comparison
"""

import numpy as np
from itertools import combinations, permutations
from scipy.linalg import eigh, eigvalsh
import warnings
warnings.filterwarnings('ignore')

np.random.seed(42)

# ============================================================================
# CORE INFRASTRUCTURE
# ============================================================================

def perm_sign(p):
    """Sign of permutation."""
    s = 0
    p = list(p)
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s += 1
    return (-1) ** s


def build_chamber_kernel(zeta, d):
    """
    Build the chamber kernel K_F on the Weyl chamber from a causal matrix zeta.

    zeta: N x N matrix with zeta[i,j] = 1 if i <= j in the poset.
    d: chamber dimension (d-tuples of distinct elements).

    K_F(P,Q) = det(zeta[P_i, Q_j]) + det(zeta[Q_i, P_j]) - delta(P,Q)

    For d=2: det = zeta[P0,Q0]*zeta[P1,Q1] - zeta[P0,Q1]*zeta[P1,Q0]
    For d=3: standard 3x3 determinant via Leibniz formula
    General d: use np.linalg.det on the d x d submatrix
    """
    N = zeta.shape[0]
    states = list(combinations(range(N), d))
    n_states = len(states)
    idx = {s: i for i, s in enumerate(states)}
    states_arr = np.array(states)  # shape (n_states, d)

    K = np.zeros((n_states, n_states))

    if d == 2:
        # Fully vectorized for d=2
        P0 = states_arr[:, 0]  # (n_states,)
        P1 = states_arr[:, 1]
        Q0 = states_arr[:, 0]
        Q1 = states_arr[:, 1]
        # Forward: det(zeta[P_i, Q_j]) for all pairs
        # zeta[P0[a], Q0[b]] = zeta[P0, :][:, Q0] etc.
        Z00 = zeta[np.ix_(P0, Q0)]  # (n_states, n_states)
        Z01 = zeta[np.ix_(P0, Q1)]
        Z10 = zeta[np.ix_(P1, Q0)]
        Z11 = zeta[np.ix_(P1, Q1)]
        fwd = Z00 * Z11 - Z01 * Z10
        # Backward: det(zeta[Q_j, P_i])
        B00 = zeta[np.ix_(Q0, P0)]
        B01 = zeta[np.ix_(Q1, P0)]
        B10 = zeta[np.ix_(Q0, P1)]
        B11 = zeta[np.ix_(Q1, P1)]
        bwd = B00 * B11 - B01 * B10
        K = fwd + bwd
        np.fill_diagonal(K, np.diag(K) - 1.0)

    elif d == 3:
        # Semi-vectorized for d=3: loop over rows, vectorize columns
        P_cols = [states_arr[:, i] for i in range(3)]
        Q_cols = [states_arr[:, j] for j in range(3)]
        for a in range(n_states):
            p = states_arr[a]
            # zeta[p[i], Q[b,j]] for all b
            z = [[zeta[p[i], Q_cols[j]] for j in range(3)] for i in range(3)]
            fwd = (z[0][0]*z[1][1]*z[2][2] + z[0][1]*z[1][2]*z[2][0]
                 + z[0][2]*z[1][0]*z[2][1] - z[0][2]*z[1][1]*z[2][0]
                 - z[0][1]*z[1][0]*z[2][2] - z[0][0]*z[1][2]*z[2][1])
            # backward: zeta[Q[b,j], p[i]]
            zb = [[zeta[Q_cols[j], p[i]] for j in range(3)] for i in range(3)]
            bwd = (zb[0][0]*zb[1][1]*zb[2][2] + zb[0][1]*zb[1][2]*zb[2][0]
                 + zb[0][2]*zb[1][0]*zb[2][1] - zb[0][2]*zb[1][1]*zb[2][0]
                 - zb[0][1]*zb[1][0]*zb[2][2] - zb[0][0]*zb[1][2]*zb[2][1])
            K[a, :] = fwd + bwd
        np.fill_diagonal(K, np.diag(K) - 1.0)

    else:
        # General d: loop with np.linalg.det
        all_perms = list(permutations(range(d)))
        all_signs = [perm_sign(p) for p in all_perms]
        for a, P in enumerate(states):
            for b, Q in enumerate(states):
                # Build d x d submatrix
                M_fwd = np.array([[zeta[P[i], Q[j]] for j in range(d)] for i in range(d)])
                M_bwd = np.array([[zeta[Q[j], P[i]] for j in range(d)] for i in range(d)])
                K[a, b] = np.linalg.det(M_fwd) + np.linalg.det(M_bwd)
                if a == b:
                    K[a, b] -= 1.0

    return K, states, idx


def build_reflection(states, idx, m, d):
    """
    Build the simplex reflection R: (s_1, ..., s_d) -> (m-1-s_d, ..., m-1-s_1).
    This requires the poset to have a natural "top" element m-1.
    For general posets, we need to define R differently.
    """
    n = len(states)
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d - 1 - j] for j in range(d))
        if reflected in idx:
            R[i, idx[reflected]] = 1.0
    return R


def analyze_sectors(K, R, label="", tol=1e-8):
    """
    Decompose K into R-even and R-odd sectors, report eigenvalues.
    Returns (le_top, lo_top, le_all, lo_all, pairing_error).
    """
    n = K.shape[0]
    K_sym = (K + K.T) / 2  # symmetrize

    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2

    Ke = Pe @ K_sym @ Pe
    Ko = Po @ K_sym @ Po

    ee = np.sort(eigvalsh(Ke))[::-1]
    eo = np.sort(eigvalsh(Ko))[::-1]

    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]

    if len(ee_nz) < 2 or len(eo_nz) < 1:
        return None, None, ee_nz, eo_nz, None

    le_top = ee_nz[0]
    lo_top = eo_nz[0]
    le2 = ee_nz[1]

    ratio = le_top / lo_top if abs(lo_top) > tol else None
    pairing = abs(le2 - lo_top) / max(abs(lo_top), 1e-15) if abs(lo_top) > tol else None

    return le_top, lo_top, ee_nz, eo_nz, pairing


def print_analysis(le, lo, ee, eo, pairing, d, label):
    """Print analysis results."""
    target = (d + 1) / (d - 1) if d > 1 else None

    if le is None or lo is None:
        print(f"  {label}: insufficient nonzero eigenvalues")
        return

    ratio = le / lo if abs(lo) > 1e-12 else float('inf')
    print(f"  {label}:")
    print(f"    Top even eigs:  {ee[:5].round(4) if len(ee) >= 5 else ee.round(4)}")
    print(f"    Top odd eigs:   {eo[:5].round(4) if len(eo) >= 5 else eo.round(4)}")
    print(f"    le/lo = {ratio:.6f}   (target = {target:.6f})")
    if pairing is not None:
        print(f"    |lambda_2^even - lambda_1^odd| / |lambda_1^odd| = {pairing:.2e}  "
              f"{'PAIRED' if pairing < 0.01 else 'NOT PAIRED'}")
    print(f"    Gap law error: {abs(ratio - target) / target * 100:.2f}%")


# ============================================================================
# TEST 1: REGULAR LATTICE (SANITY CHECK)
# ============================================================================

def test_regular_lattice():
    print("=" * 80)
    print("TEST 1: REGULAR LATTICE [m] — SANITY CHECK")
    print("  zeta(i,j) = 1 if i <= j. This is the original chamber theory setup.")
    print("=" * 80)

    for d in [2, 3, 4]:
        print(f"\n  d = {d}, target le/lo = {(d+1)/(d-1):.6f}")
        print(f"  {'m':>4} {'states':>7} {'le':>10} {'lo':>10} {'le/lo':>10} {'target':>10} {'pairing':>12}")
        print(f"  {'-'*4} {'-'*7} {'-'*10} {'-'*10} {'-'*10} {'-'*10} {'-'*12}")

        ms = [6, 8, 10] if d <= 3 else [6, 8]
        for m in ms:
            N = m
            zeta = np.zeros((N, N))
            for i in range(N):
                for j in range(N):
                    if i <= j:
                        zeta[i, j] = 1.0

            K, states, idx = build_chamber_kernel(zeta, d)
            R = build_reflection(states, idx, m, d)
            le, lo, ee, eo, pairing = analyze_sectors(K, R)

            if le is not None and lo is not None:
                ratio = le / lo
                target = (d + 1) / (d - 1)
                pair_str = f"{pairing:.2e}" if pairing is not None else "N/A"
                print(f"  {m:>4} {len(states):>7} {le:>10.4f} {lo:>10.4f} "
                      f"{ratio:>10.6f} {target:>10.6f} {pair_str:>12}")


# ============================================================================
# TEST 2: 1+1D MINKOWSKI SPRINKLING
# ============================================================================

def sprinkle_1plus1(N):
    """
    Sprinkle N points in a 1+1D causal diamond.
    Diamond: {(t,x) : 0 < t < 1, |x| < t, |x| < 1-t}
    This is the intersection of the future of (0,0) and past of (1,0).
    """
    points = []
    while len(points) < N:
        t = np.random.uniform(0, 1)
        x = np.random.uniform(-1, 1)
        # Inside diamond: |x| < t and |x| < 1-t
        if abs(x) < t and abs(x) < 1 - t:
            points.append((t, x))
    return np.array(points)


def causal_matrix_minkowski_1plus1(points):
    """
    Build causal matrix for 1+1D Minkowski space.
    i <= j iff (t_j - t_i)^2 - (x_j - x_i)^2 >= 0 and t_j >= t_i.
    """
    N = len(points)
    # Sort by time coordinate for topological ordering
    order = np.argsort(points[:, 0])
    points = points[order]

    zeta = np.eye(N)  # reflexive: i <= i
    for i in range(N):
        for j in range(i + 1, N):
            dt = points[j, 0] - points[i, 0]
            dx = points[j, 1] - points[i, 1]
            if dt >= 0 and dt * dt - dx * dx >= 0:
                zeta[i, j] = 1.0

    # Transitive closure (should already be transitive for Minkowski, but be safe)
    # Floyd-Warshall
    for k in range(N):
        for i in range(N):
            for j in range(N):
                if zeta[i, k] > 0.5 and zeta[k, j] > 0.5:
                    zeta[i, j] = 1.0

    return zeta, points


def build_reflection_poset(states, idx, N, d):
    """
    For a general poset with N elements, the natural reflection is:
    R: (s_1, ..., s_d) -> (N-1-s_d, ..., N-1-s_1)
    This is only meaningful if the poset has an order-reversing symmetry.
    For random sprinklings, it generally DOESN'T.

    Instead, we try: reflect in the time coordinate.
    But this doesn't map the poset to itself.

    For an honest test, we use the same R as the lattice case:
    R reverses the labeling. This only makes sense if the topological
    sort respects some symmetry.
    """
    n = len(states)
    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(N - 1 - s[d - 1 - j] for j in range(d))
        if reflected in idx:
            R[i, idx[reflected]] = 1.0
    return R


def test_minkowski_1plus1():
    print("\n" + "=" * 80)
    print("TEST 2: 1+1D MINKOWSKI SPRINKLING")
    print("  Sprinkle N points in a causal diamond in 1+1D Minkowski space.")
    print("  Build causal matrix zeta, then chamber kernel K_F for d=2.")
    print("  Target le/lo = 3.000000 for d=2.")
    print("=" * 80)

    d = 2
    target = (d + 1) / (d - 1)

    for N in [20, 30, 50]:
        print(f"\n  N = {N} points, d = {d}")

        # Multiple trials
        ratios = []
        pairings = []
        n_trials = 5 if N <= 30 else 3

        for trial in range(n_trials):
            np.random.seed(42 + trial * 100)
            points = sprinkle_1plus1(N)
            zeta, points_sorted = causal_matrix_minkowski_1plus1(points)

            n_relations = int(np.sum(zeta) - N)  # exclude diagonal
            density = n_relations / (N * (N - 1))

            K, states, idx = build_chamber_kernel(zeta, d)
            R = build_reflection_poset(states, idx, N, d)

            # Check if R is a valid involution (R^2 = I)
            R2_err = np.max(np.abs(R @ R - np.eye(len(states))))

            # Also check if R commutes with K (required for sector decomposition)
            RK_err = np.max(np.abs(R @ K - K @ R))

            if R2_err > 0.1 or RK_err > 0.1:
                # R is not valid for this poset — try without sectors
                K_sym = (K + K.T) / 2
                evals = np.sort(eigvalsh(K_sym))[::-1]
                evals_nz = evals[np.abs(evals) > 1e-8]
                if trial == 0:
                    print(f"    R^2 error: {R2_err:.4f}, [R,K] error: {RK_err:.4f}")
                    print(f"    R is NOT a valid symmetry for this poset.")
                    print(f"    Full spectrum top 5: {evals_nz[:5].round(4)}")
                    print(f"    Causal density: {density:.3f}")
                    print(f"    Attempting sector analysis anyway...")

            le, lo, ee, eo, pairing = analyze_sectors(K, R)

            if le is not None and lo is not None and abs(lo) > 1e-8:
                ratios.append(le / lo)
                if pairing is not None:
                    pairings.append(pairing)

            if trial == 0:
                print(f"    Chamber size: {len(states)}")
                print(f"    Causal relations: {n_relations} (density {density:.3f})")
                if le is not None and lo is not None:
                    print(f"    le = {le:.4f}, lo = {lo:.4f}, le/lo = {le/lo:.6f}")
                    if pairing is not None:
                        print(f"    Pairing error: {pairing:.2e}")

        if ratios:
            mean_r = np.mean(ratios)
            std_r = np.std(ratios)
            print(f"\n    Over {len(ratios)} trials:")
            print(f"    le/lo = {mean_r:.4f} +/- {std_r:.4f}  (target = {target:.4f})")
            print(f"    Deviation from target: {abs(mean_r - target)/target*100:.1f}%")
            if pairings:
                print(f"    Mean pairing error: {np.mean(pairings):.2e}")


# ============================================================================
# TEST 3: 2+1D MINKOWSKI SPRINKLING
# ============================================================================

def sprinkle_2plus1(N):
    """
    Sprinkle N points in a 2+1D causal diamond.
    Diamond: future of origin intersected with past of (1,0,0).
    {(t,x,y) : t > 0, t^2 - x^2 - y^2 > 0, (1-t)^2 - x^2 - y^2 > 0}
    """
    points = []
    while len(points) < N:
        t = np.random.uniform(0, 1)
        x = np.random.uniform(-1, 1)
        y = np.random.uniform(-1, 1)
        r2 = x * x + y * y
        if t * t > r2 and (1 - t) ** 2 > r2:
            points.append((t, x, y))
    return np.array(points)


def causal_matrix_minkowski_2plus1(points):
    """Build causal matrix for 2+1D Minkowski space."""
    N = len(points)
    order = np.argsort(points[:, 0])
    points = points[order]

    zeta = np.eye(N)
    for i in range(N):
        for j in range(i + 1, N):
            dt = points[j, 0] - points[i, 0]
            dx = points[j, 1] - points[i, 1]
            dy = points[j, 2] - points[i, 2]
            if dt >= 0 and dt * dt - dx * dx - dy * dy >= 0:
                zeta[i, j] = 1.0

    # Transitive closure
    for k in range(N):
        for i in range(N):
            for j in range(N):
                if zeta[i, k] > 0.5 and zeta[k, j] > 0.5:
                    zeta[i, j] = 1.0

    return zeta, points


def test_minkowski_2plus1():
    print("\n" + "=" * 80)
    print("TEST 3: 2+1D MINKOWSKI SPRINKLING")
    print("  Sprinkle N points in a causal diamond in 2+1D Minkowski space.")
    print("  Build K_F for d=2. Target le/lo = 3.000000.")
    print("=" * 80)

    d = 2
    target = (d + 1) / (d - 1)

    for N in [30, 50]:
        print(f"\n  N = {N} points, d = {d}")

        ratios = []
        n_trials = 3

        for trial in range(n_trials):
            np.random.seed(42 + trial * 100)
            points = sprinkle_2plus1(N)
            zeta, points_sorted = causal_matrix_minkowski_2plus1(points)

            n_relations = int(np.sum(zeta) - N)
            density = n_relations / (N * (N - 1))

            K, states, idx = build_chamber_kernel(zeta, d)
            R = build_reflection_poset(states, idx, N, d)

            R2_err = np.max(np.abs(R @ R - np.eye(len(states))))
            RK_err = np.max(np.abs(R @ K - K @ R))

            le, lo, ee, eo, pairing = analyze_sectors(K, R)

            if le is not None and lo is not None and abs(lo) > 1e-8:
                ratios.append(le / lo)

            if trial == 0:
                print(f"    Chamber size: {len(states)}")
                print(f"    Causal density: {density:.3f}")
                print(f"    R^2 error: {R2_err:.4f}, [R,K] error: {RK_err:.4f}")
                if le is not None and lo is not None:
                    print(f"    le = {le:.4f}, lo = {lo:.4f}, le/lo = {le/lo:.6f}")
                    if pairing is not None:
                        print(f"    Pairing error: {pairing:.2e}")

        if ratios:
            mean_r = np.mean(ratios)
            std_r = np.std(ratios)
            print(f"\n    Over {len(ratios)} trials:")
            print(f"    le/lo = {mean_r:.4f} +/- {std_r:.4f}  (target = {target:.4f})")
            print(f"    Deviation: {abs(mean_r - target)/target*100:.1f}%")


# ============================================================================
# TEST 4: RANDOM DAG (NO GEOMETRY)
# ============================================================================

def random_dag_zeta(N, p):
    """
    Generate a random DAG on N nodes.
    For each pair (i,j) with i < j, add edge i -> j with probability p.
    Then compute transitive closure to get the partial order.
    """
    # Direct edges
    adj = np.eye(N)
    for i in range(N):
        for j in range(i + 1, N):
            if np.random.random() < p:
                adj[i, j] = 1.0

    # Transitive closure (Floyd-Warshall)
    zeta = adj.copy()
    for k in range(N):
        for i in range(N):
            for j in range(N):
                if zeta[i, k] > 0.5 and zeta[k, j] > 0.5:
                    zeta[i, j] = 1.0

    return zeta


def test_random_dag():
    print("\n" + "=" * 80)
    print("TEST 4: RANDOM DAG (NO GEOMETRY)")
    print("  Random DAG on N=20 nodes, edge probability p=0.3.")
    print("  Transitive closure gives a poset. Test d=2 chamber.")
    print("  There is NO reason for the gap law to hold here.")
    print("=" * 80)

    d = 2
    target = (d + 1) / (d - 1)
    N = 20
    p = 0.3

    ratios = []
    n_trials = 10

    for trial in range(n_trials):
        np.random.seed(42 + trial * 37)
        zeta = random_dag_zeta(N, p)

        n_relations = int(np.sum(zeta) - N)
        density = n_relations / (N * (N - 1))

        K, states, idx = build_chamber_kernel(zeta, d)
        R = build_reflection_poset(states, idx, N, d)

        R2_err = np.max(np.abs(R @ R - np.eye(len(states))))
        RK_err = np.max(np.abs(R @ K - K @ R))

        le, lo, ee, eo, pairing = analyze_sectors(K, R)

        if le is not None and lo is not None and abs(lo) > 1e-8:
            ratio = le / lo
            ratios.append(ratio)
        else:
            ratio = None

        if trial < 3:
            print(f"\n  Trial {trial}: density={density:.3f}, "
                  f"R^2 err={R2_err:.4f}, [R,K]={RK_err:.4f}")
            if ratio is not None:
                print(f"    le={le:.4f}, lo={lo:.4f}, le/lo={ratio:.6f}")
                if pairing is not None:
                    print(f"    Pairing error: {pairing:.2e}")
            else:
                print(f"    Could not compute ratio")

    if ratios:
        mean_r = np.mean(ratios)
        std_r = np.std(ratios)
        print(f"\n  Over {len(ratios)} trials:")
        print(f"  le/lo = {mean_r:.4f} +/- {std_r:.4f}  (lattice target = {target:.4f})")
        print(f"  Deviation from target: {abs(mean_r - target)/target*100:.1f}%")
        print(f"  Individual ratios: {[round(r, 4) for r in ratios]}")


# ============================================================================
# TEST 5: BENINCASA-DOWKER D'ALEMBERTIAN
# ============================================================================

def links_and_2links(zeta):
    """
    Compute links and 2-links from a causal matrix.
    Link(i,j): zeta[i,j]=1 and no k with zeta[i,k]=zeta[k,j]=1 (i<k<j).
    2-link(i,j): exactly one intermediate k.
    """
    N = zeta.shape[0]

    # Number of intermediate elements between i and j
    n_between = np.zeros((N, N), dtype=int)
    for i in range(N):
        for j in range(N):
            if zeta[i, j] > 0.5 and i != j:
                for k in range(N):
                    if k != i and k != j and zeta[i, k] > 0.5 and zeta[k, j] > 0.5:
                        n_between[i, j] += 1

    link = np.zeros((N, N))
    twolink = np.zeros((N, N))

    for i in range(N):
        for j in range(N):
            if zeta[i, j] > 0.5 and i != j:
                if n_between[i, j] == 0:
                    link[i, j] = 1.0
                elif n_between[i, j] == 1:
                    twolink[i, j] = 1.0

    return link, twolink


def benincasa_dowker_2d(zeta, l_sq=1.0):
    """
    Benincasa-Dowker d'Alembertian in 2D (retarded + advanced, symmetrized).

    Retarded: Box_ret f(x) = (2/l^2) * [-f(x) + sum_{y>x: link} f(y)
                               - (1/2) sum_{y>x: 2-link} f(y)]
    Advanced: Box_adv f(x) = (2/l^2) * [-f(x) + sum_{y<x: link} f(y)
                               - (1/2) sum_{y<x: 2-link} f(y)]

    We return the symmetrized version (Box_ret + Box_adv) / 2 for spectral analysis,
    as well as the raw retarded version.
    """
    N = zeta.shape[0]
    link, twolink = links_and_2links(zeta)

    # Retarded (future) part
    Box_ret = np.zeros((N, N))
    for x in range(N):
        Box_ret[x, x] = -1.0
        for y in range(N):
            if link[x, y] > 0.5:  # y in future of x
                Box_ret[x, y] += 1.0
            if twolink[x, y] > 0.5:
                Box_ret[x, y] -= 0.5
    Box_ret *= 2.0 / l_sq

    # Advanced (past) part: same formula but using link^T, twolink^T
    Box_adv = np.zeros((N, N))
    for x in range(N):
        Box_adv[x, x] = -1.0
        for y in range(N):
            if link[y, x] > 0.5:  # y in past of x
                Box_adv[x, y] += 1.0
            if twolink[y, x] > 0.5:
                Box_adv[x, y] -= 0.5
    Box_adv *= 2.0 / l_sq

    # Symmetrized
    Box_sym = (Box_ret + Box_adv) / 2.0

    return Box_ret, Box_adv, Box_sym


def test_benincasa_dowker():
    print("\n" + "=" * 80)
    print("TEST 5: BENINCASA-DOWKER D'ALEMBERTIAN")
    print("  Compare BD d'Alembertian spectrum with chamber kernel spectrum.")
    print("=" * 80)

    for N in [10, 15, 20]:
        print(f"\n  N = {N} points (1+1D Minkowski sprinkling)")
        np.random.seed(42)
        points = sprinkle_1plus1(N)
        zeta, points_sorted = causal_matrix_minkowski_1plus1(points)

        # BD d'Alembertian (retarded, advanced, symmetrized)
        Box_ret, Box_adv, Box_sym = benincasa_dowker_2d(zeta)

        # Retarded spectrum (complex in general)
        ret_evals = np.sort(np.linalg.eigvals(Box_ret).real)[::-1]
        # Symmetrized spectrum (real)
        sym_evals = np.sort(eigvalsh(Box_sym))[::-1]

        # Link/2-link counts
        link, twolink = links_and_2links(zeta)
        n_links = int(np.sum(link))
        n_2links = int(np.sum(twolink))

        # Chamber kernel d=2
        d = 2
        K, states, idx = build_chamber_kernel(zeta, d)
        K_sym_ch = (K + K.T) / 2
        k_evals = np.sort(eigvalsh(K_sym_ch))[::-1]

        print(f"    Links: {n_links}, 2-links: {n_2links}")
        print(f"    BD retarded spectrum (top 5): {ret_evals[:5].round(4)}")
        print(f"    BD symmetrized spectrum (top 5): {sym_evals[:5].round(4)}")
        print(f"    BD symmetrized spectrum (bot 5): {sym_evals[-5:].round(4)}")
        print(f"    K_F spectrum (top 5): {k_evals[:5].round(4)}")

        # Check spectral relationship using symmetrized BD
        nz_sym = sym_evals[np.abs(sym_evals) > 0.1]
        if len(nz_sym) >= 2:
            print(f"    BD sym nonzero eigs: {len(nz_sym)}, top ratio: {nz_sym[0]/nz_sym[1]:.4f}")
        if abs(k_evals[0]) > 1e-10 and abs(k_evals[1]) > 1e-10:
            print(f"    K_F top ratio: {k_evals[0]/k_evals[1]:.4f}")


# ============================================================================
# TEST 6: SPECTRAL DIMENSION COMPARISON
# ============================================================================

def spectral_dimension(L, t_range):
    """
    Compute spectral dimension d_s(t) = -2 d(log P(t))/d(log t)
    where P(t) = tr(e^{-tL}) / N.
    L should be a positive-semidefinite Laplacian.
    """
    evals = np.sort(eigvalsh(L))
    # Shift to make non-negative
    evals = evals - evals[0]
    N = len(evals)

    log_t = np.log(t_range)
    P_vals = np.array([np.sum(np.exp(-t * evals)) / N for t in t_range])

    # Avoid log(0)
    mask = P_vals > 1e-30
    log_P = np.log(P_vals[mask])
    log_t_m = log_t[mask]

    # Numerical derivative
    if len(log_t_m) < 3:
        return None, None

    d_s = -2 * np.gradient(log_P, log_t_m)

    return d_s, t_range[mask]


def test_spectral_dimension():
    print("\n" + "=" * 80)
    print("TEST 6: SPECTRAL DIMENSION COMPARISON")
    print("  For each causal set, compute:")
    print("  - Chamber le/lo ratio")
    print("  - Spectral dimension from the graph Laplacian")
    print("  - Spectral dimension from K_F")
    print("  Question: does the chamber gap encode the spectral dimension?")
    print("=" * 80)

    d = 2
    target = (d + 1) / (d - 1)
    t_range = np.logspace(-2, 2, 100)

    # 1+1D sprinkling
    for N in [20, 40]:
        print(f"\n  1+1D Minkowski, N={N}:")
        np.random.seed(42)
        points = sprinkle_1plus1(N)
        zeta, pts = causal_matrix_minkowski_1plus1(points)

        # Graph Laplacian from the Hasse diagram (links only)
        link, _ = links_and_2links(zeta)
        A_undirected = link + link.T
        A_undirected = np.minimum(A_undirected, 1.0)
        degree = np.diag(np.sum(A_undirected, axis=1))
        L_graph = degree - A_undirected

        d_s_graph, t_graph = spectral_dimension(L_graph, t_range)

        # Chamber kernel
        K, states, idx = build_chamber_kernel(zeta, d)
        K_sym = (K + K.T) / 2
        # Use -K as a "Laplacian" (K has large positive eigenvalues)
        max_eval = eigvalsh(K_sym)[-1]
        L_chamber = max_eval * np.eye(len(states)) - K_sym

        d_s_chamber, t_chamber = spectral_dimension(L_chamber, t_range)

        R = build_reflection_poset(states, idx, N, d)
        le, lo, ee, eo, pairing = analyze_sectors(K, R)

        if le is not None and lo is not None:
            ratio = le / lo
            print(f"    le/lo = {ratio:.4f}")

        if d_s_graph is not None:
            # Report spectral dimension at intermediate scale
            mid_idx = len(t_graph) // 2
            print(f"    Spectral dim (graph Laplacian) at t={t_graph[mid_idx]:.2f}: "
                  f"d_s = {d_s_graph[mid_idx]:.4f}")
            # Report range
            print(f"    d_s range (graph): [{np.min(d_s_graph):.2f}, {np.max(d_s_graph):.2f}]")

        if d_s_chamber is not None:
            mid_idx = len(t_chamber) // 2
            print(f"    Spectral dim (chamber) at t={t_chamber[mid_idx]:.2f}: "
                  f"d_s = {d_s_chamber[mid_idx]:.4f}")
            print(f"    d_s range (chamber): [{np.min(d_s_chamber):.2f}, {np.max(d_s_chamber):.2f}]")

    # 2+1D sprinkling
    N = 30
    print(f"\n  2+1D Minkowski, N={N}:")
    np.random.seed(42)
    points = sprinkle_2plus1(N)
    zeta, pts = causal_matrix_minkowski_2plus1(points)

    link, _ = links_and_2links(zeta)
    A_undirected = np.minimum(link + link.T, 1.0)
    degree = np.diag(np.sum(A_undirected, axis=1))
    L_graph = degree - A_undirected

    d_s_graph, t_graph = spectral_dimension(L_graph, t_range)

    K, states, idx = build_chamber_kernel(zeta, d)
    K_sym = (K + K.T) / 2
    max_eval = eigvalsh(K_sym)[-1]
    L_chamber = max_eval * np.eye(len(states)) - K_sym

    d_s_chamber, t_chamber = spectral_dimension(L_chamber, t_range)

    R = build_reflection_poset(states, idx, N, d)
    le, lo, ee, eo, pairing = analyze_sectors(K, R)

    if le is not None and lo is not None:
        print(f"    le/lo = {le/lo:.4f}")

    if d_s_graph is not None:
        mid_idx = len(t_graph) // 2
        print(f"    Spectral dim (graph) at t={t_graph[mid_idx]:.2f}: d_s = {d_s_graph[mid_idx]:.4f}")
    if d_s_chamber is not None:
        mid_idx = len(t_chamber) // 2
        print(f"    Spectral dim (chamber) at t={t_chamber[mid_idx]:.2f}: d_s = {d_s_chamber[mid_idx]:.4f}")


# ============================================================================
# ADDITIONAL: Direct full-spectrum analysis without R
# ============================================================================

def test_full_spectrum_no_symmetry():
    """
    For causal sets that lack the R-symmetry, analyze the full K_F spectrum
    directly. Look for universal features.
    """
    print("\n" + "=" * 80)
    print("BONUS: FULL SPECTRUM ANALYSIS (no R-symmetry assumed)")
    print("  For each causal set, examine the eigenvalue distribution of K_F.")
    print("=" * 80)

    d = 2

    # Lattice (baseline)
    m = 10
    zeta_lat = np.zeros((m, m))
    for i in range(m):
        for j in range(m):
            if i <= j:
                zeta_lat[i, j] = 1.0
    K_lat, _, _ = build_chamber_kernel(zeta_lat, d)
    K_lat_sym = (K_lat + K_lat.T) / 2
    evals_lat = np.sort(eigvalsh(K_lat_sym))[::-1]
    print(f"\n  Lattice m=10, d=2: top evals = {evals_lat[:6].round(4)}")
    print(f"    Ratio e1/e2 = {evals_lat[0]/evals_lat[1]:.6f}")
    if abs(evals_lat[2]) > 1e-10:
        print(f"    Ratio e2/e3 = {evals_lat[1]/evals_lat[2]:.6f}")

    # Minkowski 1+1D
    for N in [20, 30]:
        np.random.seed(42)
        points = sprinkle_1plus1(N)
        zeta, _ = causal_matrix_minkowski_1plus1(points)
        K, _, _ = build_chamber_kernel(zeta, d)
        K_sym = (K + K.T) / 2
        evals = np.sort(eigvalsh(K_sym))[::-1]
        evals_nz = evals[np.abs(evals) > 1e-8]
        print(f"\n  1+1D N={N}, d=2: top evals = {evals_nz[:6].round(4)}")
        if len(evals_nz) >= 2:
            print(f"    Ratio e1/e2 = {evals_nz[0]/evals_nz[1]:.6f}")
        if len(evals_nz) >= 3 and abs(evals_nz[2]) > 1e-10:
            print(f"    Ratio e2/e3 = {evals_nz[1]/evals_nz[2]:.6f}")

    # Random DAG
    N = 20
    np.random.seed(42)
    zeta = random_dag_zeta(N, 0.3)
    K, _, _ = build_chamber_kernel(zeta, d)
    K_sym = (K + K.T) / 2
    evals = np.sort(eigvalsh(K_sym))[::-1]
    evals_nz = evals[np.abs(evals) > 1e-8]
    print(f"\n  Random DAG N={N}, p=0.3, d=2: top evals = {evals_nz[:6].round(4)}")
    if len(evals_nz) >= 2:
        print(f"    Ratio e1/e2 = {evals_nz[0]/evals_nz[1]:.6f}")


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    print("CAUSAL SET THEORY vs CHAMBER SPECTRAL THEORY")
    print("Testing whether the chamber gap law le/lo = (d+1)/(d-1)")
    print("holds for causal sets from Minkowski sprinklings.\n")

    # Test 1: Sanity check
    test_regular_lattice()

    # Test 2: 1+1D Minkowski
    test_minkowski_1plus1()

    # Test 3: 2+1D Minkowski
    test_minkowski_2plus1()

    # Test 4: Random DAGs
    test_random_dag()

    # Test 5: Benincasa-Dowker
    test_benincasa_dowker()

    # Test 6: Spectral dimension
    test_spectral_dimension()

    # Bonus: full spectrum
    test_full_spectrum_no_symmetry()

    print("\n" + "=" * 80)
    print("SUMMARY OF RESULTS")
    print("=" * 80)
    print("""
TEST 1 (Lattice sanity check): PASSED with caveats.
  - Parity pairing lambda_2^even = lambda_1^odd: EXACT (error < 1e-15).
  - Gap law le/lo -> (d+1)/(d-1): CONVERGING but slowly.
    d=2: 2.71 -> 2.74 -> 2.77 (target 3.00) at m=6,8,10
    d=3: 1.79 -> 1.84 -> 1.87 (target 2.00)
    d=4: 1.45 -> 1.52 (target 1.67)
  - The gap law is ASYMPTOTIC (m -> infinity), not exact at finite m.

TEST 2 (1+1D Minkowski sprinkling): GAP LAW FAILS.
  - R does NOT commute with K ([R,K] error = 2.0). The reflection symmetry
    of the total order has NO analog in random causal sets.
  - Even with forced sector decomposition, le/lo ~ 1.1 to 1.9
    (target 3.0), with 48-63% deviation and high variance.
  - Parity pairing: BROKEN (errors ~ 0.1 to 0.5).

TEST 3 (2+1D Minkowski sprinkling): GAP LAW FAILS.
  - Same story: le/lo ~ 1.2 to 1.4, target 3.0, deviation ~55-60%.

TEST 4 (Random DAGs): GAP LAW FAILS.
  - le/lo = 1.60 +/- 0.45 across 10 trials (target 3.0).
  - Huge variance (individual values from 1.13 to 2.73).
  - No universal ratio emerges.

TEST 5 (Benincasa-Dowker d'Alembertian):
  - BD retarded operator has all eigenvalues = -2 (artifact of the
    purely upper-triangular structure after topological sorting).
  - BD symmetrized operator has nontrivial spectrum with both positive
    and negative eigenvalues.
  - NO clear spectral relationship between BD and K_F.
    The operators live on different spaces (N points vs C(N,d) pairs).

TEST 6 (Spectral dimension):
  - Graph Laplacian spectral dimension: d_s ~ 1.5 for 1+1D (close to 2),
    d_s ~ 1.9 for 2+1D (close to 2).
  - Chamber K_F spectral dimension: not meaningful at intermediate scales
    (highly dependent on the diffusion time parameter).
  - No clear connection between chamber le/lo and spectral dimension.

FULL SPECTRUM (Bonus):
  - Lattice: e1/e2 = 2.77 (matches le/lo = gap law).
    The e2 = e3 degeneracy reflects the parity pairing.
  - Minkowski sprinklings: e1/e2 ~ 1.2 to 1.4, NO degeneracy.
  - Random DAG: e1/e2 ~ 1.28, NO degeneracy.

HONEST CONCLUSIONS:

1. The chamber gap law le/lo = (d+1)/(d-1) is SPECIFIC to total orders.
   It does NOT hold for causal sets from Minkowski sprinklings or random DAGs.

2. The FUNDAMENTAL OBSTRUCTION is the absence of an order-reversing involution
   R in generic causal sets. Without R, there are no even/odd sectors,
   and the gap law as stated is meaningless.

3. The parity pairing lambda_2^even = lambda_1^odd is EXACT for lattices
   but BROKEN for generic posets.

4. The chamber kernel K_F is still well-defined for any poset, and its
   spectrum carries information about the causal structure. But the
   UNIVERSAL RATIOS specific to total orders do not survive.

5. The Benincasa-Dowker d'Alembertian and K_F are fundamentally different:
   BD operates on N points (scalar fields on the causal set),
   K_F operates on C(N,d) pairs (d-tuples in the Weyl chamber).
   Any connection would need to go through the exterior algebra functor.

6. OPEN QUESTION: Is there a MODIFIED gap law for causal sets?
   The Minkowski sprinklings consistently give le/lo ~ 1.3-1.5 for d=2.
   This might stabilize to a different universal constant that depends
   on the spacetime dimension (not just d).
""")
