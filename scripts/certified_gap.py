"""
Arbitrary-precision computation of γ₂ using full mpmath eigensolver.

The bottleneck in koornwinder_galerkin.py was scipy.eigh (double precision).
Here we use mpmath.eigsy for the eigendecomposition, keeping ALL steps
in extended precision. This should give digits limited only by the
Galerkin truncation order P, not by floating-point precision.
"""
import mpmath
import time

# Set precision
DIGITS = 40
mpmath.mp.dps = DIGITS + 20  # extra guard digits

def si(a, b):
    """∫_Σ u^a v^b dA = a! b! / (a+b+2)! in extended precision."""
    return mpmath.beta(a + 1, b + 1) / (a + b + 2)

def K_mono(a, b):
    """(K u^a v^b)(u,v) as {(α,β): coeff} in exact rationals."""
    B = b + 1
    result = {}
    for j in range(B + 1):
        key = (a + j + 1, 0)
        # (-1)^j * C(B,j) / (B * (a+j+1))
        coeff = mpmath.mpf((-1)**j * int(mpmath.binomial(B, j))) / (B * (a + j + 1))
        result[key] = result.get(key, mpmath.mpf(0)) + coeff
    key2 = (a + 1, B)
    result[key2] = result.get(key2, mpmath.mpf(0)) - mpmath.mpf(1) / (B * (a + 1))
    return result

def solve_full_mpmath(P):
    """Full mpmath Galerkin solve at degree P."""
    t0 = time.time()

    # Full basis (no BC constraint)
    basis = [(a, total - a) for total in range(P + 1) for a in range(total + 1)]
    n = len(basis)

    # Build mass matrix B and stiffness matrix A in mpmath
    B_mat = mpmath.matrix(n, n)
    A_mat = mpmath.matrix(n, n)

    for i in range(n):
        ai, bi = basis[i]
        for j in range(i, n):
            aj, bj = basis[j]
            B_mat[i, j] = B_mat[j, i] = si(ai + aj, bi + bj)

    t1 = time.time()

    for j in range(n):
        aj, bj = basis[j]
        Kcoeffs = K_mono(aj, bj)
        for i in range(n):
            ai, bi = basis[i]
            val = mpmath.mpf(0)
            for (alpha, beta), c in Kcoeffs.items():
                val += c * si(ai + alpha, bi + beta)
            A_mat[i, j] = val

    # Symmetrize
    A_sym = mpmath.matrix(n, n)
    for i in range(n):
        for j in range(n):
            A_sym[i, j] = (A_mat[i, j] + A_mat[j, i]) / 2

    t2 = time.time()

    # Cholesky: B = L L^T
    L = mpmath.cholesky(B_mat)
    L_inv = L ** (-1)

    # M = L^{-1} A_sym L^{-T}
    M = L_inv * A_sym * L_inv.T

    t3 = time.time()

    # Full eigendecomposition in mpmath
    # mpmath.eigsy returns (eigenvalues, eigenvectors) for symmetric matrix
    evals, evecs = mpmath.eigsy(M)

    t4 = time.time()

    # Find principal eigenvalue (largest)
    max_idx = 0
    for i in range(1, n):
        if evals[i] > evals[max_idx]:
            max_idx = i

    lam_s = evals[max_idx]
    z = evecs[:, max_idx]  # eigenvector in orthonormalized basis

    # Transform back: C = L^{-T} z
    C = L_inv.T * z

    # Normalize sign
    if C[0] < 0:
        C = -C

    lam_comp = 2 * lam_s

    t5 = time.time()

    # Compute gap: γ = 1 - <u+v>_{ψ²}
    norm2 = mpmath.mpf(0)
    u_mom = mpmath.mpf(0)
    v_mom = mpmath.mpf(0)
    for i in range(n):
        for j in range(n):
            prod = C[i] * C[j]
            ai, bi = basis[i]
            aj, bj = basis[j]
            norm2 += prod * si(ai + aj, bi + bj)
            u_mom += prod * si(ai + aj + 1, bi + bj)
            v_mom += prod * si(ai + aj, bi + bj + 1)

    gap = 1 - (u_mom + v_mom) / norm2

    t6 = time.time()

    return {
        'P': P, 'n': n,
        'lam_s': lam_s, 'lam_comp': lam_comp, 'gap': gap,
        'times': {
            'mass': t1 - t0, 'stiff': t2 - t1, 'cholesky': t3 - t2,
            'eigsy': t4 - t3, 'transform': t5 - t4, 'gap': t6 - t5,
        },
    }

# ============================================================
print("=" * 75)
print(f"ARBITRARY-PRECISION GALERKIN (mpmath, {DIGITS} target digits)")
print("=" * 75)
print()

prev_lam = mpmath.mpf(0)
prev_gap = mpmath.mpf(0)

for P in range(1, 14):
    r = solve_full_mpmath(P)
    dlam = abs(r['lam_comp'] - prev_lam) if prev_lam > 0 else mpmath.mpf(0)
    dgap = abs(r['gap'] - prev_gap) if prev_gap > 0 else mpmath.mpf(0)
    tt = r['times']
    total_t = sum(tt.values())

    print(f"  P={r['P']:2d}: n={r['n']:4d}")
    print(f"    λ_comp = {mpmath.nstr(r['lam_comp'], 30)}")
    print(f"    γ₂     = {mpmath.nstr(r['gap'], 30)}")
    print(f"    Δλ = {mpmath.nstr(dlam, 4)}, Δγ = {mpmath.nstr(dgap, 4)}")
    print(f"    [{total_t:.1f}s: mass={tt['mass']:.1f} stiff={tt['stiff']:.1f} "
          f"chol={tt['cholesky']:.1f} eig={tt['eigsy']:.1f}]")
    print()

    prev_lam = r['lam_comp']
    prev_gap = r['gap']

print("=" * 75)
print("FINAL RESULT")
print("=" * 75)
print(f"  λ_comp = {mpmath.nstr(prev_lam, DIGITS)}")
print(f"  γ₂     = {mpmath.nstr(prev_gap, DIGITS)}")
