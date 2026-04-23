#!/usr/bin/env python3
"""
Reproducible verification that |CC([n] x [3])| is a polynomial of degree
exactly 6 in n, with the closed form

    |CC([n] x [3])| = C(n,0) + 6 C(n,1) + 20 C(n,2) + 35 C(n,3)
                    + 36 C(n,4) + 20 C(n,5) + 5 C(n,6).

Proof outline (see docs/Width3PolynomialProof.md for the full writeup):

  1. Build the 10-state transfer matrix T on states
     {F(0), F(1), F(2), F(3), B(0,0), B(0,1), B(0,2), B(1,1), B(1,2), B(2,2)}
     encoding the antitone-boundary characterization of order-convex subsets
     (SlabCharacterization.lean).
  2. Compute charpoly(T) = (lambda - 1)^10 symbolically.
  3. By Cayley-Hamilton, (T - I)^10 = 0, so N := T - I is nilpotent.
  4. T^n = sum_{k=0..9} C(n,k) N^k; hence
     a(n) = v0^T T^n 1 = sum_{k=0..9} c_k C(n,k) with c_k = v0^T N^k 1.
  5. Compute c_k for k=0..9 directly: c_7 = c_8 = c_9 = 0, so degree = 6.

This script is self-contained (sympy only) and runs in well under a second.
"""

from math import comb
from sympy import Matrix, eye, ones, zeros, symbols, factor

# Width-3 grid parameters.
W = 3
N_F = W + 1                  # F(0), F(1), F(2), F(3)
N_B = W * (W + 1) // 2       # B(L,R) with 0 <= L <= R <= W-1
N = N_F + N_B                # 10


def F_idx(k: int) -> int:
    return k


def B_idx(L: int, R: int) -> int:
    offset = (W + 1) + L * W - L * (L - 1) // 2
    return offset + (R - L)


def build_transfer_matrix():
    """TM rows indexed by source state, columns by target. Entry = multiplicity."""
    T = [[0] * N for _ in range(N)]

    # From F(k):
    #   - empty row -> F(k)                               (1 way)
    #   - start block (L', R') with R' < k (or R' < W if k = W)
    for k in range(N_F):
        T[k][F_idx(k)] += 1
        R_cap = min(k, W) if k < W else W
        for L_new in range(W):
            for R_new in range(L_new, R_cap):
                T[k][B_idx(L_new, R_new)] += 1

    # From B(L, R):
    #   - end block (next row empty)   -> F(L)             (1 way)
    #   - continue block with L' <= L and L' <= R' <= R
    for L in range(W):
        for R in range(L, W):
            src = B_idx(L, R)
            T[src][F_idx(L)] += 1
            for L_new in range(L + 1):
                for R_new in range(L_new, R + 1):
                    T[src][B_idx(L_new, R_new)] += 1

    return Matrix(T)


def main():
    T = build_transfer_matrix()
    print(f"Transfer matrix shape: {T.shape}")

    # Initial state = F(W) (no prior block).  Observable = sum over all final states.
    v0 = zeros(N, 1); v0[F_idx(W), 0] = 1
    one = ones(N, 1)

    # Sanity: reproduce the first 11 values.
    expected = [1, 7, 33, 114, 321, 781, 1702, 3403, 6349, 11191, 18811]
    Tn = eye(N)
    print("\nSanity check  a(n) = v0^T T^n 1:")
    for n in range(11):
        val = int((v0.T * Tn * one)[0, 0])
        mark = "OK" if val == expected[n] else f"MISMATCH (expected {expected[n]})"
        print(f"  n={n:2d}: {val:>7}  {mark}")
        Tn = Tn * T

    # Characteristic polynomial of T.
    lam = symbols("lam")
    cp = T.charpoly(lam).as_expr()
    cp_f = factor(cp)
    print(f"\ncharpoly(T) = {cp_f}")
    assert cp_f == (lam - 1) ** N, "charpoly is not (lambda - 1)^10"

    # By Cayley-Hamilton, (T - I)^N = 0.  Verify directly.
    I_N = eye(N)
    N_mat = T - I_N
    assert (N_mat ** N) == zeros(N, N), "(T - I)^N should be the zero matrix"
    print(f"(T - I)^{N} = 0   [Cayley-Hamilton, verified]")

    # Compute c_k = v0^T (T - I)^k 1 for k = 0..9.
    c = []
    Mk = I_N
    for k in range(N):
        c.append(int((v0.T * Mk * one)[0, 0]))
        Mk = Mk * N_mat
    print("\nCoefficients c_k = v0^T (T-I)^k 1:")
    for k, ck in enumerate(c):
        print(f"  c_{k} = {ck}")

    degree = max(k for k, ck in enumerate(c) if ck != 0)
    assert degree == 6, f"expected degree 6, got {degree}"
    print(f"\nDegree of a(n) as polynomial in n: {degree}")

    # Closed form:  a(n) = sum_k c_k * C(n, k)
    def P(n: int) -> int:
        return sum(c[k] * comb(n, k) for k in range(N))

    # Verify P(n) matches TM for n = 0..20.
    vals_tm = [
        1, 7, 33, 114, 321, 781, 1702, 3403, 6349, 11191, 18811,
        30372, 47373, 71709, 105736, 152341, 215017, 297943, 406069, 545206, 722121,
    ]
    ok = all(P(n) == vals_tm[n] for n in range(21))
    print(f"\nClosed-form P(n) matches TM for n = 0..20: {ok}")
    assert ok

    # Pretty-print the closed form.
    terms = [f"{c[k]}*C(n,{k})" for k in range(degree + 1) if c[k] != 0]
    print("\nClosed form:")
    print(f"  |CC([n] x [3])| = {' + '.join(terms)}")


if __name__ == "__main__":
    main()
