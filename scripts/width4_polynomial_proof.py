#!/usr/bin/env python3
"""
Reproducible verification that |CC([n] x [4])| is a polynomial of degree
exactly 8 in n, with the closed form

    |CC([n] x [4])| = C(n,0) + 10 C(n,1) + 50 C(n,2) + 140 C(n,3)
                    + 245 C(n,4) + 273 C(n,5) + 191 C(n,6)
                    +  77 C(n,7) +  14 C(n,8).

Proof outline (mirrors scripts/width3_polynomial_proof.py):

  1. Build the 15-state transfer matrix T on states
         F(0), F(1), F(2), F(3), F(4),
         B(L,R) for 0 <= L <= R <= 3
     encoding the antitone-boundary characterization of order-convex
     subsets (SlabCharacterization.lean specialized to d=2, width=4).
  2. Compute charpoly(T) = (lambda - 1)^15 symbolically.
  3. By Cayley-Hamilton, (T - I)^15 = 0, so N := T - I is nilpotent.
  4. T^n = sum_{k=0..14} C(n,k) N^k; hence
     a(n) = v0^T T^n 1 = sum_{k=0..14} c_k C(n,k) with c_k = v0^T N^k 1.
  5. Compute c_k for k=0..14 directly; c_9..c_14 vanish, so the degree
     is 8 and the Newton-series closed form is as stated above.

The script also includes a brute-force cross-check for n = 0..4
(2^(4n) subsets, up to 2^16 = 65536 at n=4) before any novel claim.

Self-contained (sympy only) and runs in a few seconds.
"""

from math import comb
from sympy import Matrix, eye, ones, zeros, symbols, factor, Rational, expand, Poly, factorial

# Width-4 grid parameters.
W = 4
N_F = W + 1                  # F(0), F(1), F(2), F(3), F(4)
N_B = W * (W + 1) // 2       # B(L,R) with 0 <= L <= R <= W-1  ==>  10
N = N_F + N_B                # 15


def F_idx(k: int) -> int:
    return k


def B_idx(L: int, R: int) -> int:
    # Pairs (L,R) with 0 <= L <= R <= W-1 in lex order:
    #   (0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)
    offset = (W + 1) + L * W - L * (L - 1) // 2
    return offset + (R - L)


def build_transfer_matrix(w=W):
    """TM rows = source state, columns = target.  Entry = number of ways
    to go from source to target given one additional grid row.

    State semantics (matching the width-3 script):
      F(k)   : no currently active block; any future block must have
               right edge R' < k  (k = w means unconstrained).
      B(L,R) : currently active block spanning columns [L, R].

    Transitions come from the slab rules of SlabCharacterization.lean
    (see docs/Width4PolynomialProof.md, Step 1).
    """
    n_F = w + 1
    n_B = w * (w + 1) // 2
    n = n_F + n_B

    def F_(k): return k

    def B_(L, R):
        off = (w + 1) + L * w - L * (L - 1) // 2
        return off + (R - L)

    T = [[0] * n for _ in range(n)]

    # From F(k):
    #   - empty row -> F(k)                                    (1 way)
    #   - start a new block (L', R') where R' < min(k, w)      (one each)
    for k in range(n_F):
        T[F_(k)][F_(k)] += 1
        R_cap = k if k < w else w
        for L_new in range(w):
            for R_new in range(L_new, R_cap):
                T[F_(k)][B_(L_new, R_new)] += 1

    # From B(L, R):
    #   - end block (next row empty) -> F(L)                  (1 way)
    #   - continue block with L' <= L and L' <= R' <= R
    for L in range(w):
        for R in range(L, w):
            src = B_(L, R)
            T[src][F_(L)] += 1
            for L_new in range(L + 1):
                for R_new in range(L_new, R + 1):
                    T[src][B_(L_new, R_new)] += 1

    return Matrix(T)


def is_order_convex(S_set):
    """S_set: frozenset of (i,j).  Componentwise order-convex iff for every
    a <= b in S, the whole box [a, b] is in S."""
    pts = list(S_set)
    for a in pts:
        for b in pts:
            if a[0] <= b[0] and a[1] <= b[1]:
                for i in range(a[0], b[0] + 1):
                    for j in range(a[1], b[1] + 1):
                        if (i, j) not in S_set:
                            return False
    return True


def count_bf(n, w):
    cells = [(i, j) for i in range(n) for j in range(w)]
    total = 1 << (n * w)
    cnt = 0
    for mask in range(total):
        S = frozenset(cells[k] for k in range(n * w) if (mask >> k) & 1)
        if is_order_convex(S):
            cnt += 1
    return cnt


def tm_values(T, v0, one, n_max):
    out = []
    Tn = eye(T.shape[0])
    for _ in range(n_max + 1):
        out.append(int((v0.T * Tn * one)[0, 0]))
        Tn = Tn * T
    return out


def main():
    T = build_transfer_matrix(W)
    print(f"Transfer matrix shape: {T.shape}   (W={W}, N_F={N_F}, N_B={N_B}, N={N})")

    v0 = zeros(N, 1); v0[F_idx(W), 0] = 1
    one = ones(N, 1)

    # ---- Brute-force cross-check for n = 0..4 ----
    print("\nBrute-force vs transfer matrix (n = 0..4):")
    tm_vals_small = tm_values(T, v0, one, 4)
    bf_vals = [1]
    for n in range(1, 5):
        bf_vals.append(count_bf(n, W))
    for n in range(5):
        status = "OK" if tm_vals_small[n] == bf_vals[n] else \
                 f"MISMATCH (TM={tm_vals_small[n]}, BF={bf_vals[n]})"
        print(f"  n={n}: TM={tm_vals_small[n]:>7}  BF={bf_vals[n]:>7}  {status}")
        assert tm_vals_small[n] == bf_vals[n], f"TM disagrees with brute force at n={n}"

    # ---- Characteristic polynomial ----
    lam = symbols("lam")
    cp = T.charpoly(lam).as_expr()
    cp_f = factor(cp)
    print(f"\ncharpoly(T) = {cp_f}")
    assert cp_f == (lam - 1) ** N, f"charpoly is not (lambda - 1)^{N}"

    # ---- Cayley-Hamilton / nilpotency ----
    I_N = eye(N)
    M = T - I_N
    assert (M ** N) == zeros(N, N), f"(T - I)^{N} should be zero"
    print(f"(T - I)^{N} = 0   [Cayley-Hamilton, verified directly]")

    # ---- Compute c_k = v0^T (T - I)^k 1 for k = 0..N-1 ----
    c = []
    Mk = I_N
    for k in range(N):
        c.append(int((v0.T * Mk * one)[0, 0]))
        Mk = Mk * M
    print("\nCoefficients c_k = v0^T (T-I)^k 1:")
    for k, ck in enumerate(c):
        print(f"  c_{k:>2} = {ck}")

    degree = max(k for k, ck in enumerate(c) if ck != 0)
    assert degree == 8, f"expected degree 8, got {degree}"
    print(f"\nDegree of a(n) as polynomial in n: {degree}")

    # ---- Verify closed form against TM for n = 0..24 ----
    def P(n_val):
        return sum(c[k] * comb(n_val, k) for k in range(N))

    tm_vals_long = tm_values(T, v0, one, 24)
    ok = all(P(n_val) == tm_vals_long[n_val] for n_val in range(25))
    print(f"\nClosed-form P(n) matches TM for n = 0..24: {ok}")
    assert ok

    print("\nFirst 25 values of a(n) = |CC([n] x [4])|:")
    for n_val in range(25):
        print(f"  a({n_val:2d}) = {tm_vals_long[n_val]}")

    terms = [f"{c[k]}*C(n,{k})" for k in range(degree + 1) if c[k] != 0]
    print("\nClosed form (Newton series):")
    print(f"  |CC([n] x [4])| = {' + '.join(terms)}")

    n_sym = symbols("n")

    def Cbin(nn, kk):
        prod = Rational(1)
        for i in range(kk):
            prod *= (nn - i)
        return prod / factorial(kk)

    poly_expr = sum(c[k] * Cbin(n_sym, k) for k in range(N))
    poly_expanded = expand(poly_expr)
    p = Poly(poly_expanded, n_sym)
    print("\nMonomial form:")
    print(f"  a(n) = {poly_expanded}")

    print("\nMonomial coefficients (high to low):")
    for (mono_deg,), coef in sorted(p.as_dict().items(), reverse=True):
        print(f"  n^{mono_deg}: {coef}")

    leading = p.LC()
    print(f"\nLeading coefficient (n^{degree}): {leading}")
    if leading != 0:
        print(f"  (= 1/{1 / leading})")


if __name__ == "__main__":
    main()
