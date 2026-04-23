# OEIS submission draft: |CC([n] × [4])|

Not currently in OEIS as of 2026-04-23 (verified via
`curl "https://oeis.org/search?q=1,11,71,321,1146,3449,9115,21743&fmt=text"`
and a few shorter prefixes — all returned "No results").

Companion sequence to `A393665` (square case `|CC([m]²)|`).

## Record

```
%I Annnnnnn
%S Annnnnnn 1,11,71,321,1146,3449,9115,21743,47737,97861,189377,348899,
%T Annnnnnn 616110,1048503,1727321,2764885,4313513,6576247,9819619,
%U Annnnnnn 14388701,20724698,29385357,41068479,56638835,77158801
%N Annnnnnn Number of order-convex subsets of the grid poset [n] x [4] with componentwise partial order.
%C Annnnnnn A subset S of [n] x [4] = {1,...,n} x {1,2,3,4} with componentwise order is order-convex if whenever a, b in S with a <= c <= b, then c in S. Equivalently, S is the intersection of a downset and an upset.
%C Annnnnnn a(n) is a polynomial in n of degree exactly 8 with leading coefficient 1/2880. See %F for the closed form.
%C Annnnnnn The sequence can be computed by a 15-state transfer matrix T whose characteristic polynomial is (lambda - 1)^15; Cayley-Hamilton gives (T - I)^15 = 0 and a(n) = v0^T T^n 1 expands as a Newton series in C(n,k) that terminates at k = 8.
%C Annnnnnn Companion to A393665 (|CC([m]^2)|, the square case). Consistency: a(4) = 1146 = A393665(4), since [4] x [4] = [4]^2.
%C Annnnnnn Barnette, Nichols, and Richmond (2019) gave exact formulas for the number of order-convex subsets of [n] x [m] for small fixed m; this sequence realizes their count at m = 4 in closed form.
%D Annnnnnn B. Barnette, W. Nichols, and T. Richmond, The number of convex sets in a product of totally ordered sets, Rocky Mountain J. Math., 49 (2019), no. 2, 369-385.
%F Annnnnnn a(n) = C(n,0) + 10*C(n,1) + 50*C(n,2) + 140*C(n,3) + 245*C(n,4) + 273*C(n,5) + 191*C(n,6) + 77*C(n,7) + 14*C(n,8).
%F Annnnnnn a(n) = n^8/2880 + n^7/180 + 9*n^6/160 + 13*n^5/45 + 361*n^4/320 + 409*n^3/180 + 2747*n^2/720 + 73*n/30 + 1.
%F Annnnnnn 2880*a(n) = n^8 + 16*n^7 + 162*n^6 + 832*n^5 + 3249*n^4 + 6544*n^3 + 10988*n^2 + 7008*n + 2880.
%H Annnnnnn Thomas DiFiore, <a href="https://github.com/tomdif/causal-algebraic-geometry-lean">Lean 4 formal verification and sympy reproduction</a>.
%H Annnnnnn B. Barnette, W. Nichols, and T. Richmond, <a href="https://doi.org/10.1216/RMJ-2019-49-2-369">The number of convex sets in a product of totally ordered sets</a>, Rocky Mountain J. Math. 49(2): 369-385 (2019).
%e Annnnnnn a(1) = 11: for [1] x [4] (a single row of 4 cells), the order-convex subsets are the empty set and the 10 = C(5,2) contiguous intervals.
%e Annnnnnn a(2) = 71 (see scripts/width4_polynomial_proof.py for the enumeration).
%o Annnnnnn (Python) # Transfer-matrix computation (see repo scripts/width4_polynomial_proof.py for asserts / brute-force cross-check):
%o Annnnnnn from sympy import Matrix, eye, ones, zeros
%o Annnnnnn W = 4; N_F = W+1; N_B = W*(W+1)//2; N = N_F+N_B  # = 15
%o Annnnnnn def Fi(k): return k
%o Annnnnnn def Bi(L,R):
%o Annnnnnn     off = (W+1) + L*W - L*(L-1)//2
%o Annnnnnn     return off + (R-L)
%o Annnnnnn T = [[0]*N for _ in range(N)]
%o Annnnnnn for k in range(N_F):
%o Annnnnnn     T[Fi(k)][Fi(k)] += 1
%o Annnnnnn     Rcap = k if k < W else W
%o Annnnnnn     for Ln in range(W):
%o Annnnnnn         for Rn in range(Ln, Rcap):
%o Annnnnnn             T[Fi(k)][Bi(Ln,Rn)] += 1
%o Annnnnnn for L in range(W):
%o Annnnnnn     for R in range(L, W):
%o Annnnnnn         T[Bi(L,R)][Fi(L)] += 1
%o Annnnnnn         for Ln in range(L+1):
%o Annnnnnn             for Rn in range(Ln, R+1):
%o Annnnnnn                 T[Bi(L,R)][Bi(Ln,Rn)] += 1
%o Annnnnnn M = Matrix(T); v0 = zeros(N,1); v0[Fi(W),0] = 1; one_ = ones(N,1)
%o Annnnnnn def a(n):
%o Annnnnnn     Tn = eye(N)
%o Annnnnnn     for _ in range(n): Tn = Tn*M
%o Annnnnnn     return int((v0.T*Tn*one_)[0,0])
%o Annnnnnn # closed form:
%o Annnnnnn from math import comb
%o Annnnnnn c = [1,10,50,140,245,273,191,77,14]
%o Annnnnnn def A(n): return sum(c[k]*comb(n,k) for k in range(9))
%Y Annnnnnn Row m=4 of the table |CC([n] x [m])|; cf. A393665 (m=n, diagonal of that table).
%K Annnnnnn nonn,easy
%O Annnnnnn 0,2
%A Annnnnnn Thomas DiFiore, Apr 23 2026
```

## Notes for submitter

- `%O` = `0,2` means offset 0 (first term is `a(0) = 1`), and the first
  term greater than 1 appears at index 2. Confirm with OEIS editor.
- Cross-ref to `A393665` (diagonal square case, same author). If the
  width-3 submission lands as `Amxxxxxx`, also add `%Y A<m=3 case>`.
- `%e` for `a(2) = 71` is left abbreviated; OEIS editors may want a
  full listing. The 71 subsets are: empty (1) + 10 singletons (10, one
  per cell) + 2-cell comparable pairs + larger order-convex sets.
  An exhaustive listing is bulky; the script provides brute-force
  verification.
- Degree-8 polynomial is unambiguous given 9 terms; providing 25 terms
  is conservative. Trim to ~15 if the editor prefers.

## Verification checklist before submission

- [x] Transfer matrix matches brute force for n = 0..4 (see
      `scripts/width4_polynomial_proof.py`).
- [x] `charpoly(T) = (λ - 1)^15` (sympy).
- [x] Closed form `sum c_k C(n,k)` matches TM for n = 0..24.
- [x] `a(4) = 1146 = A393665(4)` cross-check.
- [x] Not currently in OEIS (checked 2026-04-23: prefixes
      `1,11,71,321,1146,3449,9115,21743` and `11,71,321,1146,3449`
      and `71,321,1146,3449` all return "No results").
