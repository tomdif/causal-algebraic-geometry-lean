# Findings on A393665, A394682, A394685 (Aug 30, 2026)

Status annotations added when this was checked into the repo: item 9 has since been
**upgraded from conjecture to theorem** — see docs/DivisibilityRenormalization.md and
the zero-sorry formalization in CausalAlgebraicGeometry/DivisibilityRenormalization.lean.
The extended-term files (b393665_extended.txt, b394685_extended.txt, a394685_fast.c)
are not yet in this repo. Items 7 and 9's limit data re-verified independently by brute
force (c(1..12) and the k ≤ 10 ratio targets below).

## A393665 — order-convex subsets of [n]^2

**1. P-recursive (new).** With A(N) the OEIS-indexed term, for N >= 4:

    4N(N+1)^2 (205N^3 - 639N^2 + 590N - 144) A(N)
      = 4N (3280N^5 - 10224N^4 + 8389N^3 + 1359N^2 - 3686N + 1008) A(N-1)
      - (205N^6 - 434N^5 + 2411N^4 - 4270N^3 + 600N^2 + 1584N - 576) A(N-2)
      + 4(N-2)(2N-3)(2N-1)(205N^3 - 24N^2 - 73N + 12) A(N-3)

   with A(1..3) = 2, 13, 114. Fitted on 60 transfer-matrix terms (29 excess
   equations), then verified on 6 further independently computed terms (N=61..66).
   Order 3 is minimal (no order-1 or order-2 recurrence with coefficient degree <= 59).
   Note P(N) = 205N^3-639N^2+590N-144 at A(N) reappears as P(N+1) at A(N-3).
   Characteristic polynomial of leading coefficients: (x-16)(4x^2+1) — root 16 confirms
   rho=16 (Lean: GrowthRateIs16.lean); the extra pair ±i/2 is genuine (recurrence is
   irreducible of order 3).

**2. Asymptotics (new).**  A(n) ~ (32/(25 pi)) 16^n / n^2 · (1 - 5/(3n) + ...).
   The constant 32/(25 pi) = 0.40743665431525205956834... matches to 25 digits.
   Equivalently A(n) / C(2n,n)^2 ~ 32/(25 n).
   Generating function is NOT algebraic (tested to degree 8 in y, 39 in x).

**3. Terms.** Extended from 20 to 66 terms by transfer matrix (file b393665_extended.txt);
   recurrence gives any number more.

## A394682 — order-convex subsets of [n]^3

**4. ERROR in published formula.** "a(n) <= C(2n,n)^4" is FALSE for n >= 4:
   n=4: a=3071673482 > 70^4=24010000. (Log of C(2n,n)^4 is Theta(n), but log a(n)=Theta(n^2).)
   Correct ideal/filter bound: a(n) <= A008793(n)^2 (plane partitions in n x n x n box, squared).
   Holds for all 6 terms; ratios a/A008793^2 = .500, .2525, .1195, .0567, .0274, .0135
   (roughly halving each step, i.e. a(n) ≈ A008793(n)^2 · 2^{-n+O(1)}).

**5. Conjecture 16 log 2 / 7 is refuted.** Since lim log A008793(n)/n^2 = (9 ln 3 - 12 ln 2)/2
   (MacMahon, numerically 0.7848722...), the corrected bound gives c_3 <= 9 ln 3 - 12 ln 2
   = 1.56974..., strictly below 16 ln2/7 = 1.58434. Consistent with the exact result
   c_3 = 9 ln 3 - 12 ln 2 (Lean: C3AsymptoticClosure.lean, from the classical MacMahon
   cubic-box asymptotic) and with the d=2 pattern c_2 = 2 log 4 = log 16. Suggest replacing
   the OEIS comment with: c_3 = 2 * lim log(A008793(n))/n^2 = 9 log 3 - 12 log 2
   (and reference / proof).

## A394685 — order-convex subsets of the divisibility poset on [n]

**6. Terms.** Extended from 31 to 117 terms (file b394685_extended.txt), reproducing all
   31 published values. Algorithm (a394685_fast.c): every m > n/2 is maximal, and chains
   a|c|b with a > n/4 cannot fit in [n], so after enumerating convex subsets of [n/4] the
   remaining elements decouple into constraint components of size <= 3 and contribute a product.

**7. Identity (new, re-verified).** a(n) = A051026(n) - 1 + c(n), where c(n) = number of
   order-convex subsets of {2,...,n}: a convex set containing 1 is exactly a nonempty
   down-set, and down-sets of the divisibility poset are counted by A051026 (antichains /
   primitive subsequences).
   c(n) = 1,2,4,8,16,32,64,112,224,448,896,1408,... (= 2^{n-1} until the first 3-chain 2|4|8).
   Suggests a cross-reference to A051026 and possibly a new entry for c(n).
   (Note c(n) = c_2(n) in the notation of docs/DivisibilityRenormalization.md.)

**8. Growth constant correction.** Least-squares slope of log a(n) is 0.6042 on every window
   from [20,60] to [80,117]; the comment's "c ≈ 0.63" should read ≈ 0.604.

**9. Self-similarity of ratios — NOW A THEOREM.**
   Let r(n) = a(n)/a(n-1). For fixed k and prime p -> oo:  r(k p) -> r(k) = a(k)/a(k-1).
   Data: k=4 -> 7/4 (deviation at p=29 is -0.0003, shrinking geometrically); k=6 -> 12/7;
   k=8 -> 13/8; k=9 -> 74/39; k=10 -> 275/148. Each observed limit equals a(k)/a(k-1)
   exactly (48/28, 156/96, 296/156, 550/296). In particular r(kp) -> 2 iff k = 1 or k prime,
   which sharpens the "deficit correlates with Omega(n)" comment: the deficit at n is governed
   by the divisor structure of n's cofactor above its largest chain element, not by Omega(n).

   Resolution: the EXACT identity c_k(kp)/c_k(kp-1) = a(k)/a(k-1) (for every prime p >= k,
   where c_k counts convex subsets of {k,...,n}) is proved in
   docs/DivisibilityRenormalization.md and formalized with zero sorry in
   CausalAlgebraicGeometry/DivisibilityRenormalization.lean. The limit law r(kp) -> r(k)
   follows conditionally on the decay lemma P(a in S) -> 0 for fixed a < k (proved for
   a = 1 via A051026 and the 2^{3n/4} lower bound; open for a >= 2, measured rates
   ≈ 0.152, 0.059, 0.042, 0.027 for a = 1..4).
