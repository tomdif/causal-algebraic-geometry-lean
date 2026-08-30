# A renormalization theorem for order-convex subsets of the divisibility poset

Notation. a(n) = A394685(n). For k >= 1 let c_k(n) = number of order-convex subsets of
{k, k+1, ..., n} under divisibility (so c_1 = a, and c_k(n) counts convex S subset [n]
with S ∩ [k-1] = ∅, since absent elements impose no constraints). r(n) = a(n)/a(n-1).

**Lean status.** Theorem 1 is fully formalized (zero sorry) in
`CausalAlgebraicGeometry/DivisibilityRenormalization.lean`, in the cross-multiplied form
c_k(kp) · a(k-1) = c_k(kp-1) · a(k); the k = 1 case recovers the prime-doubling theorem
of `DivisibilityPoset.lean`.

## Theorem 1 (exact self-similarity)

For every k >= 1 and every prime p >= k:

        c_k(kp) / c_k(kp-1)  =  a(k) / a(k-1)  =  r(k).

Verified computationally for all (k,p) with kp <= 117, p >= k. For p < k the proof
breaks down (C is no longer contained in P) and the identity can fail — e.g.
(k,p) = (4,2) and (4,3) give ratio 2 against a(4)/a(3) = 7/4 — though it can also hold
accidentally: at (k,p) = (3,2), (5,2), (5,3) both sides equal 2, because k is prime
(so r(k) = 2) while kp still has a pendant top over {k, ..., kp-1} (its only divisor
in that range is covered by kp), which forces c_k(kp) = 2·c_k(kp-1) for the unrelated
pendant reason.

Proof. Let P = {k, ..., kp-1}. Put C = {jp : 1 <= j <= k-1}. Since p >= k, p does not
divide any j < k, so C is contained in P and j -> jp is a poset isomorphism [k-1] -> C.
Let R = P \ C.

(i) No divisibility chain x | c | y in P has its three elements split between C and R.
    If y = jp in C and x | y with x in P, then either p | x (x in C) or x | j, forcing
    x <= j < k, impossible. If x = jp in C and x | y <= kp-1 then y = (js)p with js < k,
    so y in C. Hence every chain touching C lies entirely in C.
    Therefore S is convex in P iff S∩C is convex in C and S∩R is convex in R, i.e.
    c_k(kp-1) = a(k-1) · Conv(R).

(ii) Adjoining the new maximal element kp: S ∪ {kp} is convex iff S ∩ D'(kp) is an up-set
    of the proper-divisor poset of kp restricted to P. That restriction is
    {k} ∪ {dp : d | k, d < k}, which is contained in C ∪ {k} — properly for k >= 4:
    e.g. at (k,p) = (4,5), 15 ∈ C but 15 ∤ 20. The element k is covered by kp with
    nothing strictly between (k | c | kp forces c = k or kp), so k imposes no condition;
    the elements of C that are not divisors of kp impose none either. The up-set
    condition on {dp : d | k, d < k} is therefore exactly the statement that
    (S∩C) ∪ {kp} is convex in C ∪ {kp} ≅ [k]. By (i), the number of such S is
    (a(k) - a(k-1)) · Conv(R).

Hence c_k(kp) = c_k(kp-1) + (a(k)-a(k-1))·Conv(R) = a(k)·Conv(R), and the ratio is
a(k)/a(k-1).  ∎

## Corollary (limit law), conditional on a decay lemma

a(n) = c_k(n) + #{convex S : S ∩ [k-1] ≠ ∅}. If P_n(a ∈ S) -> 0 for each fixed a < k
(S uniform among convex subsets of [n]), then

        lim_{p -> ∞, p prime}  a(kp)/a(kp-1)  =  a(k)/a(k-1),

with error O( max_{a<k} P(a ∈ S) ). Observed limits on the extended terms (n <= 117)
confirm this: k=4 -> 7/4, k=6 -> 12/7, k=8 -> 13/8, k=9 -> 74/39, k=10 -> 275/148,
each exactly a(k)/a(k-1) (see docs/OEISConvexFindings.md, item 9).
In particular r(kp) -> 2 iff k = 1 or k is prime;
the "only if" direction is unconditional, since for composite k the set {1} is convex
in [k-1] but {1, k} is not convex in [k] (it misses any prime divisor q of k with
1 < q < k), so a(k) < 2·a(k-1) strictly. The "prime doubling" theorem of the OEIS
entry is the case k = 1.

## Decay lemma — status

(a) a = 1 is proved. Convex sets containing 1 are exactly the nonempty down-sets, giving
    the exact identity a(n) = A051026(n) - 1 + c_2(n) (verified for n <= 117; the down-set
    count is A051026(n) = β^{(1+o(1))n} with 1.572939 <= β <= 1.574445
    — Angelo 2018 for existence of the limit; Liu–Pach–Palincza 2021; McNew 2021).
    On the other hand every subset of (n/4, n] is convex (a chain x|c|y needs y >= 4x),
    so a(n) >= 2^{⌈3n/4⌉}, i.e. a(n)^{1/n} >= 2^{3/4} = 1.6818. Hence
        P(1 ∈ S) <= A051026(n)/a(n) <= (0.937 + o(1))^n.
    The true rate is c - ln β ≈ 0.6042 - 0.4530 = 0.151 (measured: 0.152).

(b) a >= 2 is open. Measured decay rates of P(a ∈ S): 0.152, 0.059, 0.042, 0.027 for
    a = 1..4, roughly 0.12/a. Structurally, a ∈ S forces S ∩ aN to be a down-set of the
    multiples poset aN ∩ [n] ≅ [n/a], which loses a positive fraction of the freedom of the
    ~n/(2a) maximal multiples of a in (n/2, n]. A proof needs a lower bound on a(n) that
    is uniform relative to the count of sets avoiding aN; the natural tool is McNew's
    divisor-graph method (Europ. J. Combin. 92, 2021), which handles exactly such
    "multiplicatively local" statistics and would also give the growth constant
    c = lim log a(n)/n (≈ 0.6042) as an explicit infinite product.

## Interpretation

The convex-set statistics of the divisibility poset are scale-free: multiplying the ambient
scale by a large prime reproduces the ratio function at the cofactor. The deficit
2 - r(n) at composite n is thus not a function of Ω(n) but of the divisor lattice of n
truncated at bounded cofactor, with contributions from cofactor t suppressed like
exp(-0.12 t) (this is the same decay as (b) with a = n/t). This explains the observed
grouping of deficits by n/a_max and gives the mechanism behind the growth constant:
c = ln 2 - (mean deficit), the mean being over an ultimately periodic function of n.

## Grid side (for the CAG dimension law)

* d = 2: a(n) ~ (32/(25π)) 16^n / n^2 (constant matched to 25 digits; A393665 also
  satisfies a minimal order-3 P-recurrence, see docs/OEISConvexFindings.md item 1) while
  (ideal, filter) pairs number C(2n,n)^2 ~ 16^n/(πn).
  So a convex subset of [n]^2 has on average ~ (25/32) n ideal/filter representations:
  the representation redundancy is linear with rational slope 25/32.
* d = 3: a(n) ≈ A008793(n)^2 · 2^{-n+O(1)} on the available terms, and the rigorous bound
  a(n) <= A008793(n)^2 gives c_3 <= 9 ln 3 - 12 ln 2 (MacMahon), refuting 16 ln 2 / 7.
  (The bound a(n) <= C(2n,n)^4 published at A394682 is false for n >= 4 — wrong order of
  growth; see docs/OEISConvexFindings.md item 4.)
* General d: c_d = 2 · lim log(#down-sets of [n]^d)/n^{d-1} whenever the redundancy is
  subexponential in n^{d-1}. Down-sets of [n]^d are (d-1)-dimensional partitions in a box;
  for d >= 4 their entropy is an open problem (no MacMahon-type formula), so c_4 is
  equivalent to the box-solid-partition entropy. Conversely the CAG framework gives a
  new combinatorial handle (convex sets, transfer matrices) on that classical question.
