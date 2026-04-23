# Proof that |CC([n] × [4])| is a polynomial of degree exactly 8 in n

**Status:** Paper-level proof, fully reproducible by the companion script
`scripts/width4_polynomial_proof.py` (runs in a few seconds, every
checkable claim asserted). The combinatorial Step 1 (the transfer matrix
correctly counts order-convex subsets) specializes `SlabCharacterization.lean`
to width 4; Steps 2–7 are elementary linear algebra over ℤ.

## Theorem

For all `n ≥ 0`,

```
|CC([n] × [4])| = C(n,0) + 10·C(n,1) + 50·C(n,2) + 140·C(n,3)
                + 245·C(n,4) + 273·C(n,5) + 191·C(n,6)
                + 77·C(n,7)  + 14·C(n,8).
```

In particular the sequence `a(n) := |CC([n] × [4])|` is a polynomial in `n`
of degree exactly 8, with leading coefficient `14 / 8! = 1/2880`.

## First 25 terms (verified three ways: transfer matrix + brute force for n ≤ 4 + closed form for n ≤ 24)

```
n  | a(n)
---+---------
 0 |         1
 1 |        11
 2 |        71
 3 |       321
 4 |      1146
 5 |      3449
 6 |      9115
 7 |     21743
 8 |     47737
 9 |     97861
10 |    189377
11 |    348899
12 |    616110
13 |   1048503
14 |   1727321
15 |   2764885
16 |   4313513
17 |   6576247
18 |   9819619
19 |  14388701
20 |  20724698
21 |  29385357
22 |  41068479
23 |  56638835
24 |  77158801
```

## Setup

Let `[n] × [4]` be the `n`-row × 4-column grid under the componentwise partial
order. A subset `S ⊆ [n] × [4]` is *order-convex* if whenever `a, b ∈ S` with
`a ≤ c ≤ b`, then `c ∈ S`. Write `a(n) := |CC([n] × [4])|` for the count of
such subsets.

## Proof

### Step 1 — Slab parameterization (specialization of `SlabCharacterization.lean`)

Every non-empty order-convex `S ⊆ [n] × [4]` has row sections `S_i = [L_i, R_i]`
that are (possibly empty) contiguous intervals, and for *consecutive* non-empty
rows `i, i+1`:

```
L_{i+1} ≤ L_i     and     R_{i+1} ≤ R_i
```

(antitone boundary going top-to-bottom). If row `i+1` is empty and row `i+2`
is again non-empty with block `[L_{i+2}, R_{i+2}]`, then convexity with respect
to the empty row forces `R_{i+2} < L_i`. More generally, any subsequent
non-empty row must have right edge strictly below the left edge of the
last-seen block.

This is a direct specialization of the general slab characterization to
`d = 2, width = 4`, identical in structure to the width-3 case.

### Step 2 — Transfer matrix

The slab rules from Step 1 are realized by a row-by-row transfer matrix on
the 15-state space

```
{F(0), F(1), F(2), F(3), F(4)} ∪ {B(L,R) : 0 ≤ L ≤ R ≤ 3}
```

(5 free states + C(4+1,2) = 10 active-block states). `F(k)` encodes "no
active block; any future block must have `R' < k`" (with `k = 4` meaning
unconstrained / initial). `B(L,R)` encodes "active block spanning columns
`L..R`". The transition multiplicities are

| From     | To       | Multiplicity |
|----------|----------|--------------|
| `F(k)`   | `F(k)`   | 1 (empty row, stay) |
| `F(k)`   | `B(L',R')` where `R' < min(k, 4)` | 1 (start a block) |
| `B(L,R)` | `F(L)`   | 1 (end block; empty row) |
| `B(L,R)` | `B(L',R')` where `L' ≤ L` and `L' ≤ R' ≤ R` | 1 (continue block) |

Let `T ∈ M₁₅(ℤ)` be the matrix built from these multiplicities, `v₀ = e_{F(4)}`
the initial-state vector, and `1 = (1,…,1)` the summation covector. Then

```
a(n) = v₀ᵀ · Tⁿ · 1.
```

### Step 3 — Spectral fact

Direct computation (reproduced by `scripts/width4_polynomial_proof.py` via
sympy):

```
charpoly(T; λ) = det(λI - T) = (λ - 1)¹⁵.
```

All fifteen eigenvalues of `T` are 1.

### Step 4 — Cayley–Hamilton and nilpotency of `N := T - I`

By Cayley–Hamilton applied to the characteristic polynomial in Step 3,
`(T - I)¹⁵ = 0`. Equivalently, `N := T - I` is nilpotent of index at most 15.
(The script verifies `N¹⁵ = 0` directly as a sanity check.)

### Step 5 — Binomial expansion of `Tⁿ`

Since `T = I + N` with `N¹⁵ = 0`:

```
Tⁿ = (I + N)ⁿ = ∑_{k=0}^{14} C(n, k) · Nᵏ,
```

valid for every integer `n ≥ 0`. (For `n < k`, `C(n,k) = 0`; the identity is
a polynomial identity in `n`.)

### Step 6 — The observable is a Newton series

Applying `v₀ᵀ (·) 1` to both sides of Step 5:

```
a(n) = ∑_{k=0}^{14} c_k · C(n, k),     c_k := v₀ᵀ Nᵏ 1 ∈ ℤ.
```

### Step 7 — Compute the `c_k`

Direct matrix computation (sympy, exact integer arithmetic):

| `k` |  `c_k` |
|-----|--------|
|  0  |    1   |
|  1  |   10   |
|  2  |   50   |
|  3  |  140   |
|  4  |  245   |
|  5  |  273   |
|  6  |  191   |
|  7  |   77   |
|  8  |   14   |
|  9  |    0   |
| 10  |    0   |
| 11  |    0   |
| 12  |    0   |
| 13  |    0   |
| 14  |    0   |

Therefore

```
a(n) = C(n,0) + 10·C(n,1) + 50·C(n,2) + 140·C(n,3) + 245·C(n,4)
     + 273·C(n,5) + 191·C(n,6) + 77·C(n,7) + 14·C(n,8),
```

a polynomial in `n` of degree exactly `max{k : c_k ≠ 0} = 8`. The leading
coefficient is `c_8 / 8! = 14/40320 = 1/2880`. ∎

## Monomial form

Expanding the Newton series:

```
a(n) = n⁸/2880 + n⁷/180 + 9 n⁶/160 + 13 n⁵/45 + 361 n⁴/320
     + 409 n³/180 + 2747 n²/720 + 73 n/30 + 1.
```

Equivalently, clearing the LCM `2880 = 2⁶ · 3² · 5`,

```
2880 · a(n) = n⁸ + 16 n⁷ + 162 n⁶ + 832 n⁵ + 3249 n⁴
            + 6544 n³ + 10988 n² + 7008 n + 2880.
```

## Pattern: width k → degree 2k

Width 2: `|CC([n] × [2])|` is a degree-4 polynomial (classical).
Width 3: degree 6 (`docs/Width3PolynomialProof.md`).
Width 4: degree 8 (this file).

All three are instances of the general pattern: the width-`k` transfer
matrix has dimension `(k+1) + k(k+1)/2 = (k+1)(k+2)/2`, its characteristic
polynomial is `(λ − 1)^{(k+1)(k+2)/2}` (conjectured; verified for `k ∈ {2,3,4}`),
and the resulting Newton series terminates at index `2k`. For width `k`, the
expected leading coefficient is `ℓ_k / (2k)!`, where

| `k` | N = dim | degree | c_{2k} | leading |
|-----|---------|--------|--------|---------|
| 2   |    6    |   4    |    1   |  1/24   |
| 3   |   10    |   6    |    5   |  1/144  |
| 4   |   15    |   8    |   14   |  1/2880 |

The `c_{2k}` values `1, 5, 14` match the Catalan numbers `C_2, C_3, C_4`
(OEIS A000108). This is a conjectural observation, not proved here.

## Corollaries

- **Asymptotics:** `a(n) ~ n⁸ / 2880` as `n → ∞`.
- **Divisibility:** `2880 · a(n) ∈ ℤ[n]` and in fact `a(n) ∈ ℤ` for every
  `n ≥ 0` (verified by the closed form).
- **Consistency at `n = 4`:** `a(4) = 1146`, which is the `n = 4`
  entry of `A393665` — the square case `|CC([m]²)|` at `m = 4`, as it
  should be (`[4] × [4] = [4]²`).

## What is left for full Lean formalization

- Steps 2–7 are pure linear algebra over ℤ and a finite matrix computation.
  In Mathlib these reduce to `Matrix.charpoly`, the Cayley–Hamilton theorem,
  and binomial identities; a ~100-line specialization once the TM is defined,
  parallel to the width-3 case.
- Step 1 is the combinatorial content. It specializes `SlabCharacterization.lean`
  to `d = 2, width = 4` and should follow by restriction of the general result.

## Companion artifacts

- `scripts/width4_polynomial_proof.py` — self-contained sympy script
  reproducing Steps 2–7, cross-checked against brute force for `n ≤ 4`,
  with assertions on every checkable claim (runs in a few seconds).
- `oeis_width4_submission_draft.md` — OEIS submission draft (sequence not
  currently in OEIS as of 2026-04-23).

## Cross-references

- `CausalAlgebraicGeometry/SlabCharacterization.lean` — general slab
  characterization used in Step 1.
- `scripts/width3_polynomial_proof.py` and `docs/Width3PolynomialProof.md` —
  the width-3 analogue; this file reproduces that structure at width 4.
- `CausalAlgebraicGeometry/GrowthRateIs16.lean` — growth constant for the
  square case `|CC([m]²)|` (A393665); the width-`k` diagonal is a
  different asymptotic regime where `a(n) ~ n^{2k} / const`.
- `CausalAlgebraicGeometry/PartitionDimensionBridge.lean` — related
  dimension-law results.
