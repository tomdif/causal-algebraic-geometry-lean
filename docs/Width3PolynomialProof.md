# Proof that |CC([n] × [3])| is a polynomial of degree exactly 6 in n

**Status:** Paper-level proof, fully reproducible by the companion script
`scripts/width3_polynomial_proof.py`. The combinatorial Step 1 (the transfer
matrix correctly counts order-convex subsets) specializes `SlabCharacterization.lean`
to width 3; Steps 2–7 are elementary linear algebra over ℤ that run in sympy
in well under a second.

## Theorem

For all `n ≥ 0`,

```
|CC([n] × [3])| = C(n,0) + 6·C(n,1) + 20·C(n,2) + 35·C(n,3)
                + 36·C(n,4) + 20·C(n,5) + 5·C(n,6).
```

In particular the sequence `a(n) := |CC([n] × [3])|` is a polynomial in `n`
of degree exactly 6, with leading coefficient `5 / 6! = 1/144`.

## First 20 terms (verified two ways: transfer matrix + brute force for n ≤ 5)

```
n  | a(n)
---+------
0  |      1
1  |      7
2  |     33
3  |    114
4  |    321
5  |    781
6  |   1702
7  |   3403
8  |   6349
9  |  11191
10 |  18811
11 |  30372
12 |  47373
13 |  71709
14 | 105736
15 | 152341
16 | 215017
17 | 297943
18 | 406069
19 | 545206
20 | 722121
```

## Setup

Let `[n] × [3]` be the `n`-row × 3-column grid under the componentwise partial
order. A subset `S ⊆ [n] × [3]` is *order-convex* if whenever `a, b ∈ S` with
`a ≤ c ≤ b`, then `c ∈ S`. Write `a(n) := |CC([n] × [3])|` for the count of
such subsets.

## Proof

### Step 1 — Slab parameterization (specialization of `SlabCharacterization.lean`)

Every non-empty order-convex `S ⊆ [n] × [3]` has row sections `S_i = [L_i, R_i]`
that are (possibly empty) contiguous intervals, and for *consecutive* non-empty
rows `i, i+1`:

```
L_{i+1} ≤ L_i     and     R_{i+1} ≤ R_i
```

(antitone boundary going top-to-bottom). If row `i+1` is empty and row `i+2` is
again non-empty with block `[L_{i+2}, R_{i+2}]`, then convexity with respect to
the empty row forces `R_{i+2} < L_i`. More generally, any subsequent non-empty
row must have right edge strictly below the left edge of the last-seen block.

This is a direct specialization of the general slab characterization to
`d = 2, width = 3`.

### Step 2 — Transfer matrix

The slab rules from Step 1 are realized by a row-by-row transfer matrix on
the 10-state space

```
{F(0), F(1), F(2), F(3)} ∪ {B(L,R) : 0 ≤ L ≤ R ≤ 2}
```

where `F(k)` encodes "no active block; any future block must have `R' < k`"
(with `k = 3` meaning unconstrained), and `B(L,R)` encodes "active block
spanning columns `L..R`". The transition multiplicities are

| From     | To       | Multiplicity |
|----------|----------|--------------|
| `F(k)`   | `F(k)`   | 1 (empty row, stay) |
| `F(k)`   | `B(L',R')` where `R' < min(k, 3)` | 1 (start a block) |
| `B(L,R)` | `F(L)`   | 1 (end block; empty row) |
| `B(L,R)` | `B(L',R')` where `L' ≤ L` and `L' ≤ R' ≤ R` | 1 (continue block) |

Let `T ∈ M₁₀(ℤ)` be the matrix built from these multiplicities, `v₀ = e_{F(3)}`
the initial-state vector, and `1 = (1,…,1)` the summation covector. Then

```
a(n) = v₀ᵀ · Tⁿ · 1.
```

### Step 3 — Spectral fact

Direct computation (reproduced by `scripts/width3_polynomial_proof.py` via
sympy):

```
charpoly(T; λ) = det(λI - T) = (λ - 1)¹⁰.
```

All ten eigenvalues of `T` are 1.

### Step 4 — Cayley–Hamilton and nilpotency of `N := T - I`

By Cayley–Hamilton applied to the characteristic polynomial in Step 3,
`(T - I)¹⁰ = 0`. Equivalently, `N := T - I` is nilpotent of index at most 10.
(The script verifies `N¹⁰ = 0` directly as a sanity check.)

### Step 5 — Binomial expansion of `Tⁿ`

Since `T = I + N` with `N¹⁰ = 0`:

```
Tⁿ = (I + N)ⁿ = ∑_{k=0}^{9} C(n, k) · Nᵏ,
```

valid for every integer `n ≥ 0`. (For `n < k`, `C(n,k) = 0`; the identity is
a polynomial identity in `n`.)

### Step 6 — The observable is a Newton series

Applying `v₀ᵀ (·) 1` to both sides of Step 5:

```
a(n) = ∑_{k=0}^{9} c_k · C(n, k),     c_k := v₀ᵀ Nᵏ 1 ∈ ℤ.
```

### Step 7 — Compute the `c_k`

Direct matrix computation (sympy, exact integer arithmetic):

| `k` |  `c_k` |
|-----|--------|
|  0  |   1    |
|  1  |   6    |
|  2  |  20    |
|  3  |  35    |
|  4  |  36    |
|  5  |  20    |
|  6  |   5    |
|  7  |   0    |
|  8  |   0    |
|  9  |   0    |

Therefore

```
a(n) = C(n,0) + 6·C(n,1) + 20·C(n,2) + 35·C(n,3)
     + 36·C(n,4) + 20·C(n,5) + 5·C(n,6),
```

a polynomial in `n` of degree exactly `max{k : c_k ≠ 0} = 6`. The leading
coefficient is `c_6 / 6! = 5/720 = 1/144`. ∎

## Monomial form

Expanding the Newton series:

```
a(n) = n⁶/144 + n⁵/16 + 61 n⁴/144 + 53 n³/48 + 185 n²/72 + 11 n/6 + 1.
```

## Corollaries

- **Asymptotics:** `a(n) ~ n⁶ / 144` as `n → ∞`.
- **Divisibility:** `144 · a(n) ∈ ℤ[n]`, so `144 | (144 · a(n))` in ℤ for all
  `n`; equivalently, `a(n) ∈ ℤ` for every `n ≥ 0` (verified by the closed form).
- **Supermultiplicative with `|CC([m] × [m])|` at `m = 3`:** `a(3) = 114`
  matches the `n = 3` entry of `A393665`, the square case. (Sanity check.)

## What is left for full Lean formalization

- Steps 2–7 are pure linear algebra over ℤ and a finite matrix computation.
  In Mathlib these reduce to `Matrix.charpoly`, `Matrix.pow_sub_one_eq_zero_of_charpoly`,
  and binomial identities; a ~100-line specialization once the TM is defined.
- Step 1 is the combinatorial content. It specializes `SlabCharacterization.lean`
  to `d = 2, width = 3` and should follow by restriction of the general result.

## Companion artifacts

- `scripts/width3_polynomial_proof.py` — self-contained sympy script
  reproducing Steps 2–7 (runs in <1s), with assertions on every checkable
  claim in the theorem.
- OEIS entry: submitted companion to `A393665` with this closed form in the
  `%F` field.

## Cross-references

- `CausalAlgebraicGeometry/SlabCharacterization.lean` — general slab
  characterization used in Step 1.
- `CausalAlgebraicGeometry/GrowthRateIs16.lean` — growth constant for the
  square case `|CC([m]²)|` (A393665); the width-`k` diagonal is a different
  asymptotic regime where `a(n) ~ n^{2k} / const`.
- `CausalAlgebraicGeometry/PartitionDimensionBridge.lean` — related
  dimension-law results.
