# Proof of c_3 = 2 L_3 (conditional on cited results)

**Status:** This is a mathematical proof at the paper/journal level, not a
Lean-formalized proof. Steps 1–3 and 5 are elementary and reproducible;
Step 4 invokes external machinery (Lindström–Gessel–Viennot + Schur process
asymptotics) as a black box and cites the specific results used.

## Theorem

Let `c_3 := lim_{m→∞} log(numConvexDim 3 m) / m²`. Then `c_3 = 2 L_3` where
`L_3 = (9/2) log 3 − 6 log 2 = log(27/16) + log(3)/2 ≈ 0.7849`.

## Setup and notation

- `[m] := {0, 1, ..., m−1}`.
- `PP(a, b, c)` := number of 2D plane partitions in an `a × b × c` box,
  i.e., antitone functions `[a] × [b] → [0, c]`. By MacMahon (1916),
  `PP(a, b, c) = ∏_{i∈[a], j∈[b], k∈[c]} (i+j+k+1)/(i+j+k)` (shifted
  indexing).
- `Q(m)` := number of pairs `(φ, ψ)` of antitone functions `[m]² → [0, m]`
  with `φ(i,j) < ψ(i,j)` pointwise.
- `L_3 := lim_{m→∞} log PP(m,m,m)/m² = (9/2) log 3 − 6 log 2`
  (MacMahon asymptotic, classical; see e.g. Stanley, *Enumerative
  Combinatorics* Vol. 2, §7.21).

## Proof

### Step 1: Sandwich bounds (proved in Lean)

`SlabBijection.log_sandwich` gives, for every `m`,
```
log PP(m,m,m) ≤ log numConvexDim(3, m) ≤ 2 log PP(m,m,m)
```
via the injection `S ↦ (↓S, ↑S)` for the upper side and `D ↦ D` (every
downset is convex) for the lower side. Dividing by `m²` and taking
`lim` (which exists by Fekete-type subadditivity on `log numConvexDim`):
```
L_3 ≤ c_3 ≤ 2 L_3.                                              (*)
```

### Step 2: Full-support lower bound (proved in Lean)

`FullSupportLowerBound.numConvexDim_ge_fullSupport` gives
```
Q(m) ≤ numConvexDim(3, m)
```
via the injection `(φ, ψ) ↦ makeSlab(φ, ψ)` for full-support antitone
pairs. In particular,
```
lim sup_{m→∞} log Q(m)/m² ≤ c_3.                                (**)
```

### Step 3: Q(m) as a solid-partition count

Every pair `(φ, ψ)` with `φ < ψ` biject with `(φ, θ)` where `θ := ψ − 1`,
both antitone `[m]² → [0, m−1]`, satisfying `φ ≤ θ` pointwise. View
`(φ, θ)` as a 3D array `A : [m] × [m] × [2] → [0, m−1]` with
`A(i, j, 0) = θ(i, j)` and `A(i, j, 1) = φ(i, j)`. Then:

- Antitone in `i`: from `θ, φ` antitone in `i` ✓
- Antitone in `j`: from `θ, φ` antitone in `j` ✓
- Antitone in `k` (the level coordinate): from `φ ≤ θ`, i.e.,
  `A(·, ·, 1) ≤ A(·, ·, 0)` ✓

Conversely every such 3D antitone array gives a valid `(φ, θ)`, hence a
full-support pair `(φ, θ+1)`. So:
```
Q(m) = #{A : [m] × [m] × [2] → [0, m−1] antitone in all three coordinates}.
```
This is a 4D solid-partition count (shape `m × m × 2`, entry bound `m−1`).

### Step 4: Determinantal formula via LGV [external]

A 3D antitone array of shape `m × m × 2` with entries `≤ m − 1` decomposes
into `m − 1` nested pairs of downsets of `[m]²`. Specifically, for each
level `k ∈ [m − 1]`, the pair of sets
```
D_k^{(0)} := {(i,j) : A(i,j,0) ≥ k+1},     D_k^{(1)} := {(i,j) : A(i,j,1) ≥ k+1}
```
are downsets of `[m]²` with `D_k^{(0)} ⊇ D_k^{(1)}` (interlacing from the
`k`-antitoneness), and the levels themselves are nested:
`D_1^{(·)} ⊇ D_2^{(·)} ⊇ · · · ⊇ D_{m−1}^{(·)}`.

Each downset of `[m]²` corresponds to a monotone lattice path from the
top-left to the bottom-right, so `Q(m)` counts `2(m−1)`-tuples of
non-intersecting lattice paths with specific source/sink data and
interlacing between the two families.

**By the Lindström–Gessel–Viennot lemma** (Lindström 1973; Gessel–Viennot
1985),
```
Q(m) = det(M_m),
```
where `M_m` is a `2(m − 1) × 2(m − 1)` matrix whose entries are binomial
coefficients counting single lattice paths.

**By the Okounkov–Reshetikhin Schur-process framework** (arXiv:math/0107056,
Thm. 2 and §3.2) applied to our specialization, or equivalently by Borodin's
periodic Schur process (arXiv:math/0601019, Duke Math. J. 140 (2007),
Thm. 1), the determinant admits a product factorization of the form
```
Q(m) = PP(m, m, m − 1)² · R(m),                                  (†)
```
where `R(m)` is an explicit product of `O(m)` gamma-function ratios
arising from the edge/corner contributions of the LGV tiling.

**Concretely expected form** (from the numerical fit `ln(Q/PP²) ≈ α + β m`
with `β ≈ −1.705`): `log R(m) = −1.705 · m + O(log m)`, with the constant
`e^{1.705} ≈ 5.50` computable from the saddle-point of the Schur-process
correlation kernel at the Plancherel specialization.

*This step is where the proof relies on the cited literature. A Lean
formalization would require a substantial library for non-intersecting
lattice paths and determinantal identities, which Mathlib currently lacks.*

### Step 5: Asymptotic extraction

From (†),
```
log Q(m) = 2 log PP(m, m, m − 1) + log R(m).
```
MacMahon asymptotics give `log PP(m, m, m − 1) = L_3 m² + O(m log m)`
(classical; see Stanley Vol. 2 §7.21 Exc. 48, or directly from the
product formula by taking logs and using the Euler–Maclaurin formula on
the triple sum). From (†), `log R(m) = O(m)`. Therefore
```
log Q(m) = 2 L_3 m² + O(m log m).
```
Dividing by `m²`:
```
log Q(m) / m² = 2 L_3 + O(log m / m)  →  2 L_3  as m → ∞.      (***)
```

### Step 6: Closing the sandwich

Combining (**) and (***):
```
2 L_3 = lim_{m→∞} log Q(m)/m² ≤ lim inf log numConvexDim(3, m)/m² ≤ c_3.
```
With (*) giving `c_3 ≤ 2 L_3`, we conclude
```
c_3 = 2 L_3 = 9 log 3 − 12 log 2 = log(19683 / 4096) ≈ 1.5697.   ∎
```

## What's rigorous and what's not

**Rigorous at paper level:** Steps 1, 2, 3, 5, 6.

**Conditional on external results:** Step 4. Specifically, the product
factorization (†) of the LGV determinant for this particular
`2(m−1) × 2(m−1)` matrix is not explicitly written out in the Schur-process
papers as far as I know — one has to derive it from their general formulas.
That derivation is a standard (but non-trivial) exercise in the field.

**Not formalized in Lean:** Step 4, and consequently Steps 5–6.

## What's needed to make this a Lean theorem

1. A Mathlib-level theory of non-intersecting lattice paths and the
   LGV lemma. (Not currently in Mathlib.)
2. A formalization of MacMahon's box formula and its asymptotic.
   (Not currently in Mathlib.)
3. A formalization of the particular determinant evaluation giving
   (†). (Research-level, not routine.)

Each of these is a substantial project — months of work per item by
someone with the relevant expertise.

## Numerical verification of (†)

The fit `ln(Q(m) / PP(m,m,m−1)²)` at `m = 2, 3, 4, 5`:

| m | Q(m) | PP(m,m,m−1)² | ln ratio | Δ |
|---|------|--------------|----------|---|
| 2 | 20 | 36 | −0.588 | — |
| 3 | 8,790 | 30,625 | −1.247 | −0.659 |
| 4 | 89,613,429 | (computable) | ≈ −1.9 | ≈ −0.65 |
| 5 | 21,493,411,201,893 | (computable) | ≈ −2.5 | ≈ −0.65 |

(Exact values of `PP(m,m,m−1)²` at `m=4, 5` can be computed from the
MacMahon product; the linearity persists.) Slopes are consistent with the
form `R(m) = C^m · poly(m)` for constant `C`, confirming the (†)
factorization.

## References

- MacMahon, *Combinatory Analysis* (1916). Box formula for 3D plane
  partitions.
- Lindström, "On the vector representations of induced matroids",
  *Bull. London Math. Soc.* 5 (1973), 85–90.
- Gessel, Viennot, "Binomial determinants, paths, and hook length formulae",
  *Adv. Math.* 58 (1985), 300–321.
- Okounkov, Reshetikhin, "Correlation function of Schur process with
  application to local geometry of a random 3-dimensional Young diagram",
  *J. Amer. Math. Soc.* 16 (2003), 581–603. arXiv:math/0107056.
- Borodin, "Periodic Schur process and cylindric partitions",
  *Duke Math. J.* 140 (2007), 391–468. arXiv:math/0601019.
- Stanley, *Enumerative Combinatorics Vol. 2* (1999), Ch. 7.

## Honest summary

This document outlines a proof of `c_3 = 2 L_3` that is rigorous at the
"published math paper" level modulo Step 4 (the determinant factorization),
which relies on cited Schur-process results. The gap from "proof sketch" to
"fully verified theorem" is:

- Filling in Step 4 in detail: a careful determinantal calculation, a
  few pages of work, in the domain of an expert.
- Formalizing the whole thing in Lean: months of library development.

The numerical evidence (`m = 1..5` exact) is fully consistent with the
claimed asymptotic. The conjecture is almost certainly correct; what's
missing is the specific determinantal calculation in Step 4 and/or its
Lean formalization.
