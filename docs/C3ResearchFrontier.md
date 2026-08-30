# The c₃ research frontier: deterministic multiscale closure

**Status (August 2026):** the CAG-specific part of `c₃ = 2L₃` is now closed
in Lean. `C3AsymptoticClosure.C3Conjecture_of_macmahon` proves the full-support
pair asymptotic from the single classical input

```text
log(downsetCountDim 3 m)/m² → L₃.
```

The former boxed-plane-partition limit-shape input and its lozenge-coordinate
bridge are no longer needed. The one remaining formal gap is a Lean proof of
MacMahon's cubic-box formula/asymptotic and its evaluation at

```text
L₃ = (9/2) log 3 - 6 log 2.
```

Even before that evaluation, the repository now proves unconditionally

```text
[2 log(downsetCountDim 3 m) - log Q(m)] / m² → 0,
[2 log(downsetCountDim 3 m) - log|CC([m]^3)|] / m² → 0.
```

Thus the two-boundary entropy factorization itself is a finished Lean theorem.

## Target

Let `Ω_m` be the antitone profiles `[m]² → {0,...,m}` and

```text
Q(m) = #{(φ, ψ) ∈ Ω_m² : φ(x) < ψ(x) for every x}.
```

The already formalized sandwich reduces the three-dimensional convex-set
growth problem to

```text
log Q(m) = 2 log|Ω_m| - o(m²).
```

## New deterministic argument

Choose a block size `k+1` and quantize every height:

```text
coarseCode(h)(x) = floor(h(x)/(k+1)).
```

There are at most `Thin(m,m/(k+1))` coarse codes. A largest code fiber has at
least the floored average size, and every member of that fiber lies in a
radius-`k` tube around the corresponding clipped integer barrier. The existing
shift-compression theorem applies to that tube.

Threshold layers encode a height-`r` profile by `r` ordinary downsets of the
`m×m` grid. Since that grid has `C(2m,m)≤4^m` downsets,

```text
Thin(m,r) ≤ 4^(mr).
```

All of this is machine-checked. The resulting exact finite theorem is

```text
downsetCountDim(3,m)^2
  ≤ Q(m) · 4^[1 + 2m floor(m/(k+1)) + mk + m(k+1)].
```

Set `k=floor(sqrt(m))+1`. The correction exponent is `O(m^(3/2))`, hence its
normalized logarithm tends to zero. `C3AsymptoticClosure.lean` formalizes that
real-analysis squeeze and proves:

```text
MacMahon cubic asymptotic  →  C3Conjecture
MacMahon cubic asymptotic  →  log|CC([m]^3)|/m² → 2L₃.
```

## Lean theorem ladder

1. `C3ShiftCompression.tube_square_le_Q_mul_thin`: exact two-sided tube shift.
2. `C3MultiscaleCompression.thinProfile_card_le_four_pow`: elementary thin
   profile bound, without rectangular MacMahon.
3. `C3MultiscaleCompression.card_antitoneProfile_eq_downsetCount`: exact
   coordinate bridge between profile structures and cubic downsets.
4. `C3MultiscaleCompression.downset_square_le_power_correction`: finite
   multiscale inequality above.
5. `C3AsymptoticClosure.tendsto_correctionExponent_div_sq`: correction is
   subarea at square-root scale.
6. `C3AsymptoticClosure.C3Conjecture_of_macmahon`: the CAG-specific asymptotic.
7. `C3AsymptoticClosure.c3_eq_2L3_of_macmahon`: convex-set growth limit.
8. `C3AsymptoticClosure.pair_entropy_gap_tendsto_zero` and
   `convex_entropy_gap_tendsto_zero`: unconditional factorization, even before
   evaluating the one-surface constant.

All have zero `sorry` and no custom axioms.

## What remains

The remaining task is classical enumerative analysis, not a CAG ordering or
limit-shape problem:

1. Formalize the MacMahon product for `downsetCountDim 3 m`.
2. Rewrite its logarithm as the appropriate two-dimensional Riemann sum.
3. Prove convergence to the integral
   `∫₀¹∫₀¹ log((1+x+y)/(x+y)) dx dy`.
4. Evaluate the integral as `(9/2)log 3 - 6log 2`.

The published limit-shape literature remains useful for fluctuation theory,
but it is no longer an input to the entropy constant.
