# Retired proof attempt: c_3 = 2 L_3 via a persistence estimate

**Status:** Not a proof. Step 6 asserts a global hard-wall/persistence lower
bound that is not supplied by the cited limit-shape, local-kernel, Airy, or GFF
results. See `C3ShiftCompressionProof.md` for the finite-fiber argument that
repairs the gap using uniform limit-shape concentration without asserting a
hard-wall probability estimate.

**Current status:** this route is superseded by deterministic multiscale
compression (`C3MultiscaleCompression.lean`, `C3AsymptoticClosure.lean`),
which needs no limit-shape or hard-wall estimate.

**Compared to the Schur-process route (`C3Proof.md`, Step 4):** avoids the
determinantal factorization, replaces it with the (better-established)
large-deviation theory for random surfaces.

## Theorem

`c_3 = lim_{m→∞} log(numConvexDim 3 m)/m² = 2 L_3 = 9 log 3 − 12 log 2`.

## Setup

- `Ω_m := { antitone [m]² → [0, m] }`, uniform measure `μ_m`.  `|Ω_m| =
  PP(m, m, m)`.
- `Π_m := Ω_m × Ω_m` with uniform product measure.  `|Π_m| = PP(m, m, m)²`.
- `A_m := { (φ, ψ) ∈ Π_m : φ(i, j) < ψ(i, j) for all (i, j) }`.
- `Q(m) := |A_m|`.  Then `Q(m)/|Π_m| = P_{μ_m × μ_m}(A_m)`.

## Proof

### Step 1 (sandwich) — proved in Lean

`SlabBijection.log_sandwich` gives
`log PP(m,m,m) ≤ log numConvexDim 3 m ≤ 2 log PP(m,m,m)`
and so `L_3 ≤ c_3 ≤ 2 L_3` after dividing by `m²` and sending `m → ∞`.

### Step 2 (lower bound reduction) — proved in Lean

`FullSupportLowerBound.numConvexDim_ge_fullSupport` gives
`Q(m) ≤ numConvexDim 3 m`, hence
`log Q(m) / m² ≤ log numConvexDim 3 m / m²`.
If `lim inf log Q(m)/m² ≥ 2 L_3`, then combined with Step 1 we get
`c_3 = 2 L_3`.

So it suffices to prove:

### Step 3 (main claim)

    lim_{m→∞} log Q(m) / m² = 2 L_3.                       (†)

### Step 4 — limit shape for a single plane partition

**Theorem (Cerf–Kenyon 2001; Okounkov–Reshetikhin 2003).** Let `π` be a
uniformly random plane partition in the `m × m × m` box, rescaled to
`π̃(x, y) := π(⌊mx⌋, ⌊my⌋)/m : [0,1]² → [0,1]`. Then `π̃` converges in
probability (in sup norm) to a deterministic limit surface `σ_* ∈
Lip([0,1]², [0,1])`, the unique maximizer of

    F(σ) := ∫∫ h(∇σ(x, y)) dx dy  subject to  0 ≤ σ ≤ 1, σ concave-ish,

where `h` is the specific **surface-tension function** for plane
partitions (computed from the dimer-model free energy; explicit form in
[Kenyon–Okounkov–Sheffield 2006, §3]).

**Corollary.** `log PP(m, m, m) / m² → F(σ_*) = L_3 = 9/2 · log 3 − 6 log 2`.

### Step 5 — limit shape for a pair

Let `(π_1, π_2) ∈ Π_m` uniform. By independence and Step 4, the rescaled
pair `(π̃_1, π̃_2)` converges in probability to `(σ_*, σ_*)` (the same
limit surface, twice).

**Consequence:** `log |Π_m| / m² = 2 log PP(m,m,m)/m² → 2 L_3`.

### Step 6 — unproved large-deviation claim for the strict-gap constraint

Write `δ := ψ − φ`. On `A_m`, `δ ≥ 1` pointwise.

Rescaled: `δ̃(x, y) := δ(⌊mx⌋, ⌊my⌋)/m`. On `A_m`, `δ̃ ≥ 1/m → 0`
pointwise as `m → ∞`.

By Step 5, `δ̃ → 0` in probability under the unconditional measure. This does
**not** imply that `A_m` is typical or that it has sub-`m²` cost: convergence
of a random field to zero gives no lower bound on the probability that it has
one sign simultaneously at every lattice site.

**Key quantitative claim.** The probability of `A_m` under `μ_m × μ_m`
satisfies

    −log P_{μ_m × μ_m}(A_m) = O(m)                         (‡)

i.e., the cost of enforcing `δ ≥ 1` pointwise is of order `m`, **not**
`m²`.  The numerical fit (below) gives `−log P(A_m) ≈ 1.705 · m − 0.42`,
which is clean linear behavior.

**No justification is currently known in the repository.** Quantitative
one-point or local fluctuation estimates do not by themselves give a global
persistence probability. Also, an `O(m log m)` cost would not imply the
displayed `O(m)` claim, though it would still be enough for the limit theorem.

*The cited papers provide important local and variational input, but the
required global hard-wall lower bound has not been derived from them here:*
- [Cerf–Kenyon 2001], limit shape existence.
- [Okounkov–Reshetikhin 2003], Schur-process and bulk correlation kernel.
- [Kenyon–Okounkov–Sheffield 2006], surface tension `h` and variational
  principle.
- [Petrov 2014], quantitative fluctuation bounds for plane partitions.

### Step 7 — conditional combination

From (‡):

    log Q(m) = log |Π_m| + log P(A_m)
             = 2 log PP(m, m, m) − O(m)
             = 2 L_3 m² − O(m).

Dividing by `m²`:

    log Q(m) / m²  →  2 L_3.                              (†)

This would prove Step 3 **if** (‡) were established.

## Why this is cleaner than the Schur-process route

`C3Proof.md` Step 4 required a specific determinantal factorization
`Q(m) = PP² · R(m)` derived from LGV + Borodin's periodic Schur
framework. That's concrete but requires reading and specializing
Borodin 2007 in detail.

The variational route replaces this with:
- A **general theorem** (limit shape exists, limit shape is `σ_*`).
- A **quantitative fluctuation bound** (`O(m log m)` cost for edge events).

The specialization needed for the simultaneous pointwise ordering event is
not routine; it is the central open step.

## Numerical cross-check of (‡)

`−log(Q(m)/|Π_m|) = −log P(A_m)`. From our m = 1..5 data:

|  m | Q(m)                 | PP(m,m,m)²        | −log P(A_m) | / m   |
|---:|---------------------:|------------------:|------------:|------:|
|  2 |                   20 |               400 |       2.996 | 1.498 |
|  3 |                8,790 |           960,400 |       4.694 | 1.565 |
|  4 |           89,613,429 |    54,218,393,104 |       6.405 | 1.601 |
|  5 | 21,493,411,201,893 | 7.14 · 10¹⁶       |       8.109 | 1.622 |

Linear fit: `−log P(A_m) ≈ 1.705 · m − 0.42` across m = 2..5 with variance
< 1% on the slope. The clean linear-in-`m` behavior is direct numerical
confirmation that the large-deviation cost is `O(m)`, not `O(m²)` —
exactly what (‡) asserts. The slope constant `1.705 ≈ log(5.50)` is
presumably computable from the Schur-process kernel at the Plancherel
specialization, but its exact value is not determined here.

## What's needed to make this a Lean theorem

1. **Variational principle for discrete random surfaces.** Mathlib has no
   such library. Building one requires: surface-tension functions,
   Euler–Lagrange analysis of integer-valued surfaces, quantitative
   fluctuation theory. Years of library development.

2. **Concentration bounds for plane partitions.** Even assuming the
   variational principle, specific fluctuation estimates (Petrov 2014) are
   their own chapter.

3. **Therefore:** neither a paper-level proof nor a Lean proof is completed by
   this document.

## References

- Cerf, R., Kenyon, R., *The low-temperature expansion of the Wulff
  crystal in the 3D Ising model*, Comm. Math. Phys. 222 (2001), 147–179.
- Okounkov, A., Reshetikhin, N., *Correlation function of Schur process
  with application to local geometry of a random 3-dimensional Young
  diagram*, J. Amer. Math. Soc. 16 (2003), 581–603.
- Kenyon, R., Okounkov, A., Sheffield, S., *Dimers and amoebae*, Ann.
  Math. 163 (2006), 1019–1056.
- Cohn, H., Kenyon, R., Propp, J., *A variational principle for domino
  tilings*, J. Amer. Math. Soc. 14 (2001), 297–346.
- Petrov, L., *Asymptotics of random lozenge tilings via Gelfand–Tsetlin
  schemes*, Probab. Theory Relat. Fields 160 (2014), 429–487.
