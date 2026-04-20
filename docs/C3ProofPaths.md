# Proof Paths for c_3 = 2 L_3

Exploration of routes to a rigorous proof. Ranked by "distance to a Lean
theorem." Includes one path that achieves a strict improvement over the
sandwich lower bound (`c_3 ≥ 2 L_3 − log 2`) without Schur-process machinery.

---

## Path A — FKG / Harris–Holley inequality

**Claim:** `c_3 ≥ 2 L_3 − log 2 ≈ 0.877`. Strict improvement over sandwich
lower bound `L_3 ≈ 0.785`. Does **not** close to `2 L_3`.

**Setup.** Let `Ω = { antitone pairs (φ, ψ) on [m]² → [0, m] }`. Under the
product partial order

    (φ, ψ) ≼ (φ', ψ')  iff  φ ≥ φ' pointwise  and  ψ ≤ ψ' pointwise,

`Ω` is a finite distributive lattice (pointwise max/min of antitone functions
is antitone). The events `A_{ij} := { ψ(i,j) > φ(i,j) }` are up-closed in `≼`
(increasing ψ or decreasing φ enhances the inequality).

The uniform measure on `Ω` is trivially log-supermodular (constant on a
sublattice). By the **Harris–FKG inequality**,

    P(⋂_{i,j} A_{ij})  ≥  ∏_{i,j} P(A_{ij}).

Since `Q(m)/|Ω| = P(⋂ A_{ij})` and `|Ω| = PP(m,m,m)²`, this gives

    Q(m)  ≥  PP(m,m,m)²  ·  ∏_{i,j} P(A_{ij}).

**Marginal lower bound.** By the `(φ,ψ) ↔ (ψ,φ)` symmetry of `Ω`,
`P(ψ > φ at (i,j)) = P(φ > ψ at (i,j))`, so both equal `(1 − P(ψ=φ))/2`.
Since the antitone-marginal distribution at any fixed cell is a distribution
on `{0, 1, ..., m}` with ≥ 2 elements in its support (verify: constant-`0`
and constant-`m` antitone functions both exist), `P(ψ = φ at cell) ≤ 1`,
but this trivial bound gives nothing.

For a non-trivial bound we need `P(ψ = φ at cell) ≤ 1 − c/m` for some `c > 0`,
which follows from the fact that the marginal has a spread of at least `m+1`
values. By a **concavity-of-`x²`** argument:

    P(ψ = φ at cell) = ∑ₖ pₖ²  ≤  (max pₖ).

For large `m` the marginal distribution concentrates (Okounkov–Reshetikhin
limit shape), so `max pₖ → 0`. This gives `P(A_{ij}) → 1/2` and

    log Q(m)  ≥  log PP(m,m,m)²  +  m² · log(1/2 − o(1))
             =  2 L_3 · m²  −  m² · log 2  +  o(m²).

Dividing by `m²`:  **`c_3 ≥ 2 L_3 − log 2 ≈ 0.877`**.

**Status.** Rigorous given: (i) distributive-lattice property of antitone
pairs (direct), (ii) Harris–FKG (Mathlib has this for product measures on
lattices; the specialization needs work), (iii) `max pₖ → 0` for antitone
marginals (requires Okounkov–Reshetikhin limit-shape concentration — a
substantial result, but **cited** not re-proved).

**Gap to `2 L_3`.** The `−log 2` loss comes from FKG giving only a product
lower bound on `P(⋂ A_{ij})`, treating cells as effectively independent.
In reality, the events are **highly positively correlated** via the antitone
structure: typically, if `ψ > φ` at one cell, it's true at most cells.
Removing this loss requires a correlation-aware argument (Schur process).

**Lean feasibility.** ~Weeks if (i)-(iii) are available in Mathlib; months
if the marginal concentration has to be proved from scratch. The FKG step
for the distributive lattice is probably clean.

---

## Path B — Second-moment / Paley–Zygmund

**Claim:** Same bound as Path A (`c_3 ≥ 2 L_3 − log 2`), different machinery.

Let `X := #{ cells (i,j) : ψ(i,j) ≤ φ(i,j) }` on uniform `Ω`. Then
`Q(m) = |Ω| · P(X = 0)`. Standard second-moment bounds on `P(X = 0)` give
at best `P(X = 0) ≥ 1/(1 + Var(X)/E[X]²)`. For large `m`, `E[X] ≈ m²/2`,
`Var(X) ≤ E[X]² · m^{O(1)}`, so `P(X = 0) ≥ m^{-O(1)}`, which gives
`log Q/m² ≥ 2 L_3 − o(1) → 2 L_3`.

**WAIT** — if this works, we're done.

**Checking more carefully.** For Paley–Zygmund to give `P(X = 0) ≥ Ω(1)`,
we'd need `Var(X) ≤ O(E[X])`, i.e., tight concentration. For `X` = sum over
cells, `Var(X) = ∑_{ij,i'j'} Cov(1_{A_{ij}}, 1_{A_{i'j'}})`. For independent
cells, `Var(X) = E[X] = Θ(m²)`. But cells are **positively correlated**
(antitone structure), so `Cov > 0` and `Var(X) ≥ E[X]²/m^O(1)` typically.

In fact for highly correlated indicators, `Var(X) ≈ E[X]²`, and
Paley–Zygmund degenerates to `P(X = 0) ≥ 1/2` at best. That'd give
`Q(m) ≥ |Ω|/2`, equivalent to `c_3 ≥ 2 L_3 − log 2 / m²` → `c_3 ≥ 2 L_3`.

**This is the key observation.** If the antitone correlations are strong
enough that `Var(X) = O(E[X]²)`, then Paley–Zygmund gives `c_3 = 2 L_3`.

**Status.** Requires proving `Var(X) = O(E[X]²)` for uniform antitone pairs.
This is a concentration statement about the fluctuation of the "inversion
count" between two independent plane partitions. Plausible from limit-shape
theory but not a standard citation.

**Gap.** Proving the concentration. Might be within reach via:
- Direct moment calculation (write out covariances explicitly)
- Log-Sobolev / spectral gap for random plane partitions
- Reflection-coupling arguments

**Lean feasibility.** If the concentration is proved externally, Lean
formalization of Paley–Zygmund conclusion is manageable. If the concentration
has to be derived in Lean, that's months of probability-theory library work.

---

## Path C — Reflection / coupling symmetry

**Claim:** `Q(m) ≥ |Ω|/2 · (1 − tiny)`, giving `c_3 = 2 L_3`.

Define the involution `σ : Ω → Ω` by `σ(φ, ψ) = (ψ, φ)` (swap). This is
measure-preserving. Partition `Ω` into orbits of `σ`:
- Fixed points: `(φ, φ)`, count = `PP(m,m,m)` (diagonal).
- 2-orbits: `{(φ, ψ), (ψ, φ)}` with `φ ≠ ψ`, count = `(|Ω| − PP)/2`.

Each 2-orbit contains exactly one element satisfying "φ ≤ ψ lex" (pick
either; they're complementary under σ). So `|{(φ,ψ) : φ ≤ ψ lex, φ ≠ ψ}| =
(|Ω| − PP)/2`.

But this counts pairs with `φ ≤ ψ` **lexicographically**, not pointwise.
The set we want is `{(φ,ψ) : φ ≤ ψ pointwise}`, which is NOT
symmetric-under-`σ` in the same clean way.

**Dead end.** The swap involution doesn't respect pointwise order.

**Remediation via a different involution?** If we had an involution that
(a) preserves the measure, (b) sends `{φ < ψ pointwise}` to `{φ > ψ
pointwise}` bijectively with "mixed" pairs cycling among themselves in small
orbits, then by orbit counting:
  `|{φ < ψ pointwise}| = |{φ > ψ pointwise}| = (|Ω| − |mixed|)/2`.
If `|mixed| = o(|Ω|)`, then `Q(m) ~ |Ω|/2 = PP(m)²/2`, giving `c_3 = 2 L_3`.

No such involution is obvious for pointwise order on antitone pairs.

**Status.** Dead end as stated. Possible remediation via a clever
construction, but none known.

---

## Path D — Interlacement / zipper reduction

Every pair `(φ, ψ)` with `φ < ψ` encodes a nested sequence of downsets of
`[m]³`. Specifically, for each level `k ∈ {1, ..., m}`, let
  `D_k^ψ := {(i,j,ℓ) : ℓ < ψ(i,j) and ℓ ≥ k−1}` (a slab)
  `D_k^φ := {(i,j,ℓ) : ℓ < φ(i,j) and ℓ ≥ k−1}`
Then `Q(m)` counts `(m−1)`-tuples of pairs `(D_k^ψ, D_k^φ)` with specific
interlacing.

**Schur-process interpretation.** This is exactly the "Hall-Littlewood
specialization" of the periodic Schur process at `q = 1`. Borodin 2007
(Thm. 1 + §3) gives product formulas for the generating function.
Specializing to our boundary data should give `Q(m)` in closed form.

**Status.** Requires *careful* derivation from Borodin's general formula.
Not a black-box citation — one has to identify the correct specialization
and compute. This is the "Step 4" of the paper-level proof in `C3Proof.md`.

**Lean feasibility.** Not achievable without a Mathlib Schur-process library.

---

## Path E — Entropy / free-energy argument

Define `F(m) := log Q(m) / m²`. Show `F` is essentially concave in `1/m`,
with boundary data `F(1) = 0` and `F(∞) = 2 L_3`.

**Concavity evidence.** From data, `F(2) = 0.749, F(3) = 1.009, F(4) = 1.144,
F(5) = 1.228`. Differences (discrete first deriv): `0.260, 0.135, 0.084`.
Ratios of diffs: `0.52, 0.62`. Consistent with concavity.

**Approach.** If `F(m)` is provably concave in `1/m` (analytic claim about
the interaction of antitone constraint with cell count), then by tangent-line
bounds,

    F(m)  ≥  F(m₀) + F'(m₀) · (m − m₀)  +  o(m)

Taking `m₀ = 5` and using `F(5) = 1.228, F'(5) ≈ 0.08` gives
`F(∞) ≥ 1.228 + 0.08 · ∞`, blowing up. So we need concavity in a different
variable — in `1/m`.

In `1/m` coordinates: `F(5) = 1.228` at `1/m = 0.2`; `F(4) = 1.144` at
`1/m = 0.25`. Slope `(1.144 − 1.228)/(0.25 − 0.2) = −1.68`. Extrapolating
to `1/m = 0`: `F(∞) ≈ 1.228 + 0.2 · 1.68 ≈ 1.564`. That matches 2 L_3.

**Status.** If concavity of `F` in `1/m` can be proved, we get `F(∞) ≥ 2 L_3`
rigorously, closing the sandwich. The concavity claim itself reduces to
a log-convexity / log-concavity statement about certain combinatorial
quantities — potentially tractable by Graham–Knuth or similar.

**Problem.** No standard theorem directly gives this concavity. Would need
original proof.

---

## Path F — Limit-shape variational argument

The Okounkov–Reshetikhin / Cerf–Kenyon variational principle gives, for
boundary-condition-constrained plane partitions, a variational formula
for the asymptotic count:

    log(# constrained PPs) / m²  →  sup_σ ∫∫ H(∇σ) dx dy

where `σ` is a surface function, `H` is the "free energy" / entropy density,
and the integral is over the support of `σ`.

For **single** plane partitions: `sup = ∫∫ H_0 = L_3`.

For **pairs** `(φ, ψ)` with `φ < ψ`: the sup is over pairs of surfaces
`(σ, τ)` with `σ ≤ τ`. The entropy is additive, `H(σ, τ) = H_0(σ) + H_0(τ)`,
and the constraint `σ ≤ τ` is a pointwise constraint that doesn't change
the sup value (just restricts to the "ordered cone" of pair surfaces).

Since the optimizing single-PP surface is the **same** for φ and ψ (both
want the limit shape), the pair sup is `2 L_3`, achieved by `(σ*, τ*)` with
`σ* < τ*` in any infinitesimal shift. The cost of enforcing strict
pointwise inequality is `0` in the `m²` scaling (it's an `m`-scaling "edge"
correction).

**Conclusion.** `log Q(m) / m² → 2 L_3`.

**Status.** This IS the expected proof. It's rigorous at the level of
variational calculus / calculus of variations. The Cerf–Kenyon machinery
is in a series of published papers. Making it Lean-formal requires
formalizing continuous-surface entropy and variational principles.

**Lean feasibility.** Multi-year research project (Mathlib doesn't have
any of this machinery).

---

## Summary ranking

| Path | Rigor status | Bound achieved | Lean effort |
|---|---|---|---|
| A (FKG) | Rigorous w/ 1 citation | `2 L_3 − log 2` | Weeks |
| B (Paley–Zygmund) | Needs `Var` concentration | `2 L_3` if concentration holds | Weeks post-concentration |
| C (Reflection) | Dead end | — | — |
| D (Schur process) | Cited black box | `2 L_3` | Years |
| E (Concavity of `F` in `1/m`) | Conjectural | `2 L_3` if concavity holds | Months post-concavity |
| F (Variational) | Cited black box | `2 L_3` | Years |

## Recommendation

**Path A is the honest "closest Lean theorem" target.** It gives a
strict improvement `c_3 ≥ 2 L_3 − log 2` via FKG + antitone-marginal
concentration — both of which are reasonably approachable in Mathlib.

**Path B is the "highest upside if we can prove concentration" target.** If
`Var(X)/E[X]² = O(1)` can be established for the inversion count between
two uniform antitone plane partitions, we close to `c_3 = 2 L_3` without
Schur-process heavy machinery. This is the key technical step worth pursuing.

**Path E is the "clean structural" target.** If concavity of
`log Q(m)/m²` in `1/m` can be established, we're done. Would need an
original proof, but it's an elegant direction.

**Paths D, F are the "correct but heavy" routes.** They prove the full result
via established literature but require multi-year Lean library development.

## Path G — Lattice-theoretic (after OEIS A056936 identification)

**Key identification:** By Step 3 of the bijection in `C3Proof.md`,
`Q(m) = #{order ideals of the 4D poset [m]·[m]·[2]·[m−1]}`, i.e., the size
of the distributive lattice `J([m]²·[2]·[m−1])`.

**OEIS check:** Q(4) = 89,613,429 = A056936(4), where A056936 is
"Antichains (or order ideals) in the poset 2·3·4·n." At `n = 4` the
underlying poset is `2·3·4·4 = 2·(m−1)·m·m` with `m = 4`. A single-value
coincidence because Q(m) traces a different diagonal of the same family.

**Reference unlocked:** Berman, Koehler, "Cardinalities of finite distributive
lattices", *Mitteilungen aus dem Mathematischen Seminar Giessen* 121 (1976),
pp. 103–124. This studies the counts `|J([a]·[b]·[c]·[d])|` directly and
pre-dates the Schur-process machinery by decades. The asymptotics they
consider are for one dimension growing with others fixed, not our diagonal,
but the framework is elementary lattice theory — transfer matrix on 3D
order ideals. Worth reading for the specific diagonal `a = b = m,
c = 2, d = m − 1`.

**Approach.** The asymptotic `log|J([a]·[b]·[c]·[d])|` as all dimensions grow
proportionally is the **bulk 4D solid-partition entropy**. This is essentially
a lattice animal / dimer-model entropy, computable via:
- Thermodynamic variational principle (Cerf–Kenyon–Sheffield, 2004+).
- Transfer matrix in one dimension with matrix size growing.

**Status.** Identifies the right classical framing. Closed-form asymptotic
not obvious from the lattice-theoretic view, but the problem becomes a
standard question in lattice-animal entropy, which has been studied.

**Lean feasibility.** Comparable to path D — the lattice framing doesn't
make Lean formalization easier, but it cleanly identifies the quantity.

## What I'd do next

1. Attempt Path B: write explicit moments of the inversion count `X` between
   two uniform antitone plane partitions for `m = 2, 3, 4, 5`. If
   `Var(X)/E[X]²` is bounded by a constant numerically, that's strong evidence
   for Paley–Zygmund route.

2. If (1) looks promising, try to prove the variance bound rigorously. This
   would close `c_3 = 2 L_3` without importing Schur-process machinery.

3. If (1) fails (variance blows up), fall back to Path A and prove
   `c_3 ≥ 2 L_3 − log 2` rigorously via FKG.
