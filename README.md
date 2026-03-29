# Causal-Algebraic Geometry — Lean 4 Formalization

Formal verification of the mathematical framework developed in the accompanying papers. The codebase covers algebraic-geometric foundations (causal algebras, CSpec, structure sheaves, cohomology), the combinatorial core (grid-convex subset counting, growth constants, dimension law), gauge-theoretic results (Wilson loop, holonomy composition), the Benincasa-Dowker action (positive energy theorem, cylinder factorization), and separation/invariant analysis.

## Codebase

**64 files, 15,117 lines.** Zero sorry on the critical path. Thirteen sorries remain in standalone LGV lattice path files (`LGV.lean`, `LGVInvolution.lean`, `LGVLatticePath.lean`, `LindstromReflection.lean`) that are not imported by any other module.

Build: `lake build` (~3,100 jobs, Lean 4 v4.28.0, Mathlib v4.28.0).

## Papers

The `papers/` directory contains the three papers this formalization supports:

| Paper | File | Status |
|-------|------|--------|
| Causal-Algebraic Geometry | `causal_algebraic_geometry.tex` | Foundations: CSpec, sheaves, cohomology, Noetherian ratio, arithmetic bridge |
| Order-Convex Subsets of Grid Posets | `grid_convex_subsets.tex` | Counting: sequence, transfer matrix, growth constant ρ₂ = 16 |
| Black Hole Thermodynamics from Counting Convex Subsets | `bh_thermodynamics.tex` | Physics: dimension law, area law, Hawking temperature |

A fourth paper (JT gravity from the BD-weighted partition function) is at [tomdif/jt-gravity-from-convex-subsets](https://github.com/tomdif/jt-gravity-from-convex-subsets).

## Key Verified Results

### Growth constant ρ₂ = 16 (0 sorry)

- `crossing_pairs_le`: |crossing antitone pairs| ≤ C(2m+1,m)·C(2m-1,m) via domain-splitting Lindström injection
- `growth_constant_eq_neg_log_sixteen`: the Fekete limit equals −log 16
- `numGridConvex_le_choose_sq`: |CC([m]²)| ≤ C(2m, m)²
- `numGridConvex_ge_catalan_bound`: |CC([m]²)| ≥ C(2m,m)²/(2(m+1))

`#print axioms growth_constant_eq_neg_log_sixteen` returns only `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`.

### Discrete positive energy theorem (0 sorry)

- `bd_action_fullGrid`: S_BD([m]×[n]) = -(m-1)(n-1) + 1 for all m, n ≥ 1
- `bd_action_ge`: S_BD(S) ≥ -(m-1)(n-1) + 1 for all nonempty convex S
- `bd_action_eq_iff_full`: equality iff S = [m]×[n] (for m, n ≥ 2)
- `cylinder_bd_factorization`: S_BD(S × [t]) = t · S_BD_spatial(S) - |S| · (t-1)

Flat spacetime is the unique global minimizer of the Benincasa-Dowker action.

### Dimension law (0 sorry)

- `numConvexDim_supermul`: supermultiplicativity for all d ≥ 2
- `tiling_inequality`: |CC([m]^d)|^{|ac|} ≤ |CC([km]^d)| for any antichain ac of [k]^d
- `numConvexDim_exponential_lower`: 2^m ≤ |CC([m]^d)|

Together these give log |CC([m]^d)| = Θ(m^{d-1}).

### Convexity ↔ multiplication (0 sorry)

- `convexity_iff_preserves_multiplication`: S is causally convex iff restriction to S preserves multiplication
- `cspec_uniquely_determined`: CSpec is the unique topology supporting a structure sheaf
- `non_convex_breaks_restriction`: non-convex subsets break the ring homomorphism

### Separation theorems (0 sorry)

- `separation5_theorem`: two 5-element posets agreeing on 8 classical invariants (width, height, edges, antichains, maximal chains, comparable pairs, order ideals, join-irreducibles) but differing on γ
- `holonomy_separates_Y_fork`: holonomy weight distinguishes posets with identical classical invariants
- `gamma_chain_lt_gamma_antichain`: γ(chain) < γ(antichain) for all n ≥ 2

### Holonomy composition (0 sorry)

- `transitionMatrix_junction`: T_{p,q} · T_{q,r} = e_q (the discrete parallel transport law)
- `transitionMatrix_idempotent`: T_{p,q}² = T_{p,q}
- 4 nesting laws, orthogonality, completeness — establishing holonomy as a functor

### Recovery theorem — precise status

- `principalFilter_injective`: the non-strict filter α ↦ {β : α ≤ β} is always injective (no hypotheses needed)
- `closedPoint_isCausallyPrime`: strict upset ↑α is causally prime for non-maximal α
- `closedPoint_injective_T0`: strict upset map is injective under T₀ hypothesis
- `recovery_counterexample`: V-poset shows T₀ is necessary for strict upset injectivity
- `minimum_not_proper`: ↑≤(minimum) = Λ is not proper, hence not a CSpec point
- The "closed points" language from scheme theory does not apply correctly to CSpec

### Wilson loop (0 sorry)

- `cylinder_wilson_loop_trace`: normalized trace = (t-1)/t, independent of spatial circumference c

### Additional results (0 sorry)

- `grid_width_eq`: width([m]²) = m for all m
- `intervals_lt_convex`: intervals O(m⁴) vs convex subsets Θ(16^m) for all m ≥ 2
- `totalOrder_numCC_eq_numInt_succ`: |CC| = |Int| + 1 for total orders
- `sectorCount_zero_eq_one`: only the empty set has 0 blocks (all m, n)
- `subexp_lower_nat`: 16^m ≤ 16m³ · (|CC| + 1) (subexponential factor bound)
- D-finiteness: NEGATIVE — no recurrence of order ≤ 5 with polynomial degree ≤ 4
- State count: C(n+2,2) is the boundary-pair count (verified m ≤ 8)

## File Organization

| Directory | Contents |
|-----------|----------|
| `CausalAlgebraicGeometry/` | All 64 Lean source files |
| `papers/` | LaTeX and PDF for the three papers |

### Key files

| File | Lines | Content |
|------|-------|---------|
| `BDAction.lean` | 780 | BD action formula, positive energy theorem, uniqueness |
| `DimensionLaw.lean` | 709 | Convex subsets of [m]^d, supermultiplicativity, bounds |
| `CrossingBound.lean` | 276 | Domain-splitting Lindström injection, ρ₂ = 16 |
| `CylinderFactorization.lean` | 243 | S_BD(S×[t]) = t·S_spatial - |S|·(t-1) |
| `HolonomyComposition.lean` | 295 | 12 composition laws for discrete connection |
| `GammaOrdering.lean` | 337 | γ(chain) < γ(antichain), γ → 1 for chains |
| `Separation5.lean` | 262 | 5-element separation on 8 invariants |
| `ConvexityIFF.lean` | 160 | S convex ↔ restriction preserves multiplication |
| `T0Recovery.lean` | 119 | Non-strict filter always injective |
| `RecoveryLimitations.lean` | 93 | Precise limitations of recovery theorem |
| `IntervalVsConvex.lean` | 218 | Polynomial vs exponential growth |
| `GrowthRateIs16.lean` | 132 | Fekete limit = −log 16 |

## Axiom Audit

All key theorems depend only on the standard Lean kernel axioms: `propext`, `Classical.choice`, `Quot.sound`, plus `Lean.ofReduceBool` and `Lean.trustCompiler` (from `native_decide` for computational verification). No `sorryAx` on the critical path.

## Building

```bash
lake update
lake build          # ~3100 jobs
```

## License

Apache 2.0
