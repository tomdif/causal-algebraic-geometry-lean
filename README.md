# Causal-Algebraic Geometry — Lean 4 Formalization

Formal verification of the mathematical framework developed in the accompanying papers. The codebase covers the algebraic-geometric foundations (causal algebras, CSpec, structure sheaves, cohomology), the combinatorial core (grid-convex subset counting, growth constants, dimension law), and gauge-theoretic results (Wilson loop independence).

## Codebase

**46 files, 11,019 lines.** One `sorry` remains (`crossing_pairs_bound` in `RhoEquals16.lean` for m ≥ 9), affecting only the exact value ρ₂ = 16. The dimension law, tiling inequality, and all structural results are sorry-free.

Build: `lake build` (~3,100 jobs, Lean 4 v4.28.0, Mathlib v4.28.0).

## Papers

The `papers/` directory contains the three papers this formalization supports:

| Paper | File | Status |
|-------|------|--------|
| Causal-Algebraic Geometry | `causal_algebraic_geometry.tex` | Foundations: CSpec, sheaves, cohomology, Noetherian ratio, arithmetic bridge |
| Order-Convex Subsets of Grid Posets | `grid_convex_subsets.tex` | Counting: sequence, transfer matrix, growth constant ρ₂ = 16 |
| Black Hole Thermodynamics from Counting Convex Subsets | `bh_thermodynamics.tex` | Physics: dimension law, area law, Hawking temperature, cosmological constant |

A fourth paper (JT gravity from the BD-weighted partition function) is at [tomdif/jt-gravity-from-convex-subsets](https://github.com/tomdif/jt-gravity-from-convex-subsets).

## Key Verified Results

### Dimension law (DimensionLaw.lean, AntichainTiling.lean — 0 sorry)

For all d ≥ 2 and m ≥ 1: the number of order-convex subsets of [m]^d satisfies

- **Upper bound**: `numConvexDim d m ≤ downsetCountDim d m * upsetCountDim d m`
- **Supermultiplicativity**: `numConvexDim d m * numConvexDim d n ≤ numConvexDim d (m + n)`
- **Tiling inequality**: `numConvexDim d m ^ ac.card ≤ numConvexDim d (k * m)` for any antichain `ac` of [k]^d
- **Exponential lower bound**: `2 ^ m ≤ numConvexDim d m`

Combined with the antichain bound A(k,d) = Θ(k^{d-1}), these establish log |CC([m]^d)| = Θ(m^{d-1}).

### Growth constant ρ₂ = 16 (TightUpperBound.lean, GrowthRateIs16.lean — 0 sorry in new files)

- `card_downsets_eq_choose`: the number of downsets of [m]² equals C(2m, m)
- `numGridConvex_le_choose_sq`: |CC([m]²)| ≤ C(2m, m)²
- `growth_constant_eq_neg_log_sixteen`: the Fekete limit equals −log 16

Inherits one sorry from `RhoEquals16.lean` (the Catalan lower bound at m ≥ 9).

### Wilson loop (GaugeConnection.lean — 0 sorry)

- `cylinder_wilson_loop_trace`: on the grid [c] × [t], the normalized interval-projection trace equals (t−1)/t, independent of the spatial circumference c.

### Foundations (0 sorry throughout)

- `Supermultiplicativity.lean`: |CC([m+n]²)| ≥ |CC([m]²)| · |CC([n]²)|
- `GrowthConstant.lean`: Fekete's lemma gives convergence of log|CC|/m
- `MonotoneProfileBound.lean`: |CC([m]²)| ≤ 16^m via downset × upset injection
- `GridClassification.lean`: order-convex subsets have interval row fibers
- `DilworthProof.lean`: Dilworth's theorem (fully proved)
- `Separation.lean`: two 4-element posets with identical classical invariants but different Noetherian ratio

## File Organization

| Directory | Contents |
|-----------|----------|
| `CausalAlgebraicGeometry/` | All 46 Lean source files |
| `papers/` | LaTeX and PDF for the three papers |

### New files from the dimension law formalization

| File | Lines | Sorry | Content |
|------|-------|-------|---------|
| `DimensionLaw.lean` | 709 | 0 | Convex subsets of [m]^d, supermultiplicativity, bounds |
| `AntichainTiling.lean` | 235 | 0 | Block embedding, antichain incomparability, tiling inequality |
| `TightUpperBound.lean` | 147 | 0 | |CC([m]²)| ≤ C(2m,m)², downset-antitone bijection |
| `GrowthRateHelper.lean` | 206 | 0 | Central binomial bounds, log(poly)/n → 0 |
| `GrowthRateIs16.lean` | 132 | 0 | Fekete limit = −log 16 via squeeze |

## Axiom Audit

All key theorems (dimension law, tiling inequality, Wilson loop, upper bounds) depend only on the standard Lean kernel axioms: `propext`, `Classical.choice`, `Quot.sound`. The single `sorryAx` dependency is confined to `growth_constant_eq_neg_log_sixteen` via the inherited `crossing_pairs_bound`.

## Building

```bash
lake update
lake build          # ~3100 jobs
```

## License

Apache 2.0
