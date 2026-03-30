# Causal-Algebraic Geometry — Lean 4 Formalization

Formal verification of the mathematical framework developed in the accompanying papers. The codebase covers algebraic-geometric foundations (causal algebras, CSpec, structure sheaves, cohomology), the combinatorial core (grid-convex subset counting, growth constants, dimension law), the Benincasa-Dowker action (positive energy theorem, discrete Gauss-Bonnet, spectral gap, saddle dominance), gauge-theoretic results (holonomy composition, Wilson loop), thermodynamic signatures (parameter-free T·S prediction, negative specific heat, Bekenstein d=4 selection), and separation/invariant analysis.

## Codebase

**82 files, 17,343 lines.** Zero sorry on the critical path. Thirteen sorries remain in standalone LGV lattice path files (`LGV.lean`, `LGVInvolution.lean`, `LGVLatticePath.lean`, `LindstromReflection.lean`) that are not imported by any other module.

Build: `lake build` (~3,100 jobs, Lean 4 v4.28.0, Mathlib v4.28.0).

## Papers

The `papers/` directory contains the four papers this formalization supports:

| Paper | File | Content |
|-------|------|---------|
| Causal-Algebraic Geometry | `causal_algebraic_geometry.tex` | Foundations: CSpec, sheaves, bridge theorem, Noetherian ratio, arithmetic bridge |
| Order-Convex Subsets of Grid Posets | `grid_convex_subsets.tex` | Counting: sequence, transfer matrix, growth constant ρ₂ = 16 |
| Black Hole Thermodynamics | `bh_thermodynamics.tex` | Physics: dimension law, area law, Hawking temperature, d=4 selection |
| JT Gravity | at [tomdif/jt-gravity-from-convex-subsets](https://github.com/tomdif/jt-gravity-from-convex-subsets) | BD partition function, JT effective action, density of states |

## Key Verified Results

### The complete derivation chain (all 0 sorry)

1. **Bridge theorem** (`ConvexityIFF.lean`): S convex ↔ restriction preserves multiplication
2. **Dimension law** (`DimensionLaw.lean`, `AntichainTiling.lean`): log|CC([m]^d)| = Θ(m^{d-1})
3. **Growth constant** (`CrossingBound.lean`, `GrowthRateIs16.lean`): ρ₂ = 16 exactly
4. **Discrete Gauss-Bonnet** (`DiscreteGaussBonnet.lean`): 2·S_BD = Σ(2 - deg), local curvature decomposition
5. **Positive energy** (`BDAction.lean`): S_BD(S) ≥ -(m-1)(n-1)+1, equality iff S = flat
6. **Spectral gap** (`UniversalGap.lean`, `SpectralGap.lean`): Δ = 1, first excited degeneracy = 2
7. **Saddle dominance** (`SaddleDominance.lean`): flat dominates Z(β) when β > m·ln(16)
8. **Stationarity derived** (`CylinderOptimal.lean`): full cylinder minimizes 3D S_BD among ALL convex subsets
9. **Cylinder forced** (`CylinderForced.lean`): convexity + boundary conditions → full cylinder
10. **Cylinder factorization** (`CylinderFactorization.lean`): S_BD(S×[t]) = t·S_spatial - |S|·(t-1)
11. **Parameter-free prediction** (`ParameterFreePrediction.lean`): T·S = m/(d-2), c cancels
12. **Negative specific heat** (`ThermodynamicSignatures.lean`): C = -S/(d-3) < 0 for d ≥ 4
13. **Bekenstein selection** (`ThermodynamicSignatures.lean`): S/(ER) ∝ m^{d-4}, constant iff d = 4
14. **Four-way d=4 selection**: Hawking, specific heat, Bekenstein, evaporation — from one exponent

### Separation and invariants (0 sorry)

- `separation5_theorem`: 5-element posets agreeing on 8 classical invariants, separated by γ
- `holonomy_separates_Y_fork`: holonomy weight distinguishes classically identical posets
- `dimensional_ordering`: γ(chain) < γ(grid) < γ(antichain) for all m ≥ 2

### Algebraic structure (0 sorry)

- `convexity_iff_preserves_multiplication`: the bridge theorem (clean IFF)
- `cspec_uniquely_determined`: CSpec is the unique sheaf-compatible topology
- `principalUpset_isCausallyPrime`: ↑α is ALWAYS a CSpec point (no hypotheses)
- `bulletproof_recovery`: T₀ posets fully recoverable from CSpec
- `gluing_dimension_gap`: corner algebras do NOT satisfy gluing (honest limitation)
- `cspec_larger_than_primes`: CSpec ≇ Spec(Z/nZ) — CSpec is strictly richer

### Holonomy (0 sorry)

- `transitionMatrix_junction`: T_{p,q}·T_{q,r} = e_q (functorial composition)
- `cylinder_wilson_loop_trace`: trace = (t-1)/t, independent of spatial circumference

### Boundary and fluctuations (0 sorry)

- `boundary_fluctuation`: exactly 2 removable elements from [m]² (min and max)
- `max_bd_eq_width_small`: max S_BD = width = m on [m]²
- `antidiag_bd_4`: anti-diagonal achieves S_BD = 4 > min(d,m) = 2 (disproves UV cutoff claim)

### Counting and asymptotics (0 sorry)

- `numGridIntervals_le`: |Int([m]²)| ≤ m⁴+1 (polynomial)
- `intervals_lt_convex`: |Int| < |CC| for all m ≥ 2 (exponential dominates)
- `numIntervals_ge_sq_div_width`: |Int| ≥ n²/(2w) via Cauchy-Schwarz
- `subexp_lower_nat`: 16^m/(16m³) ≤ |CC([m]²)| ≤ 16^m
- D-finiteness: NEGATIVE — no recurrence of order ≤ 5

## Physics bridge (honest accounting)

The derivation chain above requires exactly **two physics identifications**:

- **β = 8πm** (inverse Hawking temperature = temporal extent, from GR)
- **m = r_s/ℓ** (grid size = Schwarzschild radius / lattice spacing)

Vacuum stationarity is **derived** (CylinderOptimal.lean). Black hole stationarity for excited states remains an assumption. See `HonestAccounting.lean` for the precise logical structure.

**Falsifiable prediction**: c₃ ≤ π (growth constant of |CC([m]³)| must satisfy the Bekenstein bound).

## File Organization

| Directory | Contents |
|-----------|----------|
| `CausalAlgebraicGeometry/` | 82 Lean source files |
| `papers/` | LaTeX and PDF for the four papers |

## Axiom Audit

All key theorems depend only on standard Lean kernel axioms: `propext`, `Classical.choice`, `Quot.sound`, plus `Lean.ofReduceBool` and `Lean.trustCompiler` (from `native_decide`). No `sorryAx` on the critical path.

## Building

```bash
lake update
lake build          # ~3100 jobs
```

## License

Apache 2.0
