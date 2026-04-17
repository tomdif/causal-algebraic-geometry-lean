# Causal-Algebraic Geometry — Lean 4 Formalization

Formal verification of the mathematical framework deriving the Standard Model from a locally finite partial order. The codebase covers algebraic-geometric foundations (causal algebras, CSpec, structure sheaves), combinatorial core (grid-convex subset counting, growth constants, dimension law, near-vacuum partition functions), the Benincasa-Dowker action (spectral gap, saddle dominance, positive energy), the chamber kernel and Feshbach projection (Jacobi matrix J₄, spectral gap γ₄ = ln(5/3), Higgs mass prediction), gauge-theoretic results (holonomy, Wilson loop), the Landau-Ginzburg phase structure (trivial topological order, bottleneck lemma), and the Uvarov-Chebyshev identification of the chamber polynomials.

## Codebase

**254 files, 45,856 lines.** Zero sorry. Zero custom axioms beyond Lean's core (propext, choice, quot.sound).

Build: `lake build` (Lean 4 v4.28.0, Mathlib v4.28.0).

## Companion Repository

The physics derivation (gauge group, Higgs mass, electroweak scale, Born rule, Einstein equation) is formalized in [tomdif/unifiedtheory](https://github.com/tomdif/unifiedtheory) (~200 Lean files, also zero sorry).

## Key Verified Results

### Near-Vacuum Theorem and Partition Functions (0 sorry)

- `NearVacuumTheorem.lean`: CC_{m²-k}([m]²) = A000712(k) = (p * p)(k), generating function η(q)^{-2}
- `NearVacuumFull.lean`: Stabilization for all m > k via NIS equivalence (explicit Equiv, not native_decide)
- `NearVacuumD3.lean`: Extension to d=3 (plane partitions squared), all 4 sorry eliminated
- `NearVacuumHigherD.lean`: Dimensional ladder conjecture, computational verification for d=3,4
- `EtaConnection.lean`: Connection to Dedekind eta function
- `BoundaryHolography.lean`: The exponent 2 in η(q)^{-2} counts boundaries, not bosons

### Spectral Theory and Chamber Kernel (0 sorry)

- `ChamberKernel.lean`: K_F defined from the order kernel, R-decomposition
- `VolterraBridge.lean`: Jacobi entries from Volterra singular value ratios
- `VolterraConvergence.lean`: Explicit O(1/m²) error bound for SV ratio convergence
- `SpectralData.lean`: Characteristic polynomial (5λ-3)(150λ²-50λ+3)=0, discriminant analysis
- `UvarovChebyshev.lean`: Chamber polynomials as boundary-perturbed Chebyshev (not a new OP family)
- `IntegrationSpectrum.lean`: SM parameters from singular values of integration operator

### Landau-Ginzburg Phase Structure (0 sorry)

- `BottleneckLemma.lean`: Abstract bottleneck structure → Perron-Frobenius → unique ground state
- `TrivialTopologicalOrder.lean`: No topological order on any cylinder, structural proof for all L
- `LandauGinzburg.lean`: Capstone assembling the complete LG structure

### Algebraic Foundations (0 sorry)

- `ConvexityIFF.lean`: S convex ↔ restriction preserves multiplication (bridge theorem)
- `CSpecSheaf.lean`: CSpec is the unique topology compatible with the structure sheaf
- `CSpecUniqueness.lean`: No enlargement possible — CSpec is forced by algebraic structure
- `Separation.lean`: Noetherian ratio γ detects geometry beyond classical invariants
- `HolonomyComposition.lean`: Junction law, functorial composition, gauge structure

### Combinatorial Core (0 sorry)

- `DimensionLaw.lean`: log|CC([m]^d)| = Θ(m^{d-1}) (area-law scaling)
- `GrowthRateIs16.lean`: ρ₂ = 16 exactly
- `SlabCharacterization.lean`: Every convex subset of [m]^{d+1} is a slab between antitone boundaries
- `UniversalGap.lean`: Spectral gap Δ = 1, universal for all m ≥ 2
- `PartitionDimensionBridge.lean`: Two independent equations both select d = 3

### Benincasa-Dowker Action (0 sorry)

- `DiscreteGaussBonnet.lean`: 2·S_BD = Σ(2 - deg)
- `BDAction.lean`: Positive energy theorem
- `SaddleDominance.lean`: Flat dominates Z(β)
- `CylinderForced.lean`: Convexity + boundary conditions → full cylinder
- `ParameterFreePrediction.lean`: T·S = m/(d-2)
- `ThermodynamicSignatures.lean`: Negative specific heat, Bekenstein d=4 selection

### Dimension Selection (0 sorry)

- `SpectralData.lean`: Feshbach discriminant symmetric around d=3; prime at d=2 AND d=4
- `PartitionDimensionBridge.lean`: 2d+3 = d² selects d = 3 (independent of Lovelock)

### RG Flow and Dynamics (0 sorry)

- `GrowthRule.lean`: 3-slice convexity constraint as Markov growth rule
- `TransferMatrixComputable.lean`: Decidable growth rule with branching factors
- `BottleneckLemma.lean`: Abstract bottleneck → unique ground state for all cylinders
- `TrivialTopologicalOrder.lean`: No topological order (structural proof)
- `PathGraphOrigin.lean`: K_F at minimal m is the path graph (bare RG theory)
- `RGFlow.lean`: Parameter-free flow from path graph to Volterra fixed point
- `Universality.lean`: The RG fixed point is unique and inescapable
- `SpectralGapConvergence.lean`: Two routes to ln(5/3) unified
- `FeshbachProjection.lean`: R-decomposition, target ratios, monotone convergence

### Cosmological Constant (0 sorry)

- `CosmologicalConstant.lean`: Λ = Δ²/√N structural theorem (Sorkin + spectral gap)
- `CCCoefficient.lean`: Two candidates: c=1 (Sorkin) or c=Δ_raw=2 (BD action)

### Structural Insights (0 sorry)

- `UvarovChebyshev.lean`: Chamber polynomials as boundary-perturbed Chebyshev
- `LandauGinzburg.lean`: Complete LG structure capstone
- `BoundaryHolography.lean`: η(q)^{-2} exponent counts boundaries, not bosons
- `IntegrationSpectrum.lean`: SM from singular values of integration operator
- `CSpecUniqueness.lean`: CSpec is the unique compatible topology
- `PartitionDimensionBridge.lean`: Two independent roads to d=3

## Axiom Audit

All theorems depend only on standard Lean kernel axioms: `propext`, `Classical.choice`, `Quot.sound`, plus `Lean.ofReduceBool` and `Lean.trustCompiler` (from `native_decide`). No `sorryAx` anywhere.

## Building

```bash
lake update
lake build
```

## License

Apache 2.0
