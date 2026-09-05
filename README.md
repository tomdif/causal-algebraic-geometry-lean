# Causal-Algebraic Geometry — Lean 4 Formalization

Formal verification of the mathematical framework deriving the Standard Model from a locally finite partial order. The codebase covers algebraic-geometric foundations (causal algebras, CSpec, structure sheaves), combinatorial core (grid-convex subset counting, growth constants, dimension law, near-vacuum partition functions), the Benincasa-Dowker action (spectral gap, saddle dominance, positive energy), the chamber kernel and Feshbach projection (Jacobi matrix J₄, spectral gap γ₄ = ln(5/3), Higgs mass prediction), gauge-theoretic results (holonomy, Wilson loop), the Landau-Ginzburg phase structure (trivial topological order, bottleneck lemma), and the Uvarov-Chebyshev identification of the chamber polynomials.

## Codebase

**316 Lean source files, 62,387 lines.** The audited default library and
`FinalCheck` endpoints contain no `sorry` and no project-defined axioms.
`RHTarget.lean` is an explicitly excluded experimental file with four custom
axioms; it is not imported by the default target. See [PROOF-PATH.md](PROOF-PATH.md).

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
- `ChamberGaloisBridge.lean`: rational chamber recurrence, exact base change to ℝ, structural deflation, and the genuine splitting-field Galois action
- `ChamberGaloisConjecture.lean`: all-dimensional full-symmetric surjectivity stated on that concrete action (still a conjecture in general)
- `ChamberGaloisD4.lean`: the first full-symmetry theorem, proving the canonical `d = 4` residual action is `S₂`
- `ChamberGenericFamily.lean`: parameterized chamber recurrence, exact arithmetic specialization, and the generic polynomial over `ℚ(δ)`
- `ChamberFrobenius.lean`: integral models and replayable finite-field factorization certificates, including the complete `d = 4`, mod-11 seed
- `UvarovChebyshev.lean`: Chamber polynomials as boundary-perturbed Chebyshev (not a new OP family)
- `IntegrationSpectrum.lean`: SM parameters from singular values of integration operator

### Landau-Ginzburg Phase Structure (0 sorry)

- `BottleneckLemma.lean`: Abstract bottleneck structure → Perron-Frobenius → unique ground state
- `TrivialTopologicalOrder.lean`: No topological order on any cylinder, structural proof for all L
- `LandauGinzburg.lean`: Capstone assembling the complete LG structure

### Algebraic Foundations (0 sorry)

- `ConvexityIFF.lean`: S convex ↔ restriction preserves multiplication (bridge theorem)
- `CSpecSheaf.lean`: algebraic locality for causal corner sections
- `CSpecActualSheaf.lean`: the generated CSpec topology and a genuine `TopCat.Sheaf (Type _)`, stored in `CausalSchemeData`
- `CSpecRingSheaf.lean`: the corresponding genuine `RingCat` sheaf of noncommutative causal-corner rings
- `CSpecChamberRoots.lean`: local residual chamber polynomials, their root-choice sheaf, faithful local Galois actions, and fixed-dimension constancy
- `CSpecChamberRootsCounterexample.lean`: a two-point CSpec counterexample to unrestricted root-sheaf local constancy
- `CSpecUniqueness.lean`: No enlargement possible — CSpec is forced by algebraic structure
- `Separation.lean`: Noetherian ratio γ detects geometry beyond classical invariants
- `HolonomyComposition.lean`: Junction law, functorial composition, gauge structure

### Combinatorial Core (0 sorry)

- `DimensionLawComplete.lean`: explicit all-d bounds proving log|CC([m]^d)| = Θ(m^{d-1})
- `C3BarrierLowerBound.lean`: certified deterministic-barrier lower bound for the c₃ problem
- `C3ShiftCompression.lean`: certified finite shift/fiber inequality
- `C3MultiscaleCompression.lean`: deterministic height quantization eliminates the limit-shape input and bounds the total correction by `exp(O(m^(3/2)))`
- `C3AsymptoticClosure.lean`: unconditionally proves two-boundary entropy factorization; proves the numerical `C3Conjecture` and convex-count limit from the single classical MacMahon cubic-box asymptotic
- `CAGMultidimensionalEntropy.lean`: extends unconditional two-boundary entropy factorization to every ambient dimension at least three, with an explicit finite error bound; dimension four covers boxed solid partitions
- `CAGSolidPartitionVolume.lean`: exact-volume coefficient decomposition, stabilization to the genuine solid-partition counting function, a polynomial-loss large-coefficient theorem, and volume control within quantization fibers. The fixed-volume asymptotic constant remains open; see [the research note](docs/SolidPartitionEntropyProgress.md)
- `CAGCompatibilityEntropy.lean`: splits compatibility surprisal into nonnegative height-trimming and weak-ordering costs, proves a codimension-two upper bound for trimming, and reduces the full area-upper-bound problem to weak ordering. The complete area law and any gravitational interpretation remain unproved; see [the experiment and proof note](docs/CompatibilityEntropyGravityTest.md)
- `CAGOrderingClusters.lean`: identifies each sorting fiber with one independent bit per connected disagreement region, proves the exact cluster partition function and locality of ownership constraints, and bounds ordering entropy by mean cluster counts in two explicitly different ensembles. See [the cluster investigation](docs/OrderingClusterProgress.md); it does not prove the remaining area law or gravitational dynamics.
- `CAGClusterStatistics.lean`: proves `W <= K*log 2 - log P_independent(c <= K)` and an explicit conditional area criterion. A separately tested CFTP experiment samples both ensembles through side 8 with uncertainty bounds; their different mean-cluster behavior cautions against a mean-only shortcut. See [the statistical investigation](docs/ClusterStatisticsProgress.md).
- `GrowthRateIs16.lean`: ρ₂ = 16 exactly
- `DivisibilityRenormalization.lean`: A394685 is scale-free — c_k(kp)·a(k-1) = c_k(kp-1)·a(k) for every k ≥ 1 and prime p ≥ k, where c_k counts divisibility-convex subsets of {k,...,n}; subsumes the prime-doubling theorem of `DivisibilityPoset.lean`/`PendantDoubling.lean` (the case k = 1). See docs/DivisibilityRenormalization.md
- `SlabCharacterization.lean`: Every convex subset of [m]^{d+1} is a slab between antitone boundaries
- `UniversalGap.lean`: Spectral gap Δ = 1, universal for all m ≥ 2
- `PartitionDimensionBridge.lean`: Two independent equations both select d = 3

### Boundary Geometry and Effective Dynamics (0 sorry)

- `CAGBoundaryGeometry.lean`: intrinsic L¹ metric on antitone boundary surfaces and a symmetric mixed plaquette-curvature tensor
- `CAGMedianGeometry.lean`: bounded distributive-lattice structure, exact valuation formula for the metric, unique three-boundary median, and global L¹ consensus minimization
- `CAGTransitionGeometry.lean`: one-cell Hasse graph, exact graph-distance theorem, unique graph medians, and an explicit isometric embedding into the Boolean cell hypercube
- `CAGFiniteCausalGeometry.lean`: the same metric/Hasse/median/partial-cube theorem stack for downsets of every finite causal poset and every finite `CAlg`, plus an intrinsic square-completion curvature kernel
- `CAGCubicalComplex.lean`: event hyperplanes, isometric higher-dimensional causal cubes with face closure, cubical links, and the intrinsic link Laplacian
- `CAGScalingLimit.lean`: finite-chain state graphs identified with path lattices, exact centered graph Laplacian, and a fixed-length family with certified quadratic continuum-consistency error
- `CAGTwoDimensionalLimit.lean`: disjoint pairs of causal chains identified exactly with rectangular grid state spaces, the intrinsic five-point Laplacian, and a fixed-square family with certified quadratic continuum-consistency error
- `CAGPlaquetteLimit.lean`: elementary rectangles realized as intrinsic two-event causal cubes whose link edge and alternating field sum recover the mixed continuum Hessian on coupled quartic surfaces
- `CAGProductScalingLimit.lean`: arbitrary finite families of independent causal chains identified with higher-dimensional path products, exact Manhattan distance and `(2d+1)`-point Laplacian, and a dimension-uniform fixed-cube continuum limit
- `CAGSmoothScalingLimit.lean`: Mathlib Taylor theory upgrades the product limit from polynomial calibration to arbitrary coupled coordinate-smooth fields, with the sharp uniform error bound `(sum M_i)h²/12` and fixed-domain convergence
- `CAGNonproductScalingLimit.lean`: every finite causal poset gets an exact radial birth–death Laplacian determined by intrinsic upward/downward branching, plus a smooth drift–diffusion expansion, a branching-balance criterion, and bounded-branching continuum convergence
- `CAGDirectionalGeometry.lean`: a complete intrinsic event-labeled frame on every finite causal-state graph, an exact directional decomposition of its Laplacian, the order-curvature identity saying mixed frontier sectional defect is precisely the indicator of causal precedence, and the full trace formula `K_dir=2·(# frontier causal incidences)`
- `CAGDiscreteConnection.lean`: the canonical partial event-wall connection between variable-dimensional directional frames, with identity/inverse/composition laws, zero holonomy on its domain, a positive-definite fiber metric preserved by transport, and covariant finite differences
- `CAGFunctorialGeometry.lean`: order-isomorphic causal posets have isometric state graphs and naturally equivalent tangent frames, with invariant tangent norm, connection, sectional kernel, and total directional curvature
- `CAGCausalRefinement.lean`: past-closed embeddings into genuinely larger causal posets preserve old distances, transitions, tangent directions, metric, and connection, while the refined degree splits into old degree plus an exact count of newly created directions
- `CAGRefinementTower.lean`: compatible infinite refinement sequences obey an exact cumulative tangent-dimension law, linear-growth and stabilization criteria, and a universal normalized directional-curvature bound in `[0,1]`
- `CAGRefinementConvergence.lean`: every refinement tower has a convergent normalized-curvature subsequence; summable variation forces full curvature and persistent-old-frame field convergence with rigorous tail error bounds
- `CAGBoundaryDynamics.lean`: exact Euler–Lagrange derivation of the discrete Poisson equation for an explicitly stated boundary Dirichlet effective action
- `CAGFiniteCausalDynamics.lean`: exact graph-Laplacian Euler–Lagrange equation for that effective action on arbitrary finite causal-state graphs
- `CAGBoundaryDynamics.lean`: exact lattice dispersion `ω²=(c/a)²4sin²(q/2)`, a conditional falsifiable signature once the effective action and lattice scale are independently fixed

These are genuine finite causal-state geometric structures. They are not presented as a derived Lorentzian event-spacetime metric, Riemann tensor, or Einstein equation; [the status document](docs/CAGBoundaryGeometryStatus.md) separates proved results from effective hypotheses.

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

The endpoints in `CausalAlgebraicGeometry/FinalCheck.lean` have pinned
`#print axioms` reports. They depend only on `propext`, `Classical.choice`,
and `Quot.sound`; the exact-growth endpoint additionally uses
`Lean.ofReduceBool` and `Lean.trustCompiler` through `native_decide`.
`#guard_msgs` makes an unexpected dependency change fail the build.

This audit is intentionally scoped to the default library. The experimental,
non-imported `RHTarget.lean` contains four declared axioms and is not presented
as a proved RH formalization.

For the focused audit:

```bash
lake build CausalAlgebraicGeometry.FinalCheck
```

## Building

```bash
lake update
lake build
```

## License

Apache 2.0
