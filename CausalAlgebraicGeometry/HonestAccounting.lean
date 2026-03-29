/-
  HonestAccounting.lean — Precise separation of theorem from interpretation.

  THE COMPLETE DERIVATION CHAIN WITH EXACT BOUNDARIES.

  ════════════════════════════════════════════════════
  PURE COMBINATORICS (proved, no physics input)
  ════════════════════════════════════════════════════

  1. Dimension law: log|CC([m]^d)| = Θ(m^{d-1})
     [DimensionLaw.lean, AntichainTiling.lean]

  2. Growth constant: ρ₂ = 16
     [CrossingBound.lean, GrowthRateIs16.lean]

  3. Positive energy: S_BD(S) ≥ S_BD(flat), equality iff S = flat
     [BDAction.lean]

  4. Gauss-Bonnet: 2·S_BD = Σ(2 - deg), local curvature decomposition
     [DiscreteGaussBonnet.lean]

  5. Spectral gap: Δ = 1, first excited degeneracy = 2
     [UniversalGap.lean, SpectralGap.lean]

  6. Saddle dominance: flat dominates Z(β) when β > m·ln(16)
     [SaddleDominance.lean]

  7. Cylinder uniqueness: convexity + same boundary at both ends → full cylinder
     [CylinderForced.lean]

  8. Cylinder factorization: S_BD(S×[t]) = t·S_spatial - |S|·(t-1)
     [CylinderFactorization.lean]

  9. Bridge theorem: S convex ↔ restriction preserves multiplication
     [ConvexityIFF.lean]

  10. Separation: γ distinguishes posets invisible to 8 classical invariants
      [Separation5.lean]

  ════════════════════════════════════════════════════
  ALGEBRA (proved, uses only the dimension law exponent)
  ════════════════════════════════════════════════════

  11. Energy cancellation: T·S = m/(d-2), parameter-free
      [ParameterFreePrediction.lean]

  12. Negative specific heat: C = -S/(d-3) < 0 for d ≥ 4
      [ThermodynamicSignatures.lean]

  13. Bekenstein exponent: S/(ER) ∝ m^{d-4}, constant at d=4 only
      [ThermodynamicSignatures.lean]

  14. Four-way d=4 selection: Hawking, specific heat, Bekenstein, evaporation
      [ThermodynamicSignatures.lean, ParameterFreePrediction.lean]

  ════════════════════════════════════════════════════
  PHYSICS BRIDGE (assumed, not proved from combinatorics)
  ════════════════════════════════════════════════════

  ❗ A. Stationarity ⇒ identical boundary slices
        "A static equilibrium has the same spatial geometry at both
        temporal endpoints." This is a PHYSICAL ASSUMPTION about what
        equilibrium means. The cylinder theorem proves the CONSEQUENCE
        (identical endpoints → full cylinder) but not the PREMISE.

  ❗ B. β = 8πm (inverse Hawking temperature = temporal extent)
        This identifies the partition function parameter β with the
        physical inverse temperature. Comes from general relativity.

  ❗ C. m ~ r_s/ℓ (grid size = Schwarzschild radius in lattice units)
        This identifies the discrete parameter m with the black hole
        mass. Requires choosing a lattice spacing ℓ.

  ════════════════════════════════════════════════════
  FALSIFIABLE PREDICTION
  ════════════════════════════════════════════════════

  The Bekenstein bound S ≤ 2πER, combined with S/(ER) = c₃·2·m⁰ for d=4,
  gives c₃ ≤ π. Once c₃ is computed from the [m]³ transfer matrix,
  this is checkable. If c₃ > π, the d=4 black hole interpretation fails.

  ════════════════════════════════════════════════════
  WHAT THE FRAMEWORK IS (honest summary)
  ════════════════════════════════════════════════════

  A formally verified combinatorial framework that, given three physical
  identifications (A, B, C above), reproduces:
  - Area-law entropy scaling (the exponent, not the coefficient)
  - Hawking temperature scaling
  - Negative specific heat (correct sign from pure arithmetic)
  - Marginal Bekenstein bound at d = 4
  - Four independent criteria selecting d = 4

  It does NOT derive S = A/(4Gℏ) from first principles.
  It does NOT predict measurable quantities without fixing ℓ.
  It DOES make one falsifiable prediction: c₃ ≤ π.
-/

-- This file contains no theorems — it is documentation only.
-- All referenced theorems are in the files listed above.
