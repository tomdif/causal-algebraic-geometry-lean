/-
  SMBridge.lean — Bridge from chamber fermion theory to SM derivation

  This file documents how the chamber/exterior-Möbius theory connects
  to the Standard Model derivation chain in the unified theory repo.

  The connection:

  CHAMBER THEORY (this repo, machine-checked):
    (I - Δ_ch) · ζ_F = I              [ExteriorMobius.lean]
    K_F = ζ_F + ζ_Fᵀ - I              [ChiralStructure.lean]
    K_F = K_Fᵀ                         [ChiralStructure.lean]
    ζ_F upper triangular (right-movers) [ChiralStructure.lean]
    Chamber theorem: spec(K_F) = spec(K|_{H_sgn})  [ChamberTheorem.lean]

  SM DERIVATION (unified theory repo, all proved):
    Chirality (from K/P split)          → N_w ≥ 2     [SMForced.lean]
    Charge determinacy (anomaly cancel) → N_w = 2     [GaugeGroupDerived.lean]
    UV completeness                     → N_c ≤ 4     [MinimalityDerived.lean]
    Integer baryon charge               → N_c ≠ 4     [IntegerCharge.lean]
    RESULT: N_c = 3, N_w = 2           → THE SM       [SMForced.lean]
    Three generations (d=3 + CP)        → N_g = 3      [ThreeGenerations.lean]
    CKM structure (SVD of Yukawa)       → 3θ + 1δ     [MassAndMixing.lean]

  THE BRIDGE:
    The chamber theory provides the CHIRALITY input:
    K_F = ζ_F + ζ_Fᵀ - I is NOT vectorlike (ζ_F ≠ ζ_Fᵀ).
    The triangular decomposition gives left-movers and right-movers.
    This is the K/P split that the SM derivation chain starts from.

  Once chirality is established, the SM derivation follows:
    Chirality → N_w ≥ 2 → (charge determinacy) → N_w = 2
    → (UV + integer charge) → N_c = 3
    → (CP violation + d=3) → N_g = 3
    → (SVD) → CKM structure with 3 angles + 1 phase

  WHAT IS MACHINE-CHECKED IN THIS REPO:
    ✓ (I - Δ_ch) · ζ_F = I
    ✓ K_F symmetric
    ✓ Gell-Mann–Nishijima arithmetic (Y values)

  WHAT IS MACHINE-CHECKED IN THE UNIFIED THEORY REPO:
    ✓ SMForced: N_c = 3, N_w = 2 from 4 constraints
    ✓ AnomalyConstraints: all SM charges uniquely determined
    ✓ ThreeGenerations: N_g = 3 from CP + d=3
    ✓ MassAndMixing: CKM structure from SVD

  WHAT REMAINS OPEN:
    • Formal import of unified theory results into this repo
      (different Mathlib versions, different project structures)
    • The K/P split ↔ chamber chirality identification
      (the conceptual bridge, not yet formalized)
    • Absolute mass values (13 free parameters in Yukawa sector)
-/

-- This file serves as documentation.
-- The actual proofs are in ExteriorMobius.lean, ChiralStructure.lean,
-- and the unified theory repo.
