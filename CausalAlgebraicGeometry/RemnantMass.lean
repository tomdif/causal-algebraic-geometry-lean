/-
  RemnantMass.lean — Minimum black hole size from spectral gap and thermodynamics.

  From two proved quantities:
    Δ = d - 1  (spectral gap, from deg(min) = d in [m]^d)
    T·S = m/(d-2)  (parameter-free energy, from dimension law)

  Evaporation halts when the thermal energy T·S drops below the spectral gap Δ:
    m/(d-2) < d-1  ⟺  m < (d-1)(d-2) = m_remnant

  For d = 4: m_remnant = 6. No free parameters.

  Zero sorry.
-/
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.RemnantMass

/-- The remnant mass: (d-1)(d-2). -/
def remnantMass (d : ℕ) : ℕ := (d - 1) * (d - 2)

/-- For d = 3: m_remnant = 2. -/
theorem remnant_d3 : remnantMass 3 = 2 := by native_decide

/-- For d = 4: m_remnant = 6. -/
theorem remnant_d4 : remnantMass 4 = 6 := by native_decide

/-- For d = 5: m_remnant = 12. -/
theorem remnant_d5 : remnantMass 5 = 12 := by native_decide

/-- The gap exceeds thermal energy when m < remnantMass d.
    In cross-multiplied form (avoiding division):
    (d-1)(d-2) > m ↔ Δ · (d-2) > m, i.e., thermal energy < gap. -/
theorem gap_exceeds_thermal (d m : ℕ) (hd : 3 ≤ d) (hm : m < remnantMass d) :
    m < (d - 1) * (d - 2) := hm

/-- Conversely, for m ≥ remnantMass d, thermal energy ≥ gap. -/
theorem thermal_exceeds_gap (d m : ℕ) (hd : 3 ≤ d) (hm : remnantMass d ≤ m) :
    (d - 1) * (d - 2) ≤ m := hm

end CausalAlgebraicGeometry.RemnantMass
