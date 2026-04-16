/-
  PartitionDimensionBridge.lean — Two independent roads to d = 3

  THE RESULT:
  The equation 2d + 3 = d² has unique natural number solution d = 3.
  This is also the spatial dimension selected by the Lovelock + graviton
  counting argument.

  In D = d+1 spacetime dimensions, a massless spin-2 particle has
  D(D-3)/2 = (d+1)(d-2)/2 polarizations. For d = 3 (D = 4): this is 2.
  For d ≥ 4: polarization count > 2 (extra scalar modes).

  Two completely independent equations both select d = 3:
  (1) Partition identity: 2d + 3 = d²
  (2) Graviton count: (d+1)(d-2)/2 = 2 (for d ≥ 2)

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.PartitionDimensionBridge

/-! ## Road 1: The partition identity 2d + 3 = d² -/

/-- The equation 2d + 3 = d * d has unique natural number solution d = 3. -/
theorem partition_selects_d3 (d : ℕ) : 2 * d + 3 = d * d ↔ d = 3 := by
  constructor
  · intro h
    have hd : d ≤ 3 := by nlinarith
    have hd2 : d ≥ 3 := by nlinarith
    omega
  · rintro rfl; norm_num

/-- Direct verification: 2·3 + 3 = 9 = 3·3. -/
theorem partition_d3_check : 2 * 3 + 3 = 3 * 3 := by norm_num

/-! ## Road 2: Graviton polarization count -/

/-- In D = d+1 spacetime dimensions, a massless graviton has
    D(D-3)/2 = (d+1)(d-2)/2 independent polarizations. -/
def gravitonCount (d : ℕ) : ℕ := (d + 1) * (d - 2) / 2

/-- For d ≥ 5, the graviton count exceeds 2. -/
theorem graviton_count_large (d : ℕ) (hd : d ≥ 5) :
    gravitonCount d ≥ 6 := by
  unfold gravitonCount
  have h1 : d - 2 ≥ 3 := by omega
  have h2 : (d + 1) * (d - 2) ≥ 6 * 3 := Nat.mul_le_mul (by omega) h1
  omega

/-- (d+1)(d-2)/2 = 2 implies d = 3 (for d ≥ 2). -/
theorem graviton_forward (d : ℕ) (hd : d ≥ 2) (h : gravitonCount d = 2) :
    d = 3 := by
  unfold gravitonCount at h
  -- d ≥ 5 gives count ≥ 6, contradiction
  have hd4 : d ≤ 4 := by
    by_contra hlt
    push_neg at hlt
    have hbig := graviton_count_large d (by omega)
    unfold gravitonCount at hbig
    omega
  -- d ∈ {2, 3, 4}
  interval_cases d <;> omega

/-- (d+1)(d-2)/2 = 2 iff d = 3, for d ≥ 2. -/
theorem graviton_selects_d3 (d : ℕ) (hd : d ≥ 2) :
    gravitonCount d = 2 ↔ d = 3 :=
  ⟨graviton_forward d hd, fun h => by subst h; rfl⟩

/-- Direct verification: gravitonCount 3 = 4 * 1 / 2 = 2. -/
theorem graviton_d3_check : gravitonCount 3 = 2 := by rfl

/-! ## The coincidence: two independent roads -/

/-- **TWO INDEPENDENT ROADS TO d = 3.**

    Road 1 (partition): 2d + 3 = d·d ↔ d = 3
    Road 2 (graviton): (d+1)(d-2)/2 = 2 ↔ d = 3 (for d ≥ 2)

    These are algebraically independent equations that happen to
    have the same unique solution. -/
theorem two_independent_roads_to_d3 :
    (∀ d : ℕ, 2 * d + 3 = d * d ↔ d = 3) ∧
    (∀ d : ℕ, d ≥ 2 → (gravitonCount d = 2 ↔ d = 3)) :=
  ⟨partition_selects_d3, graviton_selects_d3⟩

/-- The two equations are genuinely different: they disagree at d = 4. -/
theorem equations_differ_at_d4 :
    (2 * 4 + 3 ≠ 4 * 4) ∧ (gravitonCount 4 ≠ 2) := by
  unfold gravitonCount
  constructor <;> norm_num

end CausalAlgebraicGeometry.PartitionDimensionBridge
