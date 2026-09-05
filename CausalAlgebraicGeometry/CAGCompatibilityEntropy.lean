/-
# Compatibility entropy: boundary trimming versus ordering

For base dimension d, D counts antitone profiles of height at most m,
H counts those of height strictly below m, and Q counts strict pairs.
The existing strict-to-weak equivalence identifies Q with ordered pairs
in the H-profile space. We prove

  0 <= 2 log(D/H) <= 2 log(downsetCountDim d m),
  0 <= log(H^2/Q),
  2 log D - log Q = 2 log(D/H) + log(H^2/Q).

The first cost has a codimension-two upper bound by the dimension law.
No such sharp bound is proved here for the second cost. The proposed
four-dimensional area law is stated as a Prop, not an axiom or theorem.
These are finite counting results, not gravitational field equations.
-/
import CausalAlgebraicGeometry.CAGMultidimensionalEntropy

namespace CausalAlgebraicGeometry.CAGCompatibilityEntropy

open C3BarrierLowerBound C3ShiftCompression C3MultiscaleCompression
open C3OrderIdealReduction FullSupportLowerBound DimensionLaw
open CAGMultidimensionalEntropy SlabBijection
open Real Filter Topology

noncomputable section
open scoped Classical

/-- The original base box, with the height ceiling lowered by one unit. -/
def TrimmedProfile (d m : ℕ) :=
  { f : (Fin d → Fin m) → Fin m // Antitone f }

instance (d m : ℕ) : Fintype (TrimmedProfile d m) := by
  unfold TrimmedProfile
  infer_instance

def trimmedCount (d m : ℕ) : ℕ := Fintype.card (TrimmedProfile d m)

theorem trimmedCount_pos (d m : ℕ) (hm : 0 < m) : 0 < trimmedCount d m := by
  exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => ⟨0, hm⟩, fun _ _ _ => le_rfl⟩⟩

/-- Forget the weak ordering after removing the strict unit gap. -/
def weakPairToProduct {d m : ℕ} (p : WeakOrderedPair d m) :
    TrimmedProfile d m × TrimmedProfile d m :=
  (⟨p.lower, p.lower_antitone⟩, ⟨p.upper, p.upper_antitone⟩)

theorem weakPairToProduct_injective {d m : ℕ} :
    Function.Injective (weakPairToProduct (d := d) (m := m)) := by
  intro p q h
  exact WeakOrderedPair.ext
    (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)

theorem fullSupportCount_le_trimmed_square (d m : ℕ) :
    fullSupportCount d m ≤ trimmedCount d m ^ 2 := by
  change Fintype.card (FullSupportPair d m) ≤ Fintype.card (TrimmedProfile d m) ^ 2
  rw [Fintype.card_congr (fullSupportPairEquivWeak d m), pow_two,
    ← Fintype.card_prod]
  exact Fintype.card_le_of_injective weakPairToProduct weakPairToProduct_injective

def includeTrimmed {d m : ℕ} (p : TrimmedProfile d m) : AntitoneProfile d m where
  toFun f := ⟨(p.val f).val, Nat.lt_succ_of_lt (p.val f).isLt⟩
  antitone := by
    intro f g hfg
    exact Fin.mk_le_mk.mpr (Fin.le_def.mp (p.property hfg))

theorem includeTrimmed_injective {d m : ℕ} :
    Function.Injective (includeTrimmed (d := d) (m := m)) := by
  intro p q h
  apply Subtype.ext
  funext f
  apply Fin.ext
  exact congrArg (fun z => (z.toFun f).val) h

theorem trimmedCount_le_downset (d m : ℕ) :
    trimmedCount d m ≤ downsetCountDim (d + 1) m := by
  rw [← card_antitoneProfile_eq_downsetCount]
  exact Fintype.card_le_of_injective includeTrimmed includeTrimmed_injective

/-- Lower every nonzero height by one, remembering the occupied base set
separately. The discarded data is a single lower-dimensional downset. -/
def trimHeight {d m : ℕ} (hm : 0 < m) (p : AntitoneProfile d m) :
    TrimmedProfile d m :=
  ⟨fun f => ⟨(p.toFun f).val - 1, by have := (p.toFun f).isLt; omega⟩,
    by
      intro f g hfg
      apply Fin.mk_le_mk.mpr
      have := Fin.le_def.mp (p.antitone hfg)
      omega⟩

theorem trimHeight_residual_injective {d m : ℕ} (hm : 0 < m) :
    Function.Injective
      (fun p : AntitoneProfile d m => (trimHeight hm p, lowerResidual 1 p)) := by
  intro p q h
  apply AntitoneProfile.ext
  funext f
  apply Fin.ext
  have ht := congrArg (fun z => (z.1.val f).val) h
  have hr := congrArg (fun z => (z.2.toFun f).val) h
  simp only [trimHeight, lowerResidual] at ht hr
  omega

/-- A one-height-layer change costs at most one base-downset choice. -/
theorem downset_le_trimmed_mul_base (d m : ℕ) (hm : 0 < m) :
    downsetCountDim (d + 1) m ≤ trimmedCount d m * downsetCountDim d m := by
  rw [← card_antitoneProfile_eq_downsetCount]
  calc
    Fintype.card (AntitoneProfile d m) ≤
        Fintype.card (TrimmedProfile d m × ThinProfile d m 1) :=
      Fintype.card_le_of_injective _ (trimHeight_residual_injective hm)
    _ = trimmedCount d m * Fintype.card (ThinProfile d m 1) := Fintype.card_prod _ _
    _ ≤ trimmedCount d m * downsetCountDim d m := by
      apply Nat.mul_le_mul_left
      simpa using thinProfile_card_le_downset_pow d m 1

def compatibilityProbability (d m : ℕ) : ℝ :=
  (fullSupportCount d m : ℝ) / (downsetCountDim (d + 1) m : ℝ) ^ 2

def compatibilityDeficit (d m : ℕ) : ℝ :=
  2 * Real.log (downsetCountDim (d + 1) m : ℝ) - Real.log (fullSupportCount d m : ℝ)

def heightTrimmingCost (d m : ℕ) : ℝ :=
  2 * (Real.log (downsetCountDim (d + 1) m : ℝ) - Real.log (trimmedCount d m : ℝ))

def weakOrderingCost (d m : ℕ) : ℝ :=
  2 * Real.log (trimmedCount d m : ℝ) - Real.log (fullSupportCount d m : ℝ)

theorem downsetCount_pos_of_side_pos (d m : ℕ) (hm : 0 < m) :
    0 < downsetCountDim (d + 1) m :=
  lt_of_lt_of_le (trimmedCount_pos d m hm) (trimmedCount_le_downset d m)

/-- A genuine probability under two independent uniform profile choices. -/
theorem compatibilityProbability_bounds (d m : ℕ) (hm : 0 < m) :
    0 < compatibilityProbability d m ∧ compatibilityProbability d m ≤ 1 := by
  have hD : (0 : ℝ) < (downsetCountDim (d + 1) m : ℝ) := by
    exact_mod_cast downsetCount_pos_of_side_pos d m hm
  have hQ : (0 : ℝ) < (fullSupportCount d m : ℝ) := by
    exact_mod_cast fullSupportCount_pos d m hm
  refine ⟨div_pos hQ (sq_pos_of_pos hD), (div_le_one (sq_pos_of_pos hD)).mpr ?_⟩
  exact_mod_cast fullSupportCount_le_downset_square d m

/-- Compatibility surprisal, not automatically Shannon mutual information. -/
theorem compatibilityDeficit_eq_neg_log_probability (d m : ℕ) (hm : 0 < m) :
    compatibilityDeficit d m = -Real.log (compatibilityProbability d m) := by
  have hD : (downsetCountDim (d + 1) m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (downsetCount_pos_of_side_pos d m hm)
  have hQ : (fullSupportCount d m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fullSupportCount_pos d m hm)
  simp only [compatibilityDeficit, compatibilityProbability,
    Real.log_div hQ (pow_ne_zero 2 hD), Real.log_pow]
  ring

theorem heightTrimmingCost_bounds (d m : ℕ) (hm : 0 < m) :
    0 ≤ heightTrimmingCost d m ∧
      heightTrimmingCost d m ≤ 2 * Real.log (downsetCountDim d m : ℝ) := by
  have hH : (0 : ℝ) < (trimmedCount d m : ℝ) := by
    exact_mod_cast trimmedCount_pos d m hm
  have hD : (0 : ℝ) < (downsetCountDim (d + 1) m : ℝ) := by
    exact_mod_cast downsetCount_pos_of_side_pos d m hm
  have hHD : (trimmedCount d m : ℝ) ≤ (downsetCountDim (d + 1) m : ℝ) := by
    exact_mod_cast trimmedCount_le_downset d m
  have hprod : (downsetCountDim (d + 1) m : ℝ) ≤
      (trimmedCount d m : ℝ) * (downsetCountDim d m : ℝ) := by
    exact_mod_cast downset_le_trimmed_mul_base d m hm
  have hB : (0 : ℝ) < (downsetCountDim d m : ℝ) := by nlinarith
  have hlo := Real.log_le_log hH hHD
  have hhi := Real.log_le_log hD hprod
  rw [Real.log_mul (ne_of_gt hH) (ne_of_gt hB)] at hhi
  unfold heightTrimmingCost
  constructor <;> linarith

theorem weakOrderingCost_nonneg (d m : ℕ) (hm : 0 < m) :
    0 ≤ weakOrderingCost d m := by
  have hQ : (0 : ℝ) < (fullSupportCount d m : ℝ) := by
    exact_mod_cast fullSupportCount_pos d m hm
  have h := Real.log_le_log hQ
    (show (fullSupportCount d m : ℝ) ≤ (trimmedCount d m : ℝ) ^ 2 by
      exact_mod_cast fullSupportCount_le_trimmed_square d m)
  rw [Real.log_pow] at h
  unfold weakOrderingCost
  norm_num at h
  linarith

/-- Both summands are nonnegative: the decomposition is not cancellation
between a large positive and a large negative term. -/
theorem compatibility_entropy_decomposition (d m : ℕ) (hm : 0 < m) :
    0 ≤ heightTrimmingCost d m ∧ 0 ≤ weakOrderingCost d m ∧
      compatibilityDeficit d m = heightTrimmingCost d m + weakOrderingCost d m := by
  refine ⟨(heightTrimmingCost_bounds d m hm).1, weakOrderingCost_nonneg d m hm, ?_⟩
  unfold compatibilityDeficit heightTrimmingCost weakOrderingCost
  ring

/-- The independent-choice success probability factors into the probability
of fitting the reduced height ranges and the conditional weak-order event. -/
theorem compatibilityProbability_factorization (d m : ℕ) (hm : 0 < m) :
    compatibilityProbability d m =
      ((trimmedCount d m : ℝ) / (downsetCountDim (d + 1) m : ℝ)) ^ 2 *
        ((fullSupportCount d m : ℝ) / (trimmedCount d m : ℝ) ^ 2) := by
  have hH : (trimmedCount d m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (trimmedCount_pos d m hm)
  unfold compatibilityProbability
  field_simp

/-- The height-ceiling artifact alone is bounded at codimension-two scale.
For four ambient dimensions, this is `2 * m^2 * log 16`. -/
theorem heightTrimmingCost_area_upper (r m : ℕ) (hm : 0 < m) :
    heightTrimmingCost (r + 2) m ≤ 2 * (m : ℝ) ^ (r + 1) * Real.log 16 := by
  have hB : (0 : ℝ) < (downsetCountDim (r + 2) m : ℝ) := by
    exact_mod_cast downsetCount_pos_of_side_pos (r + 1) m hm
  have hlog := Real.log_le_log hB
    (show (downsetCountDim (r + 2) m : ℝ) ≤ (16 : ℝ) ^ (m ^ (r + 1)) by
      exact_mod_cast (downsetCountDim_le_numConvexDim (r + 2) m).trans
        (DimensionLawComplete.numConvexDim_upper_indexed r m))
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have h := (heightTrimmingCost_bounds (r + 2) m hm).2
  nlinarith

/-- A finite uniform area upper bound. This does not assert convergence of
the area-normalized quantity or a nonzero limiting coefficient. -/
def AreaUpperBoundFour (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → f m ≤ C * (m : ℝ) ^ 2

/-- The area-upper-bound problem is exactly reduced to weak ordering:
the cost of the strict one-unit gap has already been controlled. Neither
side of this equivalence is asserted unconditionally. -/
theorem area_upper_bound_iff_weak_ordering :
    AreaUpperBoundFour (compatibilityDeficit 3) ↔
      AreaUpperBoundFour (weakOrderingCost 3) := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun m hm => ?_⟩
    obtain ⟨ht, _, heq⟩ := compatibility_entropy_decomposition 3 m hm
    have h := hbound m hm
    linarith
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C + 2 * Real.log 16, ?_, fun m hm => ?_⟩
    · exact add_nonneg hC (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
    · have ht := heightTrimmingCost_area_upper 1 m hm
      have hw := hbound m hm
      have heq := (compatibility_entropy_decomposition 3 m hm).2.2
      norm_num at ht
      nlinarith

/-- Explicitly unproved target, not a physical horizon identification.
The parameter 3 here is BASE dimension, so the ambient box is four-dimensional. -/
def CompatibilityAreaLawFour : Prop :=
  ∃ σ : ℝ, 0 < σ ∧
    Tendsto (fun m : ℕ => compatibilityDeficit 3 m / (m : ℝ) ^ 2) atTop (𝓝 σ)

end
end CausalAlgebraicGeometry.CAGCompatibilityEntropy
