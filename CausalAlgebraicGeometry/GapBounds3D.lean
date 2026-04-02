/-
  GapBounds3D: Rigorous bounds on the spectral gap observable γ₃

  The gap γ(m) = (Σ_s ψ(s)² area(s)) / (Σ_s ψ(s)² × m²) satisfies:
    0 < γ(m) ≤ 1

  Lower bound: By Perron-Frobenius, ψ > 0 on all states, and every state
  has area ≥ 1 (by the vol_pos condition), so the numerator > 0.

  Upper bound: Every state has area ≤ m², so γ ≤ 1.

  We also prove that the weighted average of any bounded observable
  lies within the observable's range.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic
import Mathlib.Order.Basic

namespace GapBounds3D

open Finset

/-! ### General weighted average bounds -/

/-- A weighted average of values in [0, B] lies in [0, B],
    given positive weights summing to a positive total. -/
theorem weighted_avg_le_bound {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι → ℝ) (f : ι → ℝ) (B : ℝ)
    (hB : 0 < B)
    (hw_pos : ∀ i ∈ S, 0 < w i)
    (hS : S.Nonempty)
    (hf_le : ∀ i ∈ S, f i ≤ B)
    (_hf_nn : ∀ i ∈ S, 0 ≤ f i) :
    S.sum (fun i => w i * f i) / (S.sum w * B) ≤ 1 := by
  have hW : 0 < S.sum w := by
    obtain ⟨j, hjS⟩ := hS
    exact Finset.sum_pos (fun i hi => hw_pos i hi) ⟨j, hjS⟩
  rw [div_le_one (mul_pos hW hB)]
  calc S.sum (fun i => w i * f i)
      ≤ S.sum (fun i => w i * B) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hf_le i hi) (le_of_lt (hw_pos i hi))
    _ = S.sum w * B := by rw [← Finset.sum_mul]

/-- A weighted average is nonneg when weights and values are nonneg. -/
theorem weighted_avg_nonneg {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι → ℝ) (f : ι → ℝ)
    (hw_nn : ∀ i ∈ S, 0 ≤ w i)
    (hf_nn : ∀ i ∈ S, 0 ≤ f i) :
    0 ≤ S.sum (fun i => w i * f i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw_nn i hi) (hf_nn i hi)

/-! ### Gap bounds for the 3D model -/

/-- The gap numerator is positive when:
    - all weights are positive
    - there exists a state with positive value -/
theorem gap_numerator_pos {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι → ℝ) (f : ι → ℝ)
    (hw_pos : ∀ i ∈ S, 0 < w i)
    (hf_nn : ∀ i ∈ S, 0 ≤ f i)
    (hf_pos : ∃ i ∈ S, 0 < f i) :
    0 < S.sum (fun i => w i * f i) := by
  obtain ⟨j, hjS, hjf⟩ := hf_pos
  calc 0 < w j * f j := mul_pos (hw_pos j hjS) hjf
    _ ≤ S.sum (fun i => w i * f i) := by
        apply Finset.single_le_sum (f := fun i => w i * f i)
        · intro i hi; exact mul_nonneg (le_of_lt (hw_pos i hi)) (hf_nn i hi)
        · exact hjS

/-- The weight sum is positive when all weights are positive and S is nonempty. -/
theorem weight_sum_pos {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι → ℝ)
    (hw_pos : ∀ i ∈ S, 0 < w i)
    (hS : S.Nonempty) :
    0 < S.sum w := by
  obtain ⟨j, hjS⟩ := hS
  exact Finset.sum_pos (fun i hi => hw_pos i hi) ⟨j, hjS⟩

/-- Gap is strictly positive: if ψ > 0 and some state has positive area,
    then γ > 0. -/
theorem gap_positive {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (ψ : ι → ℝ) (area : ι → ℝ) (m : ℝ)
    (hm : 0 < m)
    (hS : S.Nonempty)
    (hψ_pos : ∀ i ∈ S, 0 < ψ i)
    (harea_nn : ∀ i ∈ S, 0 ≤ area i)
    (harea_pos : ∃ i ∈ S, 0 < area i) :
    0 < S.sum (fun i => ψ i ^ 2 * area i) /
        (S.sum (fun i => ψ i ^ 2) * m ^ 2) := by
  apply div_pos
  · exact gap_numerator_pos S (fun i => ψ i ^ 2) area
      (fun i hi => pow_pos (hψ_pos i hi) 2) harea_nn harea_pos
  · apply mul_pos
    · exact weight_sum_pos S (fun i => ψ i ^ 2)
        (fun i hi => pow_pos (hψ_pos i hi) 2) hS
    · exact pow_pos hm 2

/-- Gap is at most 1: if area ≤ m² for all states, then γ ≤ 1. -/
theorem gap_bounded {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (ψ : ι → ℝ) (area : ι → ℝ) (m : ℝ)
    (hm : 0 < m)
    (hS : S.Nonempty)
    (hψ_pos : ∀ i ∈ S, 0 < ψ i)
    (harea_nn : ∀ i ∈ S, 0 ≤ area i)
    (harea_le : ∀ i ∈ S, area i ≤ m ^ 2) :
    S.sum (fun i => ψ i ^ 2 * area i) /
        (S.sum (fun i => ψ i ^ 2) * m ^ 2) ≤ 1 := by
  exact weighted_avg_le_bound S (fun i => ψ i ^ 2) area (m ^ 2)
    (pow_pos hm 2) (fun i hi => pow_pos (hψ_pos i hi) 2) hS harea_le harea_nn

/-- Combined: gap lies in (0, 1]. -/
theorem gap_in_unit_interval {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (ψ : ι → ℝ) (area : ι → ℝ) (m : ℝ)
    (hm : 0 < m)
    (hS : S.Nonempty)
    (hψ_pos : ∀ i ∈ S, 0 < ψ i)
    (harea_nn : ∀ i ∈ S, 0 ≤ area i)
    (harea_pos : ∃ i ∈ S, 0 < area i)
    (harea_le : ∀ i ∈ S, area i ≤ m ^ 2) :
    0 < S.sum (fun i => ψ i ^ 2 * area i) /
        (S.sum (fun i => ψ i ^ 2) * m ^ 2) ∧
    S.sum (fun i => ψ i ^ 2 * area i) /
        (S.sum (fun i => ψ i ^ 2) * m ^ 2) ≤ 1 :=
  ⟨gap_positive S ψ area m hm hS hψ_pos harea_nn harea_pos,
   gap_bounded S ψ area m hm hS hψ_pos harea_nn harea_le⟩

end GapBounds3D
