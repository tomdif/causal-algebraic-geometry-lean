/-
  Factorization of the 3D gap observable

  Proves γ₃ = f_bulk × γ_slice via the law of total expectation:
    sliceWidth(j) = occupiedFrac(j) × conditionalSliceWidth(j)

  The gap γ₃ = (1/m) Σ_j sliceWidth(j) decomposes into occupied fraction
  (bulk factor) times conditional width (slice factor) at each position.
-/
import CausalAlgebraicGeometry.FixedPoint3D
import Mathlib.Tactic

namespace Factorization3D

open FixedPoint3D Finset

/-- Reflection of a Fin m index: j ↦ m-1-j. -/
def reflectFin (m : ℕ) (hm : 0 < m) (j : Fin m) : Fin m :=
  ⟨m - 1 - j, by omega⟩

/-- Reflection is an involution. -/
@[simp] theorem reflectFin_invol (m : ℕ) (hm : 0 < m) (j : Fin m) :
    reflectFin m hm (reflectFin m hm j) = j := by
  simp only [reflectFin]; ext; simp only; omega

section Main

variable {m : ℕ} (hm : 0 < m)
variable (S : Finset (State3D m))
variable (ψ : State3D m → ℝ)
variable (hψ_pos : ∀ s ∈ S, 0 < ψ s)

/-- The conditional slice width at position j:
    E[width(j) | width(j) > 0] under ψ² measure, normalized by m. -/
noncomputable def conditionalSliceWidth (j : Fin m) : ℝ :=
  (S.filter (fun s => 0 < s.width j)).sum (fun s => ψ s ^ 2 * ↑(s.width j)) /
  ((S.filter (fun s => 0 < s.width j)).sum (fun s => ψ s ^ 2) * ↑m)

/-- Terms with width = 0 contribute zero to the weighted sum. -/
theorem zero_width_vanishes (j : Fin m) (s : State3D m)
    (hs : ¬(0 < s.width j)) :
    ψ s ^ 2 * ↑(s.width j) = 0 := by
  have hw : s.width j = 0 := by omega
  simp [hw]

/-- The weighted width sum restricted to positive-width states equals
    the unrestricted sum, since zero-width states contribute zero. -/
theorem sum_eq_filter_sum (j : Fin m) :
    S.sum (fun s => ψ s ^ 2 * (s.width j : ℝ)) =
    (S.filter (fun s => 0 < s.width j)).sum (fun s => ψ s ^ 2 * (s.width j : ℝ)) := by
  symm
  apply Finset.sum_filter_of_ne
  intro s _ hne
  by_contra h
  push_neg at h
  have hw : s.width j = 0 := by omega
  exact hne (by simp [hw])

/-- Law of total expectation:
    sliceWidth(j) = occupiedFrac(j) × conditionalSliceWidth(j)

    Proof sketch: sliceWidth(j) = Σ_s ψ²·w(j) / (Z·m)
         = Σ_{s:w>0} ψ²·w(j) / (Z·m)          [zero terms vanish]
         = (Σ_{s:w>0} ψ² / Z) × (Σ_{s:w>0} ψ²·w(j) / (Σ_{s:w>0} ψ² · m))
         = occupiedFrac(j) × conditionalSliceWidth(j) -/
theorem total_expectation (j : Fin m)
    (hZ : S.sum (fun s => ψ s ^ 2) ≠ 0)
    (hZj : (S.filter (fun s => 0 < s.width j)).sum (fun s => ψ s ^ 2) ≠ 0) :
    sliceWidth S ψ j = occupiedFrac S ψ j * conditionalSliceWidth S ψ j := by
  unfold sliceWidth occupiedFrac conditionalSliceWidth
  rw [sum_eq_filter_sum S ψ j]
  -- LHS = F_wj / (Z * m), RHS = (F_j / Z) * (F_wj / (F_j * m)) = F_wj / (Z * m)
  field_simp

/-- The gap decomposes as an average of slice widths.
    gap = (1/m) Σ_j sliceWidth(j)

    This follows from weighted_area_decomp (sum swap). -/
theorem gap_eq_avg_sliceWidth
    (hZ : S.sum (fun s => ψ s ^ 2) ≠ 0) :
    gap S ψ =
    (Finset.univ.sum (fun j : Fin m => sliceWidth S ψ j)) / ↑m := by
  unfold gap sliceWidth
  rw [weighted_area_decomp S (fun s => ψ s ^ 2)]
  -- The algebra: (Σ x_j) / (Z * m²) = (Σ (x_j / (Z * m))) / m
  -- Both sides equal (Σ x_j) / (Z * m * m)
  simp only [Finset.sum_div, div_div, sq, mul_assoc]

/-- Combined factorization: under the hypotheses of total_expectation at each j,
    gap = (1/m) Σ_j occupiedFrac(j) × conditionalSliceWidth(j). -/
theorem gap_factored
    (hZ : S.sum (fun s => ψ s ^ 2) ≠ 0)
    (hZj : ∀ j : Fin m,
      (S.filter (fun s => 0 < s.width j)).sum (fun s => ψ s ^ 2) ≠ 0) :
    gap S ψ =
    (Finset.univ.sum (fun j : Fin m =>
      occupiedFrac S ψ j * conditionalSliceWidth S ψ j)) / ↑m := by
  rw [gap_eq_avg_sliceWidth S ψ hZ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact total_expectation S ψ j hZ (hZj j)

/-- Slice width is symmetric under j ↦ m-1-j, given that the eigenvector-weighted
    width sums respect the reflection symmetry of the transfer operator. -/
theorem sliceWidth_symmetric
    (hrefl : ∀ j : Fin m,
      S.sum (fun s => ψ s ^ 2 * ↑(s.width j)) =
      S.sum (fun s => ψ s ^ 2 * ↑(s.width (reflectFin m hm j))))
    (j : Fin m) :
    sliceWidth S ψ j = sliceWidth S ψ (reflectFin m hm j) := by
  unfold sliceWidth
  rw [hrefl j]

/-- Occupied fraction is symmetric under j ↦ m-1-j, given reflection symmetry
    of the filtered ψ² sums. -/
theorem occupiedFrac_symmetric
    (hrefl : ∀ j : Fin m,
      (S.filter (fun s => 0 < s.width j)).sum (fun s => ψ s ^ 2) =
      (S.filter (fun s => 0 < s.width (reflectFin m hm j))).sum (fun s => ψ s ^ 2))
    (j : Fin m) :
    occupiedFrac S ψ j = occupiedFrac S ψ (reflectFin m hm j) := by
  unfold occupiedFrac
  rw [hrefl j]

end Main

end Factorization3D
