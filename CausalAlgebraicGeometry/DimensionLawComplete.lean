/-
  DimensionLawComplete.lean — Explicit all-dimensional bounds for grid-convex sets.

  MAIN THEOREM (dimension_law_explicit): for d ≥ 2,

    2^(m^d / (d*m + 1)) ≤ numConvexDim d m ≤ 16^(m^(d-1)).

  The lower bound takes every subset of a largest rank layer of [m]^d.  A rank
  layer is an antichain, so all of its subsets are order-convex.  The pigeonhole
  principle gives a layer of size at least m^d / (d*m+1).

  The upper bound starts from the proved two-dimensional estimate
  numConvexDim 2 m ≤ choose (2m,m)^2 ≤ 16^m and iterates the slicing inequality
  numConvexDim (d+1) m ≤ numConvexDim d m ^ m.

  Consequently log(numConvexDim d m) = Theta(m^(d-1)) for every fixed d ≥ 2,
  with completely explicit finite-m constants.  Zero sorry.
-/
import CausalAlgebraicGeometry.SlicingBound
import CausalAlgebraicGeometry.DownsetBridge
import Mathlib.Combinatorics.Pigeonhole

namespace CausalAlgebraicGeometry.DimensionLawComplete

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlicingBound
open CausalAlgebraicGeometry.DownsetBridge
open CausalAlgebraicGeometry.TightUpperBound

open scoped Classical
noncomputable section

/-! ## Rank layers and the lower bound -/

/-- The sum of the coordinates of a point in the grid `[m]^d`. -/
def gridRank {d m : ℕ} (p : Fin d → Fin m) : ℕ :=
  Finset.univ.sum fun i => (p i).val

/-- The grid rank, regarded as one of at most `d*m+1` possible values. -/
def gridRankFin (d m : ℕ) (p : Fin d → Fin m) : Fin (d * m + 1) :=
  ⟨gridRank p, by
    have hsum : gridRank p ≤ Finset.univ.sum (fun _ : Fin d => m) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_of_lt (p i).isLt
    calc
      gridRank p ≤ Finset.univ.sum (fun _ : Fin d => m) := hsum
      _ = d * m := by simp
      _ < d * m + 1 := Nat.lt_succ_self _⟩

/-- A level set of the grid-rank map. -/
def rankLayer (d m : ℕ) (r : Fin (d * m + 1)) : Finset (Fin d → Fin m) :=
  Finset.univ.filter fun p => gridRankFin d m p = r

/-- Some rank layer contains at least the average number of grid points. -/
theorem exists_large_rankLayer (d m : ℕ) :
    ∃ r : Fin (d * m + 1),
      m ^ d / (d * m + 1) ≤ (rankLayer d m r).card := by
  have hmul : (d * m + 1) * (m ^ d / (d * m + 1)) ≤ m ^ d :=
    Nat.mul_div_le _ _
  have hcards :
      Fintype.card (Fin (d * m + 1)) * (m ^ d / (d * m + 1)) ≤
        Fintype.card (Fin d → Fin m) := by
    simpa using hmul
  obtain ⟨r, hr⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := gridRankFin d m) hcards
  exact ⟨r, by simpa [rankLayer] using hr⟩

/-- Comparable points of equal grid rank coincide. -/
theorem eq_of_le_of_gridRank_eq {d m : ℕ} {p q : Fin d → Fin m}
    (hpq : p ≤ q) (hrank : gridRank p = gridRank q) : p = q := by
  funext i
  apply Fin.ext
  have hle : (p i).val ≤ (q i).val := Fin.le_def.mp (hpq i)
  apply le_antisymm hle
  by_contra hnot
  have hlt : (p i).val < (q i).val := by omega
  have hsumlt : gridRank p < gridRank q := by
    apply Finset.sum_lt_sum
    · intro j _
      exact Fin.le_def.mp (hpq j)
    · exact ⟨i, Finset.mem_univ i, hlt⟩
  omega

/-- Every subset of a rank layer is order-convex. -/
theorem subset_rankLayer_isConvex {d m : ℕ} {r : Fin (d * m + 1)}
    {S : Finset (Fin d → Fin m)} (hS : S ⊆ rankLayer d m r) :
    IsConvexDim d m S := by
  intro a ha b hb hab c hac hcb
  have har : gridRankFin d m a = r := (Finset.mem_filter.mp (hS ha)).2
  have hbr : gridRankFin d m b = r := (Finset.mem_filter.mp (hS hb)).2
  have hrank : gridRank a = gridRank b :=
    congrArg Fin.val (har.trans hbr.symm)
  have hab_eq : a = b := eq_of_le_of_gridRank_eq hab hrank
  subst b
  have hca : c = a := le_antisymm hcb hac
  simpa [hca] using ha

/-- The powerset of a rank layer injects into the family of convex subsets. -/
theorem rankLayer_powerset_le_numConvexDim (d m : ℕ) (r : Fin (d * m + 1)) :
    2 ^ (rankLayer d m r).card ≤ numConvexDim d m := by
  rw [← Finset.card_powerset]
  unfold numConvexDim
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_powerset] at hS
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, subset_rankLayer_isConvex hS⟩

/-- Explicit rank-layer lower bound, valid in every dimension. -/
theorem numConvexDim_rank_lower (d m : ℕ) :
    2 ^ (m ^ d / (d * m + 1)) ≤ numConvexDim d m := by
  obtain ⟨r, hr⟩ := exists_large_rankLayer d m
  exact (Nat.pow_le_pow_right (by norm_num) hr).trans
    (rankLayer_powerset_le_numConvexDim d m r)

/-! ## Iterated slicing and the upper bound -/

/-- A convenient exponential form of the existing sharp two-dimensional bound. -/
theorem numConvexDim_two_le_sixteen_pow (m : ℕ) :
    numConvexDim 2 m ≤ 16 ^ m := by
  calc
    numConvexDim 2 m ≤ Nat.choose (2 * m) m ^ 2 := numConvexDim_two_le_choose_sq m
    _ ≤ (4 ^ m) ^ 2 := Nat.pow_le_pow_left (choose_central_le_four_pow m) 2
    _ = 16 ^ m := by
      rw [← pow_mul, show m * 2 = 2 * m by omega,
        show (4 : ℕ) ^ (2 * m) = (4 ^ 2) ^ m by rw [pow_mul]]
      norm_num

/-- The upper bound indexed by the number of slicing steps above dimension two. -/
theorem numConvexDim_upper_indexed (k m : ℕ) :
    numConvexDim (k + 2) m ≤ 16 ^ (m ^ (k + 1)) := by
  induction k with
  | zero =>
      simpa using numConvexDim_two_le_sixteen_pow m
  | succ k ih =>
      calc
        numConvexDim (k + 1 + 2) m
            = numConvexDim ((k + 2) + 1) m := by congr 2
        _ ≤ numConvexDim (k + 2) m ^ m := numConvexDim_slicing (k + 2) m
        _ ≤ (16 ^ (m ^ (k + 1))) ^ m := Nat.pow_le_pow_left ih m
        _ = 16 ^ (m ^ (k + 1 + 1)) := by
          rw [← pow_mul]
          congr 1

/-- Explicit slicing upper bound, valid in every dimension at least two. -/
theorem numConvexDim_dimension_upper (d m : ℕ) (hd : 2 ≤ d) :
    numConvexDim d m ≤ 16 ^ (m ^ (d - 1)) := by
  have h := numConvexDim_upper_indexed (d - 2) m
  have hdim : d - 2 + 2 = d := Nat.sub_add_cancel hd
  have hexp : d - 2 + 1 = d - 1 := by omega
  simpa only [hdim, hexp] using h

/-! ## The complete dimension law -/

/-- **Explicit dimension law.** These finite-size inequalities imply
`log (numConvexDim d m) = Theta(m^(d-1))` for each fixed `d ≥ 2`. -/
theorem dimension_law_explicit (d m : ℕ) (hd : 2 ≤ d) :
    2 ^ (m ^ d / (d * m + 1)) ≤ numConvexDim d m ∧
      numConvexDim d m ≤ 16 ^ (m ^ (d - 1)) :=
  ⟨numConvexDim_rank_lower d m, numConvexDim_dimension_upper d m hd⟩

end
end CausalAlgebraicGeometry.DimensionLawComplete
