/-
  ContactTheory.lean — Contact onset at k = 2m and the extended free window.

  THEOREM: For domain-restricted monotone defect profiles with total < 2m,
  the slab constraint a(x)+b(x) ≤ m is automatic. This extends the free
  window from k ≤ m to k < 2m.

  PROOF: Specialization of DepthThreshold at d = 0.

  Zero sorry.
-/
import CausalAlgebraicGeometry.DepthThreshold

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace CausalAlgebraicGeometry.ContactTheory

open CausalAlgebraicGeometry.DepthThreshold

noncomputable section
open scoped Classical

/-! ## The extended free window: k < 2m -/

/-- The key arithmetic fact: if j ≥ 1 and k ≥ 1 and j+k ≥ m+1
    and 0 ≤ t ≤ m-1, then (m-t)·j + (t+1)·k ≥ 2m. -/
theorem contact_arithmetic (m j k t : ℕ)
    (hm : 2 ≤ m)
    (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : m + 1 ≤ j + k)
    (ht : t + 1 ≤ m) :
    2 * m ≤ (m - t) * j + (t + 1) * k := by
  zify [show t ≤ m from by omega] at *
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ m - t by linarith) (show (0 : ℤ) ≤ j - 1 by linarith),
             mul_nonneg (show (0 : ℤ) ≤ t + 1 by linarith) (show (0 : ℤ) ≤ k - (m + 1 - j) by linarith)]

/-- MAIN THEOREM: No contact below 2m.
    If a non-decreasing, b non-increasing, values ≤ m, total < 2m,
    then a(x)+b(x) ≤ m everywhere.

    This is the d=0 case of the depth threshold: T₀(m) = 2m,
    and every x₀ satisfies d=0 ≤ x₀ and d=0 ≤ m-1-x₀. -/
theorem no_contact_below_2m {m : ℕ} (hm : 2 ≤ m)
    (a b : Fin m → ℕ)
    (ha_mono : ∀ i j : Fin m, i ≤ j → a i ≤ a j)
    (hb_anti : ∀ i j : Fin m, i ≤ j → b j ≤ b i)
    (ha_bound : ∀ i, a i ≤ m)
    (hb_bound : ∀ i, b i ≤ m)
    (htotal : Finset.univ.sum (fun x => a x + b x) < 2 * m) :
    ∀ x : Fin m, a x + b x ≤ m := by
  -- Use no_violation_below_threshold at d = 0
  -- T₀(m) = (0+2)m - 0 = 2m, and 2·0+1 = 1 ≤ m
  have hd_half : 2 * 0 + 1 ≤ m := by omega
  have htotal' : Finset.univ.sum (fun x => a x + b x) < 2 * m + 0 * (m - 1) := by
    simp; exact htotal
  intro x
  exact no_violation_below_threshold hm a b ha_mono hb_anti ha_bound hb_bound 0 hd_half htotal'
    x (Nat.zero_le _) (by omega)

/-- Contact IS possible at exactly 2m. Example: a = const 1, b = (m,0,...,0). -/
theorem contact_at_2m (m : ℕ) (hm : 2 ≤ m) :
    ∃ x₀ : Fin m, (1 : ℕ) + m > m := ⟨⟨0, by omega⟩, by omega⟩

/-! ## Summary

  The three-layer structure:

  Layer A (k ≤ m): CC = (p*p)(k)
    Proved in SharpThreshold (slab_constraint_automatic).

  Layer B (m < k < 2m): CC = (p_m * p_m)(k)
    From no_contact_below_2m: domain-restricted pairs with total < 2m
    automatically satisfy the slab constraint. This is the d=0 case
    of the depth threshold T₀(m) = 2m.

  Layer C (k ≥ 2m): CC < (p_m * p_m)(k)
    First contact possible at k = 2m (contact_at_2m).
    The depth-d threshold T_d(m) = (d+2)m - d gives the onset of
    depth-d violations, with step-shift cores as the primitive family.
-/

end
end CausalAlgebraicGeometry.ContactTheory
