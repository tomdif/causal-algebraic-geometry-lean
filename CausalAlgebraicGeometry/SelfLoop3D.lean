/-
  Self-Loop Identity for the d=3 Width Chain (Theorem B)

  2 × |{(a',b') ∈ [0..b+1]×[0..b] : b' < a'}| = (b+2)(b+1)
  i.e., P(w'=0 | w=0) = 1/2.

  Proved for b = 0,...,9 by native_decide (covering m up to 11).
  The general statement follows from the triangular number identity
  Σ_{k=1}^{n} k = n(n+1)/2.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace SelfLoop3D

private abbrev selfLoopCount (b : ℕ) :=
  ((Finset.range (b + 2)) ×ˢ (Finset.range (b + 1))).filter
    (fun p : ℕ × ℕ => p.2 < p.1) |>.card

theorem self_loop_half_0 : 2 * selfLoopCount 0 = 2 * 1 := by native_decide
theorem self_loop_half_1 : 2 * selfLoopCount 1 = 3 * 2 := by native_decide
theorem self_loop_half_2 : 2 * selfLoopCount 2 = 4 * 3 := by native_decide
theorem self_loop_half_3 : 2 * selfLoopCount 3 = 5 * 4 := by native_decide
theorem self_loop_half_4 : 2 * selfLoopCount 4 = 6 * 5 := by native_decide
theorem self_loop_half_5 : 2 * selfLoopCount 5 = 7 * 6 := by native_decide
theorem self_loop_half_6 : 2 * selfLoopCount 6 = 8 * 7 := by native_decide
theorem self_loop_half_7 : 2 * selfLoopCount 7 = 9 * 8 := by native_decide
theorem self_loop_half_8 : 2 * selfLoopCount 8 = 10 * 9 := by native_decide
theorem self_loop_half_9 : 2 * selfLoopCount 9 = 11 * 10 := by native_decide

end SelfLoop3D
