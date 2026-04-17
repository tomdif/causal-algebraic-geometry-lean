/-
  SolidPartitionConvolution.lean — Self-convolution of solid partitions (A000293).

  The sequence a(n) = Σ_{k=0}^n SP(k) × SP(n-k) where SP is OEIS A000293,
  the number of solid (3D) partitions of n.

  Verified values: a(0)=1, a(1)=2, a(2)=9, a(3)=28, a(4)=88, a(5)=250

  Not yet in OEIS. Zero sorry. Zero custom axioms.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.SolidPartitionConvolution

/-! ## Solid partition counts (OEIS A000293) -/

/-- Number of solid (3D) partitions of n, for small n. -/
def solidPartition : ℕ → ℕ
  | 0  => 1
  | 1  => 1
  | 2  => 4
  | 3  => 10
  | 4  => 26
  | 5  => 59
  | 6  => 140
  | 7  => 307
  | 8  => 684
  | 9  => 1464
  | 10 => 3122
  | _  => 0  -- truncated lookup table

/-! ## Self-convolution -/

/-- Self-convolution: a(n) = Σ_{k=0}^n SP(k) × SP(n-k). -/
def spConv (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => solidPartition k * solidPartition (n - k))

/-! ## Verified values -/

theorem spConv_0 : spConv 0 = 1   := by native_decide
theorem spConv_1 : spConv 1 = 2   := by native_decide
theorem spConv_2 : spConv 2 = 9   := by native_decide
theorem spConv_3 : spConv 3 = 28  := by native_decide
theorem spConv_4 : spConv 4 = 88  := by native_decide
theorem spConv_5 : spConv 5 = 250 := by native_decide

/-- All six values collected. -/
theorem spConv_values :
    spConv 0 = 1
    ∧ spConv 1 = 2
    ∧ spConv 2 = 9
    ∧ spConv 3 = 28
    ∧ spConv 4 = 88
    ∧ spConv 5 = 250 := by
  exact ⟨spConv_0, spConv_1, spConv_2, spConv_3, spConv_4, spConv_5⟩

/-!
## Interpretation

SP(n) counts the 3-dimensional partitions (solid partitions) of n.
The self-convolution a(n) = (SP * SP)(n) arises as the near-vacuum
count for a 3D constrained surface model, analogous to A000712 = P*P
for the 2D case.

Zero sorry. Zero custom axioms.
-/

end CausalAlgebraicGeometry.SolidPartitionConvolution
