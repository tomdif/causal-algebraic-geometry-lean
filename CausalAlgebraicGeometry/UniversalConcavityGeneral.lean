/-
  UniversalConcavityGeneral.lean — The BD action is discretely concave for ALL d ≥ 2, ALL n ≥ 1.

  General theorem: for f(m) = (1-d)m^d + dm^{d-1} (the BD action),
  f(n-1) + f(n+1) ≤ 2f(n) for all d ≥ 2 and n ≥ 1.

  Proof: the second finite difference A_k(n) = (n-1)^k + (n+1)^k - 2n^k satisfies
  A_{k+1}(n) = n·A_k(n) + B_k(n) where B_k(n) = (n+1)^k - (n-1)^k.

  The BD defect at dimension d = k+2 decomposes as:
    [k+2 - (k+1)n]·A_{k+1}(n) - (k+1)·B_{k+1}(n)
  For n ≥ 2: both terms ≤ 0 (since A > 0, B > 0, coefficient ≤ -k ≤ 0).
  For n = 1: direct computation gives -(k)·2^{k+1} - 2 ≤ -2.

  This proves discrete concavity at EVERY dimension d ≥ 2 for ALL n ≥ 1,
  completing what was previously verified only through d ≤ 8.

  Zero sorry.
-/
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.UniversalConcavityGeneral

-- Second finite difference of m^k
def A (k : ℕ) (n : ℤ) : ℤ := (n - 1) ^ k + (n + 1) ^ k - 2 * n ^ k

-- First finite difference of m^k
def B (k : ℕ) (n : ℤ) : ℤ := (n + 1) ^ k - (n - 1) ^ k

/-- Key recurrence: A_{k+1}(n) = n·A_k(n) + B_k(n). -/
theorem A_succ (k : ℕ) (n : ℤ) : A (k + 1) n = n * A k n + B k n := by
  simp only [A, B, pow_succ]; ring

theorem A_one (n : ℤ) : A 1 n = 0 := by unfold A; ring

theorem B_one (n : ℤ) : B 1 n = 2 := by unfold B; ring

theorem A_two (n : ℤ) : A 2 n = 2 := by unfold A; ring

theorem A_at_one (k : ℕ) (hk : 1 ≤ k) : A k 1 = 2 ^ k - 2 := by
  simp only [A, show (1 : ℤ) - 1 = 0 from by norm_num, show (1 : ℤ) + 1 = 2 from by norm_num,
    zero_pow (show k ≠ 0 from by omega), one_pow, zero_add, mul_one]

theorem B_at_one (k : ℕ) (hk : 1 ≤ k) : B k 1 = (2 : ℤ) ^ k := by
  simp only [B, show (1 : ℤ) + 1 = 2 from by norm_num, show (1 : ℤ) - 1 = 0 from by norm_num,
    zero_pow (show k ≠ 0 from by omega), sub_zero]

/-- B_k(n) > 0 for n ≥ 1 and k ≥ 1. -/
theorem B_pos (k : ℕ) (hk : 1 ≤ k) (n : ℤ) (hn : 1 ≤ n) : 0 < B k n := by
  simp only [B]
  linarith [pow_lt_pow_left₀ (show n - 1 < n + 1 by omega)
    (show (0 : ℤ) ≤ n - 1 by omega) (show k ≠ 0 by omega)]

/-- A_k(n) > 0 for n ≥ 1 and k ≥ 2. -/
theorem A_pos (k : ℕ) (hk : 2 ≤ k) (n : ℤ) (hn : 1 ≤ n) : 0 < A k n := by
  suffices ∀ j : ℕ, 0 < A (j + 2) n from by
    rw [show k = (k - 2) + 2 from by omega]; exact this (k - 2)
  intro j; induction j with
  | zero => rw [A_two]; norm_num
  | succ j' ih =>
    rw [show j' + 1 + 2 = (j' + 2) + 1 from by omega, A_succ]
    nlinarith [B_pos (j' + 2) (by omega) n hn]

-- The BD action for dimension d = k+2: f(m) = -(k+1)m^{k+2} + (k+2)m^{k+1}
def bdAction (k : ℕ) (m : ℤ) : ℤ :=
  -((k : ℤ) + 1) * m ^ (k + 2) + ((k : ℤ) + 2) * m ^ (k + 1)

/-- The defect factors through A. -/
theorem defect_eq (k : ℕ) (n : ℤ) :
    bdAction k (n - 1) + bdAction k (n + 1) - 2 * bdAction k n =
    -((k : ℤ) + 1) * A (k + 2) n + ((k : ℤ) + 2) * A (k + 1) n := by
  simp only [bdAction, A]; ring

/-- The defect decomposes into two terms using the recurrence. -/
theorem defect_decomp (k : ℕ) (n : ℤ) :
    -((k : ℤ) + 1) * A (k + 2) n + ((k : ℤ) + 2) * A (k + 1) n =
    ((k : ℤ) + 2 - ((k : ℤ) + 1) * n) * A (k + 1) n -
    ((k : ℤ) + 1) * B (k + 1) n := by
  rw [show k + 2 = (k + 1) + 1 from rfl, A_succ]; ring

/-- **Universal discrete concavity**: the BD action f(m) = (1-d)m^d + dm^{d-1}
    satisfies f(n-1) + f(n+1) ≤ 2f(n) for ALL d ≥ 2 and ALL n ≥ 1.

    Here d = k + 2, so k = 0 corresponds to d = 2. -/
theorem universal_discrete_concavity (k : ℕ) (n : ℤ) (hn : 1 ≤ n) :
    bdAction k (n - 1) + bdAction k (n + 1) ≤ 2 * bdAction k n := by
  suffices bdAction k (n - 1) + bdAction k (n + 1) - 2 * bdAction k n ≤ 0 by linarith
  rw [defect_eq, defect_decomp]
  cases k with
  | zero =>
    -- d = 2: A(1,n) = 0, B(1,n) = 2, defect = -2
    rw [A_one, B_one]; norm_num
  | succ k' =>
    -- d ≥ 3
    by_cases hn1 : n = 1
    · -- n = 1: defect = 2^{k'+2} - 2 - (k'+2)·2^{k'+2} = -(k'+1)·2^{k'+2} - 2
      subst hn1
      rw [A_at_one (k' + 2) (by omega), B_at_one (k' + 2) (by omega)]
      have h2pos := pow_pos (show (0 : ℤ) < 2 by norm_num) (k' + 2)
      have hkpos : (0 : ℤ) ≤ ↑k' := Nat.cast_nonneg _
      push_cast
      nlinarith
    · -- n ≥ 2: coefficient ≤ 0 and A > 0, so first term ≤ 0; second term < 0
      have hn2 : 2 ≤ n := by omega
      have hA := A_pos (k' + 2) (by omega) n (by omega)
      have hB := B_pos (k' + 2) (by omega) n (by omega)
      have hkpos : (0 : ℤ) ≤ ↑k' := Nat.cast_nonneg _
      have hcoeff : ((↑(k' + 1) : ℤ) + 2 - ((↑(k' + 1) : ℤ) + 1) * n) ≤ 0 := by
        push_cast; nlinarith
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hcoeff (le_of_lt hA)]

-- Verification: bdAction matches the known polynomial forms
example : bdAction 0 m = -m ^ 2 + 2 * m ^ 1 := by unfold bdAction; ring
example : bdAction 1 m = -2 * m ^ 3 + 3 * m ^ 2 := by unfold bdAction; ring
example : bdAction 2 m = -3 * m ^ 4 + 4 * m ^ 3 := by unfold bdAction; ring
example : bdAction 3 m = -4 * m ^ 5 + 5 * m ^ 4 := by unfold bdAction; ring

-- Consistency check: defect at n=1 matches the formula from UniversalConcavity.lean
-- defect_at_one d = 2^{d-1}·(2-d) - 2
example : bdAction 0 0 + bdAction 0 2 - 2 * bdAction 0 1 = -2 := by unfold bdAction; norm_num
example : bdAction 1 0 + bdAction 1 2 - 2 * bdAction 1 1 = -6 := by unfold bdAction; norm_num
example : bdAction 2 0 + bdAction 2 2 - 2 * bdAction 2 1 = -18 := by unfold bdAction; norm_num
example : bdAction 3 0 + bdAction 3 2 - 2 * bdAction 3 1 = -50 := by unfold bdAction; norm_num

end CausalAlgebraicGeometry.UniversalConcavityGeneral
