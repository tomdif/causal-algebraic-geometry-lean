/-
  ChamberQ4Irreducible.lean
    Hero theorem: Q_4(X) = 150 X^2 - 50 X + 3 is irreducible over ℚ.

  Q_4 is the irreducible degree-2 factor of the characteristic polynomial of
  the d=4 chamber Jacobi matrix J_4. Its discriminant is
      50^2 - 4 * 150 * 3 = 700 = 2^2 * 5^2 * 7,
  with squarefree part 7 (a rational prime). The roots are (5 ± √7)/30, and
  irrationality of √7 over ℚ gives irreducibility.

  Proof skeleton:
    * Mathlib's `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`
      reduces irreducibility (for natDegree ∈ {1,2,3} over a field) to
      "no roots in the base field".
    * If x ∈ ℚ satisfies Q_4(x) = 0 then 6·Q_4(x) = (30x-5)^2 - 7 = 0,
      so 7 is a square in ℚ. But 7 is prime in ℕ, contradiction via
      Rat.isSquare_natCast_iff and Prime.not_isSquare.
-/
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Prime.Defs

namespace CausalAlgebraicGeometry.ChamberQ4

open Polynomial

/-- The irreducible degree-2 factor of `char(J_4)` over ℚ. -/
noncomputable def Q4 : Polynomial ℚ := 150 * Polynomial.X ^ 2 - 50 * Polynomial.X + 3

/-- `Q_4` has natural degree 2. -/
theorem Q4_natDegree : Q4.natDegree = 2 := by
  unfold Q4
  compute_degree!

/-- 7 is not a square in ℚ (since it is a prime natural number). -/
private theorem seven_not_isSquare_rat : ¬ IsSquare (7 : ℚ) := by
  intro h
  have hcast : IsSquare ((7 : ℕ) : ℚ) := by exact_mod_cast h
  have hnat : ¬ IsSquare (7 : ℕ) :=
    (Nat.prime_iff.mp (by decide : Nat.Prime 7)).not_isSquare
  exact hnat (Rat.isSquare_natCast_iff.mp hcast)

/-- `Q_4` has no rational root: completing the square yields `(30x − 5)² = 7`. -/
private theorem Q4_no_root (x : ℚ) : ¬ IsRoot Q4 x := by
  intro hx
  rw [IsRoot.def, Q4] at hx
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat] at hx
  -- hx : 150 * x ^ 2 - 50 * x + 3 = 0
  refine seven_not_isSquare_rat ⟨30 * x - 5, ?_⟩
  -- Goal: (7 : ℚ) = (30 * x - 5) * (30 * x - 5)
  -- Identity: 7 - (30x-5)^2 = -6 * (150 x^2 - 50 x + 3)
  linear_combination -6 * hx

/-- **Hero theorem.** `Q_4(X) = 150 X² − 50 X + 3` is irreducible over ℚ. -/
theorem Q4_irreducible : Irreducible Q4 := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ Q4_no_root
  rw [Finset.mem_Icc, Q4_natDegree]
  exact ⟨by norm_num, by norm_num⟩

end CausalAlgebraicGeometry.ChamberQ4
