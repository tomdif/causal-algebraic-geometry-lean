/-
  MacMahonFormula.lean -- The MacMahon product formula for dominating antitone pairs.

  We prove the pure arithmetic identity:

    C(2m,m)^2 * ((m-1)! * m!^2 * (m+1)!) = (2m-1)! * (2m)! * (2*(m+1))

  This is the cleared-denominator form of the MacMahon box formula:
    |dominating antitone pairs| = C(2m,m)^2 / (2*(m+1))
                                = (2m-1)! * (2m)! / ((m-1)! * m!^2 * (m+1)!)

  The proof is pure factorial arithmetic: expand (2m)! = 2m*(2m-1)! and
  (m+1)! = (m+1)*m! and m! = m*(m-1)!, then verify by ring.
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.MacMahonFormula

open Nat

/-! ## Core factorial identity -/

/-- The main cleared-denominator identity:
    (2m)! * (m-1)! * (m+1)! = (2m-1)! * 2*(m+1) * m!^2   for m ≥ 1.

    Proof: (2m)! = 2m*(2m-1)!, (m+1)! = (m+1)*m!, m! = m*(m-1)!,
    then both sides equal 2*m^2*(m+1)*(2m-1)!*(m-1)!^2. -/
theorem factorial_identity (m : ℕ) (hm : 1 ≤ m) :
    (2 * m).factorial * (m - 1).factorial * (m + 1).factorial =
    (2 * m - 1).factorial * (2 * (m + 1)) * m.factorial ^ 2 := by
  -- Write m = k + 1 to avoid Nat subtraction issues
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  -- Simplify Nat subtraction
  rw [show 1 + k = k + 1 from by omega]
  simp only [show k + 1 - 1 = k from by omega,
             show 2 * (k + 1) - 1 = 2 * k + 1 from by omega]
  -- Goal: (2*(k+1))! * k! * (k+2)! = (2*k+1)! * (2*(k+2)) * (k+1)!^2
  -- Unfold all factorials in terms of k!
  have hf1 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  have hf2 : (k + 2).factorial = (k + 2) * (k + 1).factorial := by
    rw [show k + 2 = (k + 1) + 1 from by omega]; exact Nat.factorial_succ (k + 1)
  have hf3 : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1).factorial := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by omega]; exact Nat.factorial_succ (2 * k + 1)
  rw [hf2, hf1, hf3, show 2 * (k + 1 + 1) = 2 * (k + 2) from by omega, sq]
  ring

/-! ## Connection to binomial coefficients -/

/-- C(2m,m) * m! * m! = (2m)! -/
theorem choose_mul_factorial_sq (m : ℕ) :
    Nat.choose (2 * m) m * m.factorial * m.factorial = (2 * m).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
  rwa [show 2 * m - m = m from by omega] at h

/-- C(2m,m)^2 * m!^4 = (2m)!^2 -/
theorem choose_sq_mul_factorial_fourth (m : ℕ) :
    Nat.choose (2 * m) m ^ 2 * m.factorial ^ 4 = (2 * m).factorial ^ 2 := by
  have h := choose_mul_factorial_sq m
  nlinarith [h]

/-- The MacMahon product formula (cleared-denominator form):
    C(2m,m)^2 * ((m-1)! * m!^2 * (m+1)!) = (2m-1)! * (2m)! * (2*(m+1))
    for m ≥ 1. -/
theorem macmahon_identity_cleared (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 * m) m ^ 2 *
      ((m - 1).factorial * m.factorial ^ 2 * (m + 1).factorial) =
    (2 * m - 1).factorial * (2 * m).factorial * (2 * (m + 1)) := by
  -- Multiply both sides by m!^2 to clear, then use the two key identities.
  suffices h : Nat.choose (2 * m) m ^ 2 *
      ((m - 1).factorial * m.factorial ^ 2 * (m + 1).factorial) * m.factorial ^ 2 =
      (2 * m - 1).factorial * (2 * m).factorial * (2 * (m + 1)) * m.factorial ^ 2 by
    have hpos : 0 < m.factorial ^ 2 := by positivity
    have h' : m.factorial ^ 2 * (Nat.choose (2 * m) m ^ 2 *
        ((m - 1).factorial * m.factorial ^ 2 * (m + 1).factorial)) =
        m.factorial ^ 2 * ((2 * m - 1).factorial * (2 * m).factorial * (2 * (m + 1))) := by
      linarith
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  have hfi := factorial_identity m hm
  have hcsf := choose_sq_mul_factorial_fourth m
  set C := Nat.choose (2 * m) m
  set F := m.factorial
  set G := (2 * m).factorial
  set H := (2 * m - 1).factorial
  set A := (m - 1).factorial
  set B := (m + 1).factorial
  -- hcsf : C^2 * F^4 = G^2
  -- hfi : G * A * B = H * (2*(m+1)) * F^2
  -- Goal: C^2 * (A * F^2 * B) * F^2 = H * G * (2*(m+1)) * F^2
  have lhs_rw : C ^ 2 * (A * F ^ 2 * B) * F ^ 2 = (C ^ 2 * F ^ 4) * (A * B) := by ring
  have rhs_rw : H * G * (2 * (m + 1)) * F ^ 2 = G * (H * (2 * (m + 1)) * F ^ 2) := by ring
  rw [lhs_rw, hcsf, rhs_rw, ← hfi]
  ring

/-! ## Divisibility and division form -/

/-- (m+1) divides C(2m,m) (Catalan divisibility). -/
theorem succ_dvd_centralBinom (m : ℕ) : (m + 1) ∣ Nat.choose (2 * m) m := by
  have h := Nat.succ_dvd_centralBinom m
  rwa [Nat.centralBinom_eq_two_mul_choose] at h

/-- 2*(m+1) divides C(2m,m)^2 for m ≥ 1. -/
theorem two_mul_succ_dvd_choose_sq (m : ℕ) (hm : 1 ≤ m) :
    2 * (m + 1) ∣ Nat.choose (2 * m) m ^ 2 := by
  obtain ⟨k, hk⟩ := succ_dvd_centralBinom m
  have h2 : 2 ∣ Nat.choose (2 * m) m := by
    have := Nat.two_dvd_centralBinom_of_one_le hm
    rwa [Nat.centralBinom_eq_two_mul_choose] at this
  obtain ⟨j, hj⟩ := h2
  -- C = (m+1)*k = 2*j
  -- C^2 = (m+1)*k * 2*j = 2*(m+1)*(k*j)
  rw [sq, hk]
  -- Goal: 2*(m+1) | (m+1)*k * ((m+1)*k)
  have hkj : (m + 1) * k = 2 * j := by linarith
  rw [hkj]
  -- Goal: 2*(m+1) | 2*j * (2*j)
  -- Since (m+1)*k = 2*j, we have j = (m+1)*k/2.
  -- 2*j*(2*j) = 4*j^2 and 2*(m+1) | 4*j^2 iff (m+1) | 2*j^2
  -- But 2*j = (m+1)*k, so 2*j^2 = j*(m+1)*k, and (m+1) | j*(m+1)*k.
  rw [show 2 * j * (2 * j) = 2 * (2 * j * j) from by ring]
  rw [show 2 * (m + 1) = 2 * (m + 1) from rfl]
  apply Nat.mul_dvd_mul_left
  -- Goal: (m+1) | 2*j*j
  rw [show 2 * j = (m + 1) * k from hkj.symm]
  rw [show (m + 1) * k * j = (m + 1) * (k * j) from by ring]
  exact dvd_mul_right _ _

/-- The MacMahon product formula (division form):
    C(2m,m)^2 / (2*(m+1)) is the exact quotient, for m ≥ 1.

    Combined with macmahon_identity_cleared, this gives:
    C(2m,m)^2 / (2*(m+1)) = (2m-1)!*(2m)! / ((m-1)!*m!^2*(m+1)!) -/
theorem macmahon_div_exact (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) * (2 * (m + 1)) =
    Nat.choose (2 * m) m ^ 2 :=
  Nat.div_mul_cancel (two_mul_succ_dvd_choose_sq m hm)

/-- Verification for small cases by computation. -/
example : Nat.choose (2 * 1) 1 ^ 2 / (2 * (1 + 1)) = 1 := by native_decide
example : Nat.choose (2 * 2) 2 ^ 2 / (2 * (2 + 1)) = 6 := by native_decide
example : Nat.choose (2 * 3) 3 ^ 2 / (2 * (3 + 1)) = 50 := by native_decide
example : Nat.choose (2 * 4) 4 ^ 2 / (2 * (4 + 1)) = 490 := by native_decide

end CausalAlgebraicGeometry.MacMahonFormula
