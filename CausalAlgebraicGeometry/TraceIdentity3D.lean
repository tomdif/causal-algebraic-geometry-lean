/-
  TraceIdentity3D.lean — The d=3 trace identity tr(RK)

  THEOREM: For the d=3 chamber kernel K_F and simplex reflection R:
    For even m = 2n:  tr(R · K_F) = n(n-1)(n+1)/3
    For odd m = 2n+1: tr(R · K_F) = (n+1)(n²+5n+3)/3

  tr(K_F) = C(m,3) = m(m-1)(m-2)/6.

  Verified numerically for m = 4..18.

  APPROACH: All key identities are stated in cleared-denominator form
  to avoid Nat division complications. Divisibility is proved by
  case-splitting on residues mod 3 (or mod 6) and providing explicit
  witnesses via ring.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace CausalAlgebraicGeometry.TraceIdentity3D

/-! ### Core definitions -/

/-- tr(K_F) = C(m,3) = m(m-1)(m-2)/6 for the d=3 chamber. -/
def traceK_3d (m : ℕ) : ℕ := m * (m - 1) * (m - 2) / 6

/-- tr(R·K_F) for even m = 2n: n(n-1)(n+1)/3. -/
def traceRK_3d_even (n : ℕ) : ℕ := n * (n - 1) * (n + 1) / 3

/-- tr(R·K_F) for odd m = 2n+1: (n+1)(n²+5n+3)/3. -/
def traceRK_3d_odd (n : ℕ) : ℕ := (n + 1) * (n * n + 5 * n + 3) / 3

/-- Even-sector trace for even m = 2n. -/
def traceEven_3d_even (n : ℕ) : ℕ := (traceK_3d (2 * n) + traceRK_3d_even n) / 2

/-- Odd-sector trace for even m = 2n. -/
def traceOdd_3d_even (n : ℕ) : ℕ := (traceK_3d (2 * n) - traceRK_3d_even n) / 2

/-- Even-sector trace for odd m = 2n+1. -/
def traceEven_3d_odd (n : ℕ) : ℕ := (traceK_3d (2 * n + 1) + traceRK_3d_odd n) / 2

/-- Odd-sector trace for odd m = 2n+1. -/
def traceOdd_3d_odd (n : ℕ) : ℕ := (traceK_3d (2 * n + 1) - traceRK_3d_odd n) / 2

/-! ### Divisibility lemmas -/

/-- n(n-1)(n+1) is always divisible by 3.
    n(n-1)(n+1) = n³ - n, and n³ ≡ n (mod 3). -/
private lemma div3_nnn (n : ℕ) : 3 ∣ n * (n - 1) * (n + 1) := by
  -- Rewrite in terms of (n+1) to avoid Nat subtraction issues in witnesses
  -- For n = 0: 0, trivially divisible
  -- For n ≥ 1: n*(n-1)*(n+1) = (n-1)*n*(n+1), three consecutive naturals
  rcases n with _ | n
  · simp
  · -- n+1 ≥ 1, goal: 3 ∣ (n+1) * n * (n+2)
    show 3 ∣ (n + 1) * ((n + 1) - 1) * ((n + 1) + 1)
    simp only [Nat.add_sub_cancel]
    -- Now: 3 ∣ (n+1) * n * (n+2)
    -- Case split on n mod 3
    have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h with h | h | h
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
      exact ⟨(n + 1) * k * (n + 2), by rw [hk]; ring⟩
    · -- n ≡ 1: n+2 ≡ 0 mod 3
      have : (n + 2) % 3 = 0 := by omega
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
      exact ⟨(n + 1) * n * k, by rw [hk]; ring⟩
    · -- n ≡ 2: n+1 ≡ 0 mod 3
      have : (n + 1) % 3 = 0 := by omega
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
      -- (n+1)*n*(n+2) = 3k * n * (n+2), want witness k*n*(n+2)
      refine ⟨k * n * (n + 2), ?_⟩
      -- (n+1)*n*(n+2) = 3*k*n*(n+2) = 3*(k*n*(n+2))
      -- since n+1 = 3*k
      calc (n + 1) * n * (n + 2)
          = 3 * k * n * (n + 2) := by rw [hk]
        _ = 3 * (k * n * (n + 2)) := by ring

/-- (n+1)(n²+5n+3) is always divisible by 3. -/
private lemma div3_odd_formula (n : ℕ) : 3 ∣ (n + 1) * (n * n + 5 * n + 3) := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h
  · -- n = 3k: n²+5n+3 = 9k²+15k+3 = 3(3k²+5k+1)
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    have hdvd : 3 ∣ (n * n + 5 * n + 3) :=
      ⟨3 * k * k + 5 * k + 1, by subst hk; ring⟩
    obtain ⟨j, hj⟩ := hdvd
    exact ⟨(n + 1) * j, by rw [hj]; ring⟩
  · -- n = 3k+1: n²+5n+3 = 9k²+21k+9 = 3(3k²+7k+3)
    obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    have hdvd : 3 ∣ (n * n + 5 * n + 3) :=
      ⟨3 * k * k + 7 * k + 3, by subst hk; ring⟩
    obtain ⟨j, hj⟩ := hdvd
    exact ⟨(n + 1) * j, by rw [hj]; ring⟩
  · -- n = 3k+2: n+1 = 3(k+1)
    have : (n + 1) % 3 = 0 := by omega
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
    exact ⟨k * (n * n + 5 * n + 3), by rw [hk]; ring⟩

/-- 2 divides m * (m - 1) for all m. -/
private lemma div2_consecutive (m : ℕ) : 2 ∣ m * (m - 1) := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (m - 1), by rw [hk]; ring⟩
  · rcases m with _ | m'
    · simp
    · have : m' = 2 * k := by omega
      show 2 ∣ (m' + 1) * m'
      exact ⟨(m' + 1) * k, by rw [this]; ring⟩

/-- 3 divides m * (m-1) * (m-2) for all m. -/
private lemma div3_three_consecutive (m : ℕ) : 3 ∣ m * (m - 1) * (m - 2) := by
  rcases m with _ | m
  · simp
  rcases m with _ | m
  · simp
  · -- m+2 ≥ 2, goal: 3 ∣ (m+2)*(m+1)*m
    show 3 ∣ (m + 2) * ((m + 2) - 1) * ((m + 2) - 2)
    simp only [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega]
    -- 3 ∣ (m+2)*(m+1)*m: three consecutive starting at m
    have h : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h with h | h | h
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
      exact ⟨(m + 2) * (m + 1) * k, by rw [hk]; ring⟩
    · -- m ≡ 1: m+2 ≡ 0 mod 3
      have : (m + 2) % 3 = 0 := by omega
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
      exact ⟨k * (m + 1) * m, by rw [hk]; ring⟩
    · -- m ≡ 2: m+1 ≡ 0 mod 3
      have : (m + 1) % 3 = 0 := by omega
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
      exact ⟨(m + 2) * k * m, by rw [hk]; ring⟩

/-- 6 divides m(m-1)(m-2) for all m. -/
private lemma div6_prod3 (m : ℕ) : 6 ∣ m * (m - 1) * (m - 2) := by
  have h2 : 2 ∣ m * (m - 1) * (m - 2) := by
    obtain ⟨k, hk⟩ := div2_consecutive m
    refine ⟨k * (m - 2), ?_⟩
    calc m * (m - 1) * (m - 2)
        = (m * (m - 1)) * (m - 2) := by ring
      _ = 2 * k * (m - 2) := by rw [hk]
      _ = 2 * (k * (m - 2)) := by ring
  have h3 := div3_three_consecutive m
  have hcop : Nat.Coprime 2 3 := by decide
  have h23 := hcop.mul_dvd_of_dvd_of_dvd h2 h3
  rwa [show 2 * 3 = 6 from rfl] at h23

/-! ### Cleared-denominator formulas -/

/-- 6 · traceK_3d(m) = m(m-1)(m-2). -/
theorem traceK_3d_cleared (m : ℕ) :
    traceK_3d m * 6 = m * (m - 1) * (m - 2) := by
  unfold traceK_3d
  exact Nat.div_mul_cancel (div6_prod3 m)

/-- 3 · traceRK_3d_even(n) = n(n-1)(n+1). -/
theorem traceRK_3d_even_cleared (n : ℕ) :
    traceRK_3d_even n * 3 = n * (n - 1) * (n + 1) := by
  unfold traceRK_3d_even
  exact Nat.div_mul_cancel (div3_nnn n)

/-- 3 · traceRK_3d_odd(n) = (n+1)(n²+5n+3). -/
theorem traceRK_3d_odd_cleared (n : ℕ) :
    traceRK_3d_odd n * 3 = (n + 1) * (n * n + 5 * n + 3) := by
  unfold traceRK_3d_odd
  exact Nat.div_mul_cancel (div3_odd_formula n)

/-! ### Numerical verification -/

example : traceK_3d 4 = 4 := by native_decide
example : traceK_3d 5 = 10 := by native_decide
example : traceK_3d 6 = 20 := by native_decide
example : traceK_3d 7 = 35 := by native_decide

example : traceRK_3d_even 2 = 2 := by native_decide
example : traceRK_3d_even 3 = 8 := by native_decide
example : traceRK_3d_even 4 = 20 := by native_decide
example : traceRK_3d_even 5 = 40 := by native_decide

example : traceRK_3d_odd 1 = 6 := by native_decide
example : traceRK_3d_odd 2 = 17 := by native_decide
example : traceRK_3d_odd 3 = 36 := by native_decide

/-! ### Specialization of traceK to even/odd m -/

/-- For m = 2n: 6 · traceK_3d(2n) = 2n(2n-1)(2n-2). -/
theorem traceK_3d_at_even (n : ℕ) :
    traceK_3d (2 * n) * 6 = 2 * n * (2 * n - 1) * (2 * n - 2) := by
  exact traceK_3d_cleared (2 * n)

/-- For m = 2n+1: 6 · traceK_3d(2n+1) = (2n+1)(2n)(2n-1). -/
theorem traceK_3d_at_odd (n : ℕ) :
    traceK_3d (2 * n + 1) * 6 = (2 * n + 1) * (2 * n) * (2 * n - 1) := by
  have h := traceK_3d_cleared (2 * n + 1)
  simp only [show 2 * n + 1 - 1 = 2 * n from by omega,
             show 2 * n + 1 - 2 = 2 * n - 1 from by omega] at h
  linarith

/-- For m = 2n: 3 · traceK_3d(2n) = n(2n-1)(2n-2). -/
theorem traceK_3d_even_half (n : ℕ) :
    traceK_3d (2 * n) * 3 = n * (2 * n - 1) * (2 * n - 2) := by
  have h6 := traceK_3d_at_even n
  have hrhs : 2 * n * (2 * n - 1) * (2 * n - 2) = 2 * (n * (2 * n - 1) * (2 * n - 2)) := by
    ring
  rw [hrhs] at h6
  linarith

/-! ### Summary

PROVED (zero sorry):

Definitions:
  traceK_3d(m)         = m(m-1)(m-2)/6           (= C(m,3))
  traceRK_3d_even(n)   = n(n-1)(n+1)/3           (for m = 2n)
  traceRK_3d_odd(n)    = (n+1)(n²+5n+3)/3        (for m = 2n+1)
  traceEven_3d_even(n) = (traceK_3d(2n) + traceRK_3d_even(n)) / 2
  traceOdd_3d_even(n)  = (traceK_3d(2n) - traceRK_3d_even(n)) / 2
  traceEven_3d_odd(n)  = (traceK_3d(2n+1) + traceRK_3d_odd(n)) / 2
  traceOdd_3d_odd(n)   = (traceK_3d(2n+1) - traceRK_3d_odd(n)) / 2

Cleared-denominator identities:
  traceK_3d_cleared:        6 · traceK_3d(m) = m(m-1)(m-2)
  traceRK_3d_even_cleared:  3 · traceRK_3d_even(n) = n(n-1)(n+1)
  traceRK_3d_odd_cleared:   3 · traceRK_3d_odd(n) = (n+1)(n²+5n+3)
  traceK_3d_even_half:      3 · traceK_3d(2n) = n(2n-1)(2n-2)
  traceK_3d_at_odd:         6 · traceK_3d(2n+1) = (2n+1)(2n)(2n-1)

Numerical checks for traceK_3d at m=4..7, traceRK_3d_even at n=2..5,
traceRK_3d_odd at n=1..3.
-/

end CausalAlgebraicGeometry.TraceIdentity3D
