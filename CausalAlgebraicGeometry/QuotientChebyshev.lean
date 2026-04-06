/-
  QuotientChebyshev.lean — Quotient polynomials are Mobius pullbacks of Chebyshev

  ═══════════════════════════════════════════════════════════════════
  THEOREM (Mobius-Chebyshev Spectral Containment):

  For the d=2 Weyl chamber with even m = 2(n+1), the spectral quotient
  q_n(x) = p+(x)/p-(x) decomposes as:

    q_n(x) = P_{n+1}(x) - Q_n(x)

  where:
    P_k(x) = (x+1)^k * T_k(x/(x+1))   [Mobius-Chebyshev first kind]
    Q_k(x) = (x+1)^k * U_k(x/(x+1))   [Mobius-Chebyshev second kind]

  Both families satisfy the recurrence:
    f_{k+1}(x) = 2x * f_k(x) - (x+1)^2 * f_{k-1}(x)

  This is the Chebyshev recurrence s_{k+1} = 2y*s_k - s_{k-1}
  pulled back through the Mobius map y = x/(x+1).

  VERIFIED computationally for n = 1,2,3,4 in mobius_chebyshev.py.
  ═══════════════════════════════════════════════════════════════════
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace CausalAlgebraicGeometry.QuotientChebyshev

open Real

/-! ## Part 1: Chebyshev recurrence (self-contained, ℝ-valued)

  We define Chebyshev polynomials directly as functions ℕ → ℝ → ℝ
  (evaluated at a point), rather than Mathlib's abstract Polynomial type. -/

/-- Chebyshev polynomial of the first kind, evaluated at y. -/
noncomputable def chebyshevT : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, y => y
  | (n + 2), y => 2 * y * chebyshevT (n + 1) y - chebyshevT n y

/-- Chebyshev polynomial of the second kind, evaluated at y. -/
noncomputable def chebyshevU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, y => 2 * y
  | (n + 2), y => 2 * y * chebyshevU (n + 1) y - chebyshevU n y

@[simp] theorem chebyshevT_zero (y : ℝ) : chebyshevT 0 y = 1 := by
  simp [chebyshevT]

@[simp] theorem chebyshevT_one (y : ℝ) : chebyshevT 1 y = y := by
  simp [chebyshevT]

theorem chebyshevT_succ (n : ℕ) (y : ℝ) :
    chebyshevT (n + 2) y = 2 * y * chebyshevT (n + 1) y - chebyshevT n y := by
  simp [chebyshevT]

@[simp] theorem chebyshevU_zero (y : ℝ) : chebyshevU 0 y = 1 := by
  simp [chebyshevU]

@[simp] theorem chebyshevU_one (y : ℝ) : chebyshevU 1 y = 2 * y := by
  simp [chebyshevU]

theorem chebyshevU_succ (n : ℕ) (y : ℝ) :
    chebyshevU (n + 2) y = 2 * y * chebyshevU (n + 1) y - chebyshevU n y := by
  simp [chebyshevU]

/-! ### Explicit values -/

theorem chebyshevT_two (y : ℝ) : chebyshevT 2 y = 2 * y ^ 2 - 1 := by
  rw [chebyshevT_succ]; simp; ring

theorem chebyshevU_two (y : ℝ) : chebyshevU 2 y = 4 * y ^ 2 - 1 := by
  rw [chebyshevU_succ]; simp; ring

/-! ## Part 2: Recurrence properties -/

/-- The quotient recurrence property. -/
def satisfiesQuotientRecurrence (q : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ,
    q (n + 2) x = 2 * x * q (n + 1) x - (x + 1) ^ 2 * q n x

/-- The Chebyshev recurrence property. -/
def satisfiesChebyshevRecurrence (s : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ y : ℝ,
    s (n + 2) y = 2 * y * s (n + 1) y - s n y

/-- chebyshevT satisfies the Chebyshev recurrence. -/
theorem chebyshevT_recurrence : satisfiesChebyshevRecurrence chebyshevT :=
  fun n y => chebyshevT_succ n y

/-- chebyshevU satisfies the Chebyshev recurrence. -/
theorem chebyshevU_recurrence : satisfiesChebyshevRecurrence chebyshevU :=
  fun n y => chebyshevU_succ n y

/-! ## Part 3: The Mobius-Chebyshev recurrence transformation

  CORE THEOREM: If s satisfies the Chebyshev recurrence
    s(n+2, y) = 2y * s(n+1, y) - s(n, y)
  and we define q(n, x) = (x+1)^n * s(n, x/(x+1)),
  then q satisfies the quotient recurrence
    q(n+2, x) = 2x * q(n+1, x) - (x+1)^2 * q(n, x).

  Proof: pure algebra. -/

/-- The core identity without division hypotheses:
  a^{n+2} * (2*(b/a)*f - g) = 2b * a^{n+1} * f - a^2 * a^n * g
  when a ≠ 0. -/
theorem pullback_recurrence_identity (a b f g : ℝ) (n : ℕ) (ha : a ≠ 0) :
    a ^ (n + 2) * (2 * (b / a) * f - g) =
    2 * b * (a ^ (n + 1) * f) - a ^ 2 * (a ^ n * g) := by
  field_simp
  ring

/-- The Mobius-Chebyshev recurrence transformation.
  Any Chebyshev solution, pulled back via y = x/(x+1) and scaled by (x+1)^n,
  yields a quotient recurrence solution. -/
theorem mobius_chebyshev_recurrence
    (s : ℕ → ℝ → ℝ)
    (hs : satisfiesChebyshevRecurrence s) :
    satisfiesQuotientRecurrence (fun n x => (x + 1) ^ n * s n (x / (x + 1))) := by
  intro n x
  simp only
  rw [hs n (x / (x + 1))]
  by_cases hx : x + 1 = 0
  · -- x = -1: both sides are 0 since (x+1)^k = 0 for k ≥ 1
    have hx1 : x = -1 := by linarith
    subst hx1
    simp [pow_succ]
  · exact pullback_recurrence_identity (x + 1) x (s (n + 1) (x / (x + 1)))
      (s n (x / (x + 1))) n hx

/-- The quotient recurrence is linear. -/
theorem quotient_recurrence_linear
    (q₁ q₂ : ℕ → ℝ → ℝ) (a b : ℝ)
    (h₁ : satisfiesQuotientRecurrence q₁)
    (h₂ : satisfiesQuotientRecurrence q₂) :
    satisfiesQuotientRecurrence (fun n x => a * q₁ n x + b * q₂ n x) := by
  intro n x
  simp only [h₁ n x, h₂ n x]
  ring

/-! ## Part 4: Mobius-Chebyshev polynomial families -/

/-- Mobius-Chebyshev polynomial of the first kind:
  P_k(x) = (x+1)^k * T_k(x/(x+1)). -/
noncomputable def mobiusT (k : ℕ) (x : ℝ) : ℝ :=
  (x + 1) ^ k * chebyshevT k (x / (x + 1))

/-- Mobius-Chebyshev polynomial of the second kind:
  Q_k(x) = (x+1)^k * U_k(x/(x+1)). -/
noncomputable def mobiusU (k : ℕ) (x : ℝ) : ℝ :=
  (x + 1) ^ k * chebyshevU k (x / (x + 1))

/-- mobiusT satisfies the quotient recurrence. -/
theorem mobiusT_recurrence : satisfiesQuotientRecurrence mobiusT := by
  show satisfiesQuotientRecurrence (fun n x => (x + 1) ^ n * chebyshevT n (x / (x + 1)))
  exact mobius_chebyshev_recurrence chebyshevT chebyshevT_recurrence

/-- mobiusU satisfies the quotient recurrence. -/
theorem mobiusU_recurrence : satisfiesQuotientRecurrence mobiusU := by
  show satisfiesQuotientRecurrence (fun n x => (x + 1) ^ n * chebyshevU n (x / (x + 1)))
  exact mobius_chebyshev_recurrence chebyshevU chebyshevU_recurrence

/-! ### Initial values -/

@[simp] theorem mobiusT_zero (x : ℝ) : mobiusT 0 x = 1 := by
  simp [mobiusT]

@[simp] theorem mobiusU_zero (x : ℝ) : mobiusU 0 x = 1 := by
  simp [mobiusU]

/-! ## Part 5: The quotient polynomial q_n = P_{n+1} - Q_n -/

/-- The quotient polynomial: q_n(x) = P_{n+1}(x) - Q_n(x)
  = (x+1)^{n+1} * T_{n+1}(x/(x+1)) - (x+1)^n * U_n(x/(x+1)). -/
noncomputable def quotientPoly (n : ℕ) (x : ℝ) : ℝ :=
  mobiusT (n + 1) x - mobiusU n x

/-- The quotient polynomial satisfies the quotient recurrence.
  This follows by linearity since mobiusT(n+1) and mobiusU(n) both
  satisfy the recurrence. -/
theorem quotientPoly_recurrence :
    satisfiesQuotientRecurrence quotientPoly := by
  intro n x
  show mobiusT (n + 2 + 1) x - mobiusU (n + 2) x =
    2 * x * (mobiusT (n + 1 + 1) x - mobiusU (n + 1) x) -
    (x + 1) ^ 2 * (mobiusT (n + 1) x - mobiusU n x)
  have hT := mobiusT_recurrence (n + 1) x
  have hU := mobiusU_recurrence n x
  -- hT: mobiusT(n+3) = 2x*mobiusT(n+2) - (x+1)^2*mobiusT(n+1)
  -- hU: mobiusU(n+2) = 2x*mobiusU(n+1) - (x+1)^2*mobiusU(n)
  linarith

/-! ## Part 6: Inverse transformation -/

/-- The inverse Mobius transform: if q satisfies the quotient recurrence,
  the rescaled sequence satisfies Chebyshev. -/
theorem inverse_mobius_transform (q : ℕ → ℝ → ℝ)
    (hq : satisfiesQuotientRecurrence q)
    (x : ℝ) (hx : x + 1 ≠ 0) (n : ℕ) :
    q (n + 2) x / (x + 1) ^ (n + 2) =
    2 * (x / (x + 1)) * (q (n + 1) x / (x + 1) ^ (n + 1)) -
    q n x / (x + 1) ^ n := by
  have hq' := hq n x
  have hpow : (x + 1) ^ (n + 2) ≠ 0 := pow_ne_zero _ hx
  rw [hq']
  field_simp
  ring

/-! ## Part 7: Spectral Containment Theorem (statement) -/

/-- Statement: spectral containment for d=2, even m.
  For even m = 2(n+1), the R-even characteristic polynomial p+ factors as
  p+(x) = p-(x) * q_n(x) where q_n is the quotient polynomial. -/
def SpectralContainment (pPlus pMinus : ℝ → ℝ) (n : ℕ) : Prop :=
  ∀ x : ℝ, pPlus x = pMinus x * quotientPoly n x

/-- The spectral zero location formula:
  Zeros of q_n are at x_k = cos(theta_k)/(1 - cos(theta_k))
  where theta_k = (2k-1)*pi/(2n+3) for k = 1,...,n+1. -/
noncomputable def spectralZero (n k : ℕ) : ℝ :=
  let θ := ((2 : ℝ) * ↑k - 1) * π / (2 * ↑n + 3)
  let y := cos θ
  y / (1 - y)

/-! ## Summary

  PROVED (0 sorry):
    1. pullback_recurrence_identity — core algebraic identity
    2. mobius_chebyshev_recurrence — Chebyshev → quotient via Mobius pullback
    3. mobiusT_recurrence — P_k satisfies the quotient recurrence
    4. mobiusU_recurrence — Q_k satisfies the quotient recurrence
    5. quotientPoly_recurrence — q_n = P_{n+1} - Q_n satisfies the recurrence
    6. inverse_mobius_transform — quotient → Chebyshev (inverse direction)
    7. quotient_recurrence_linear — linearity of the recurrence

  VERIFIED (Python, mobius_chebyshev.py):
    q_n = P_{n+1} - Q_n for n = 1,2,3,4 (m = 4,6,8,10)
    Zero locations: theta_k/pi = (2k-1)/(2n+3)

  SPECTRAL CONTAINMENT:
    p+(x) = p-(x) * [P_{n+1}(x) - Q_n(x)]
    where P_k, Q_k are the Mobius-Chebyshev families.
-/

end CausalAlgebraicGeometry.QuotientChebyshev
