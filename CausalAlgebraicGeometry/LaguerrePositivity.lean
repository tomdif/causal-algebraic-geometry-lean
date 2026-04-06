/-
  LaguerrePositivity.lean — Laguerre functional positivity from log-concavity

  Uses Mathlib's Monovary/rearrangement infrastructure for Newton inequalities.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Monovary
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace CausalAlgebraicGeometry.LaguerrePositivity

/-- Log-concavity: b_k² ≥ b_{k-1}·b_{k+1}. -/
def IsLogConcave (b : ℕ → ℝ) : Prop :=
  ∀ k, k ≥ 1 → b k ^ 2 ≥ b (k - 1) * b (k + 1)

/-- c₀ ≥ 0 from log-concavity at k=1. -/
theorem c0_nonneg (b : ℕ → ℝ) (h : IsLogConcave b) :
    b 1 ^ 2 - b 0 * b 2 ≥ 0 := by
  have := h 1 (le_refl 1); nlinarith [sq_nonneg (b 1)]

/-- Newton step via division: b₁²≥b₀b₂ and b₂²≥b₁b₃ → b₁b₂≥b₀b₃.
    Proof: b₀ ≤ b₁²/b₂ and b₃ ≤ b₂²/b₁, so b₀b₃ ≤ (b₁²/b₂)(b₂²/b₁) = b₁b₂. -/
theorem newton_step (b0 b1 b2 b3 : ℝ) (h0 : 0 ≤ b0) (hb1 : 0 < b1) (hb2 : 0 < b2) (h3 : 0 ≤ b3)
    (h1 : b1 ^ 2 ≥ b0 * b2) (h2 : b2 ^ 2 ≥ b1 * b3) :
    b1 * b2 ≥ b0 * b3 := by
  have step1 : b0 ≤ b1 ^ 2 / b2 := by rw [le_div_iff₀ hb2]; linarith
  have step2 : b3 ≤ b2 ^ 2 / b1 := by rw [le_div_iff₀ hb1]; linarith
  calc b0 * b3
      ≤ (b1 ^ 2 / b2) * (b2 ^ 2 / b1) := mul_le_mul step1 step2 h3 (by positivity)
    _ = b1 * b2 := by field_simp

/-- c₁ ≥ 0: b₁b₂ ≥ b₀b₃ from Newton step. -/
theorem c1_nonneg (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) (h : IsLogConcave b) :
    b 1 * b 2 - b 0 * b 3 ≥ 0 := by
  linarith [newton_step (b 0) (b 1) (b 2) (b 3) (le_of_lt (hb 0)) (hb 1) (hb 2) (le_of_lt (hb 3))
    (h 1 (le_refl 1)) (h 2 (by norm_num))]

/-- Iterated Newton: b₁b₃ ≥ b₀b₄ from chaining newton_step twice.
    b₁b₂ ≥ b₀b₃ (c1) × b₃ → b₁b₂b₃ ≥ b₀b₃².
    b₃² ≥ b₂b₄ (LC3) × b₀ → b₀b₃² ≥ b₀b₂b₄.
    Chain: b₁b₂b₃ ≥ b₀b₂b₄. Divide by b₂: b₁b₃ ≥ b₀b₄. -/
theorem newton_two_step (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) (h : IsLogConcave b) :
    b 1 * b 3 ≥ b 0 * b 4 := by
  have c1 := c1_nonneg b hb h  -- b₁b₂ ≥ b₀b₃
  have lc3 := h 3 (by norm_num)  -- b₃² ≥ b₂b₄
  -- b₁b₂b₃ ≥ b₀b₃² (multiply c1 by b₃)
  have s1 : (b 1 * b 2 - b 0 * b 3) * b 3 ≥ 0 := mul_nonneg (by linarith) (le_of_lt (hb 3))
  -- b₀(b₃²-b₂b₄) ≥ 0
  have s2 : b 0 * (b 3 ^ 2 - b 2 * b 4) ≥ 0 := mul_nonneg (le_of_lt (hb 0)) (by nlinarith)
  -- Expand and chain: b₁b₃·b₂ ≥ b₀b₄·b₂
  have key : b 1 * b 3 * b 2 ≥ b 0 * b 4 * b 2 := by nlinarith
  exact le_of_mul_le_mul_right (by linarith : b 0 * b 4 * b 2 ≤ b 1 * b 3 * b 2) (hb 2) |>.ge

/-- c₂ ≥ 0: b₂² ≥ b₀b₄ = LC(2)+NI(1,3). -/
theorem c2_nonneg (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) (h : IsLogConcave b) :
    b 2 ^ 2 - b 0 * b 4 ≥ 0 := by
  have lc2 : b 2 ^ 2 ≥ b 1 * b 3 := h 2 (by norm_num)
  have ni13 := newton_two_step b hb h  -- b₁b₃ ≥ b₀b₄
  linarith

/-- Iterated Newton 3-step: b₁b₄ ≥ b₀b₅.
    Chain: c1×b₄ + LC4×b₀ → b₁b₂b₄²≥b₀b₂b₄b₅, divide by b₂b₄. -/
theorem newton_three_step (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) (h : IsLogConcave b) :
    b 1 * b 4 ≥ b 0 * b 5 := by
  have c1 := c1_nonneg b hb h  -- b₁b₂ ≥ b₀b₃
  have lc4 := h 4 (by norm_num)  -- b₄² ≥ b₃b₅
  have lc3 := h 3 (by norm_num)  -- b₃² ≥ b₂b₄
  -- (b₁b₂-b₀b₃)(b₄²-b₃b₅) ≥ 0
  have p1 : (b 1 * b 2 - b 0 * b 3) * (b 4 ^ 2 - b 3 * b 5) ≥ 0 :=
    mul_nonneg (by linarith) (by nlinarith)
  -- b₀(b₃²-b₂b₄) ≥ 0 × b₅
  have p2 : b 0 * (b 3 ^ 2 - b 2 * b 4) * b 5 ≥ 0 :=
    mul_nonneg (mul_nonneg (le_of_lt (hb 0)) (by nlinarith)) (le_of_lt (hb 5))
  -- Expand p1: b₁b₂b₄² - b₁b₂b₃b₅ - b₀b₃b₄² + b₀b₃²b₅ ≥ 0
  -- From p2: b₀b₃²b₅ ≥ b₀b₂b₄b₅
  -- So: b₁b₂b₄² ≥ b₁b₂b₃b₅ + b₀b₃b₄² - b₀b₃²b₅
  --                ≥ b₁b₂b₃b₅ + b₀b₃b₄² - b₀b₃²b₅... complex
  -- Expand p1 and p2 to get b₁b₂b₄² + b₀b₃²b₅ ≥ b₁b₂b₃b₅ + b₀b₃b₄²
  -- and b₀b₃²b₅ ≥ b₀b₂b₄b₅
  -- Combine: b₁b₂b₄² ≥ b₁b₂b₃b₅ + b₀b₃b₄² - b₀b₃²b₅
  --          ≥ b₁b₂b₃b₅ + b₀b₃b₄² - b₀b₃²b₅  (from p1)
  -- Also: b₁b₂b₃b₅ + b₀b₂b₄b₅ ≤ b₁b₂b₃b₅ + b₀b₃²b₅ (from p2)
  -- So: b₁b₂b₄² + b₀b₂b₄b₅ ≤ b₁b₂b₄² + b₀b₃²b₅
  --       ≤ 2·b₁b₂b₄² (if b₀b₃²b₅ ≤ b₁b₂b₄²)... getting complicated.
  -- Direct: use the same division trick as newton_step.
  -- From c1: b₁b₂≥b₀b₃. So b₁/b₀ ≥ b₃/b₂ (dividing by b₀b₂).
  -- From lc4: b₄²≥b₃b₅. So b₄/b₃ ≥ b₅/b₄ (dividing by b₃b₄).
  -- So (b₁/b₀)(b₄/b₃) ≥ (b₃/b₂)(b₅/b₄).
  -- Multiply: b₁b₄/(b₀b₃) ≥ b₃b₅/(b₂b₄).
  -- From lc3: b₃²≥b₂b₄ → b₃/b₂ ≥ b₄/b₃.
  -- Chain: b₁b₄/(b₀b₃) ≥ (b₃/b₂)(b₅/b₄) ≥ (b₄/b₃)(b₅/b₄) = b₅/b₃.
  -- So b₁b₄/b₀ ≥ b₅. I.e., b₁b₄ ≥ b₀b₅.
  -- In Lean: use division.
  have hb0 := le_of_lt (hb 0); have hb3 := hb 3; have hb4 := hb 4
  -- b₁b₂ ≥ b₀b₃ → b₁ ≥ b₀b₃/b₂
  have s1 : b 0 * b 3 ≤ b 1 * b 2 := by linarith [c1]
  -- b₄² ≥ b₃b₅ → b₄ ≥ b₃b₅/b₄ → b₄²/b₃ ≥ b₅
  have s2 : b 5 ≤ b 4 ^ 2 / b 3 := by rw [le_div_iff₀ hb3]; nlinarith
  -- b₁ ≥ b₀b₃/b₂
  have s3 : b 0 * b 3 / b 2 ≤ b 1 := by rw [div_le_iff₀ (hb 2)]; linarith
  -- b₁b₄ ≥ (b₀b₃/b₂)·b₄ and b₀b₅ ≤ b₀·b₄²/b₃
  -- b₁·b₄ ≥ b₀b₃b₄/b₂ and b₀b₅ ≤ b₀b₄²/b₃
  -- Need: b₀b₃b₄/b₂ ≥ b₀b₄²/b₃ iff b₃²/b₂ ≥ b₄ iff b₃² ≥ b₂b₄ ← lc3!
  have s4 : b 0 * b 5 ≤ b 0 * (b 4 ^ 2 / b 3) :=
    mul_le_mul_of_nonneg_left s2 hb0
  have s5 : b 0 * (b 4 ^ 2 / b 3) = b 0 * b 4 ^ 2 / b 3 := by ring
  have s6 : b 0 * b 4 ^ 2 / b 3 ≤ b 0 * b 3 * b 4 / b 2 := by
    rw [div_le_div_iff₀ hb3 (hb 2)]
    -- b₀b₄²·b₂ ≤ b₀b₃b₄·b₃ = b₀b₃²b₄
    -- iff b₄b₂ ≤ b₃² ← lc3
    -- Goal: b₀*b₄²*b₂ ≤ b₀*b₃*b₄*b₃ i.e. b₀b₄(b₄b₂) ≤ b₀b₄(b₃²)
    have hb04 : 0 ≤ b 0 * b 4 := mul_nonneg hb0 (le_of_lt hb4)
    have := mul_nonneg hb04 (by nlinarith [lc3] : b 3 ^ 2 - b 2 * b 4 ≥ 0)
    nlinarith
  have s7 : b 0 * b 3 * b 4 / b 2 ≤ b 1 * b 4 := by
    rw [div_le_iff₀ (hb 2)]
    nlinarith [mul_nonneg (le_of_lt hb4) (by linarith : b 1 * b 2 - b 0 * b 3 ≥ 0)]
  linarith

/-- c₃ ≥ 0: 2b₂b₃-b₁b₄-b₀b₅ = NI(2,3) + (b₁b₄-b₀b₅) + (b₂b₃-b₁b₄) ≥ 0. -/
theorem c3_nonneg (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) (h : IsLogConcave b) :
    2*(b 2 * b 3) - b 1 * b 4 - b 0 * b 5 ≥ 0 := by
  have ni23 : b 2 * b 3 ≥ b 1 * b 4 :=
    newton_step (b 1) (b 2) (b 3) (b 4) (le_of_lt (hb 1)) (hb 2) (hb 3) (le_of_lt (hb 4))
      (h 2 (by norm_num)) (h 3 (by norm_num))
  have ni14 := newton_three_step b hb h  -- b₁b₄ ≥ b₀b₅
  -- 2b₂b₃-b₁b₄-b₀b₅ = (b₂b₃-b₁b₄)+(b₂b₃-b₀b₅)
  -- ≥ 0 + (b₁b₄-b₀b₅) ≥ 0
  linarith

/-- First 4 Laguerre coefficients nonneg. -/
theorem laguerre_positivity_first4
    (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) (h : IsLogConcave b) :
    b 1 ^ 2 - b 0 * b 2 ≥ 0 ∧
    b 1 * b 2 - b 0 * b 3 ≥ 0 ∧
    b 2 ^ 2 - b 0 * b 4 ≥ 0 ∧
    2*(b 2 * b 3) - b 1 * b 4 - b 0 * b 5 ≥ 0 :=
  ⟨c0_nonneg b h, c1_nonneg b hb h, c2_nonneg b hb h, c3_nonneg b hb h⟩

/-- Gaussian zeroes. -/
theorem gaussian_c0 : (1:ℝ)^2 - 1*(1/2) = 1/2 := by norm_num
theorem gaussian_c1 : 2*(1:ℝ)*(1/2) - 6*1*(1/6) = 0 := by norm_num

/-! ## Summary

PROVED (all 0 sorry):
  newton_step: b₁²≥b₀b₂, b₂²≥b₁b₃ → b₁b₂≥b₀b₃
  newton_two_step: b₁b₃≥b₀b₄ (iterated)
  newton_three_step: b₁b₄≥b₀b₅ (iterated)
  c0_nonneg: LC(1) ≥ 0
  c1_nonneg: NI(1,2) ≥ 0
  c2_nonneg: LC(2)+NI(1,3) ≥ 0
  c3_nonneg: NI(2,3)+NI(1,4) ≥ 0
  laguerre_positivity_first4: all four combined

PATH TO RH:
  Step 1: c_n ≥ 0 for all n [this file: proved n≤3]
  Step 2: T_k(Xi) ≥ (k+1)/k [analysis]
  Step 3: Laguerre's theorem [classical]
  Step 4: PF∞ → RH [categorical_rh]
-/

end CausalAlgebraicGeometry.LaguerrePositivity
