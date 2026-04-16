/-
  LaguerreSorry.lean — Full proof that laguerreSum ≥ 0

  PROOF: Abel summation + symmetrization via Finset.sum_range_reflect.
  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option maxHeartbeats 1600000

namespace CausalAlgebraicGeometry.LaguerreSorry

open Finset

-- newton_general: PROVED
theorem newton_general (b : ℕ → ℝ) (hb : ∀ k, 0 < b k)
    (hlc : ∀ k, k ≥ 1 → b k ^ 2 ≥ b (k - 1) * b (k + 1))
    (i s : ℕ) (hi : i ≥ 1) :
    b i * b (i + s) ≥ b (i - 1) * b (i + s + 1) := by
  induction s with
  | zero =>
    simp only [Nat.add_zero]
    nlinarith [hlc i hi, sq_nonneg (b i)]
  | succ n ih =>
    have hbin1 := hb (i + n + 1)
    have hbin := hb (i + n)
    have lc_next : b (i + n + 1) ^ 2 ≥ b (i + n) * b (i + n + 2) := by
      have h := hlc (i + n + 1) (by omega)
      rw [show i + n + 1 - 1 = i + n from by omega] at h; exact h
    have s1 : b (i - 1) ≤ b i * b (i + n) / b (i + n + 1) := by
      rw [le_div_iff₀ hbin1]; linarith
    have s2 : b (i + n + 2) ≤ b (i + n + 1) ^ 2 / b (i + n) := by
      rw [le_div_iff₀ hbin]; nlinarith
    calc b (i - 1) * b (i + n + 2)
        ≤ (b i * b (i + n) / b (i + n + 1)) *
          (b (i + n + 1) ^ 2 / b (i + n)) :=
          mul_le_mul s1 s2 (le_of_lt (hb (i + n + 2)))
            (div_nonneg (mul_nonneg (le_of_lt (hb i)) (le_of_lt hbin))
              (le_of_lt hbin1))
      _ = b i * b (i + n + 1) := by field_simp

-- g_ascending: PROVED
theorem g_ascending (b : ℕ → ℝ) (n l : ℕ)
    (hb : ∀ k, 0 < b k)
    (hlc : ∀ k, k ≥ 1 → b k ^ 2 ≥ b (k - 1) * b (k + 1))
    (hl : 2 * l ≤ n) :
    b l * b (n + 2 - l) ≤ b (l + 1) * b (n + 1 - l) := by
  have key := newton_general b hb hlc (l + 1) (n - 2 * l) (by omega)
  rw [show b (l + 1 + (n - 2 * l)) = b (n + 1 - l) from congrArg b (by omega),
      show b (l + 1 - 1) = b l from congrArg b (by omega),
      show b (l + 1 + (n - 2 * l) + 1) = b (n + 2 - l) from congrArg b (by omega)] at key
  linarith

-- Abel summation: PROVED by induction
private theorem abel_sum (a g : ℕ → ℝ) : ∀ n : ℕ,
    ∑ l ∈ range (n + 1), a l * (g (l + 1) - g l) =
    a n * g (n + 1) - a 0 * g 0 +
    ∑ l ∈ range n, (a l - a (l + 1)) * g (l + 1) := by
  intro n; induction n with
  | zero => simp; ring
  | succ m ih => rw [sum_range_succ, ih, sum_range_succ]; ring

-- THE MAIN THEOREM
theorem laguerreSum_nonneg (b : ℕ → ℝ) (hb : ∀ k, 0 < b k)
    (hlc : ∀ k, k ≥ 1 → b k ^ 2 ≥ b (k - 1) * b (k + 1))
    (n : ℕ) :
    ∑ l ∈ range (n + 1),
      (Nat.choose n l : ℝ) * (b (l+1) * b (n+2-(l+1)) - b l * b (n+2-l)) ≥ 0 := by
  -- Define g(k) = b(k)*b(n+2-k) and a(l) = C(n,l).
  set g : ℕ → ℝ := fun k => b k * b (n + 2 - k)
  set a : ℕ → ℝ := fun l => (Nat.choose n l : ℝ)
  -- Our sum equals Σ a(l)*(g(l+1)-g(l)):
  have hconv : ∀ l ∈ range (n + 1),
      (Nat.choose n l : ℝ) * (b (l+1) * b (n+2-(l+1)) - b l * b (n+2-l)) =
      a l * (g (l + 1) - g l) := by
    intro l hl; simp only [a, g]
  rw [show ∑ l ∈ range (n+1), (Nat.choose n l : ℝ) * (b (l+1) * b (n+2-(l+1)) - b l * b (n+2-l))
      = ∑ l ∈ range (n+1), a l * (g (l+1) - g l) from sum_congr rfl hconv]
  -- Apply Abel summation
  rw [abel_sum a g n]
  -- Need: boundary + interior ≥ 0
  -- Boundary: a(n)*g(n+1) - a(0)*g(0) ≥ 0
  have hbdry : a n * g (n + 1) - a 0 * g 0 ≥ 0 := by
    simp only [a, g, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have key := newton_general b hb hlc 1 n (le_refl 1)
    rw [show b (1 - 1) = b 0 from congrArg b (by omega),
        show b (1 + n) = b (n + 1) from congrArg b (by omega),
        show b (1 + n + 1) = b (n + 2) from congrArg b (by omega)] at key
    have h1 : n + 2 - (n + 1) = 1 := by omega
    have h2 : n + 2 - 0 = n + 2 := by omega
    simp only [h1, h2]; nlinarith [mul_comm (b 1) (b (n + 1))]
  -- Interior: ∑ (a(l)-a(l+1))*g(l+1) ≥ 0
  suffices hint : ∑ l ∈ range n, (a l - a (l + 1)) * g (l + 1) ≥ 0 by linarith
  -- Prove 2*interior ≥ 0 via symmetrization
  suffices h2 : 2 * ∑ l ∈ range n, (a l - a (l + 1)) * g (l + 1) ≥ 0 by linarith
  -- KEY STEP: reflect the sum.
  -- sum_range_reflect gives: Σ F(n-1-l) = Σ F(l) for F(l) = (a(l)-a(l+1))*g(l+1).
  -- F(n-1-l) = (a(n-1-l) - a(n-1-l+1)) * g(n-1-l+1)
  -- For l < n: n-1-l+1 = n-l. So F(n-1-l) = (a(n-1-l)-a(n-l))*g(n-l).
  -- And a(n-1-l)-a(n-l) = C(n,n-1-l)-C(n,n-l) = C(n,l+1)-C(n,l) = -(a(l)-a(l+1)).
  -- So F(n-1-l) = -(a(l)-a(l+1))*g(n-l).
  -- Therefore: I = Σ F(l) = Σ F(n-1-l) = -Σ (a(l)-a(l+1))*g(n-l).
  -- 2I = Σ (a(l)-a(l+1))*(g(l+1) - g(n-l)).
  -- Step 1: reflect and simplify indices
  set F : ℕ → ℝ := fun l => (a l - a (l + 1)) * g (l + 1)
  have hF_reflect : ∀ l ∈ range n,
      F (n - 1 - l) = -(a l - a (l + 1)) * g (n - l) := by
    intro l hl; rw [mem_range] at hl
    simp only [F]
    -- a(n-1-l) - a(n-1-l+1) = a(n-1-l) - a(n-l)
    have h_idx : n - 1 - l + 1 = n - l := by omega
    rw [h_idx]
    -- a(n-1-l) - a(n-l) = -(a(l) - a(l+1)) by binomial symmetry
    have h_sym1 : a (n - 1 - l) = a (l + 1) := by
      simp only [a]; congr 1
      have := Nat.choose_symm (show l + 1 ≤ n by omega)
      rw [show n - (l + 1) = n - 1 - l from by omega] at this
      exact this
    have h_sym2 : a (n - l) = a l := by
      simp only [a]; congr 1
      rw [Nat.choose_symm (show l ≤ n by omega)]
    rw [h_sym1, h_sym2]; ring
  -- Step 2: I = Σ F(n-1-l)  (by sum_range_reflect)
  have hI_eq : ∑ l ∈ range n, F l = ∑ l ∈ range n, F (n - 1 - l) :=
    (sum_range_reflect F n).symm
  -- Step 3: Σ F(n-1-l) = -Σ (a(l)-a(l+1))*g(n-l)
  have hI_neg : ∑ l ∈ range n, F (n - 1 - l) =
      -(∑ l ∈ range n, (a l - a (l + 1)) * g (n - l)) := by
    conv_rhs => rw [show -(∑ l ∈ range n, (a l - a (l + 1)) * g (n - l)) =
      ∑ l ∈ range n, (-(a l - a (l + 1)) * g (n - l)) from by
      rw [← Finset.sum_neg_distrib]; congr 1; ext l; ring]
    apply sum_congr rfl; intro l hl; exact hF_reflect l hl
  -- Step 4: 2I = Σ (a(l)-a(l+1))*(g(l+1)-g(n-l))
  have h2I : 2 * ∑ l ∈ range n, F l =
      ∑ l ∈ range n, ((a l - a (l + 1)) * (g (l + 1) - g (n - l))) := by
    have : ∑ l ∈ range n, F l = -(∑ l ∈ range n, (a l - a (l + 1)) * g (n - l)) := by
      rw [hI_eq, hI_neg]
    -- 2I = I + I. Use def of F for first copy, key for second.
    have eq1 : ∑ l ∈ range n, F l + ∑ l ∈ range n, F l =
        ∑ l ∈ range n, (a l - a (l+1)) * g (l+1) -
        ∑ l ∈ range n, (a l - a (l+1)) * g (n - l) := by rw [this]; ring
    have eq2 : ∑ l ∈ range n, (a l - a (l+1)) * g (l+1) -
        ∑ l ∈ range n, (a l - a (l+1)) * g (n - l) =
        ∑ l ∈ range n, ((a l - a (l+1)) * (g (l+1) - g (n - l))) := by
      rw [← sum_sub_distrib]; congr 1; ext l; ring
    linarith [eq1, eq2]
  rw [show (∑ l ∈ range n, (a l - a (l + 1)) * g (l + 1)) =
      ∑ l ∈ range n, F l from rfl]
  rw [h2I]
  -- Step 5: each term ≥ 0
  apply sum_nonneg
  intro l hl; rw [mem_range] at hl
  -- Term = (C(n,l)-C(n,l+1)) * (g(l+1)-g(n-l))
  -- = (C(n,l)-C(n,l+1)) * (b(l+1)*b(n+1-l) - b(n-l)*b(l+2))
  by_cases h2l : 2 * l ≥ n
  · -- Case 2l ≥ n: coeff ≥ 0 and value ≥ 0
    apply mul_nonneg
    · -- C(n,l) ≥ C(n,l+1)
      simp only [a]; push_cast
      -- C(n,l) ≥ C(n,l+1) when l ≥ n/2
      -- Use symmetry: C(n,l) = C(n,n-l) and C(n,l+1) = C(n,n-l-1).
      -- Then C(n,n-l-1) ≤ C(n,n-l) from choose_le_succ_of_lt_half_left
      -- since n-l-1 < n/2 when l ≥ n/2.
      -- C(n, n-l-1) ≤ C(n, n-l) by choose_le_succ since n-l-1 < n/2
      -- C(n, n-l-1) = C(n, l+1) by symmetry, C(n, n-l) = C(n, l) by symmetry
      have hmono := Nat.choose_le_succ_of_lt_half_left (show n - l - 1 < n / 2 by omega)
      -- hmono : C(n, n-l-1) ≤ C(n, n-l-1+1) = C(n, n-l)
      have hsym_nl : Nat.choose n (n - l) = Nat.choose n l :=
        Nat.choose_symm (show l ≤ n by omega)
      have h_idx : n - l - 1 + 1 = n - l := by omega
      rw [h_idx] at hmono
      -- hmono : C(n, n-l-1) ≤ C(n, n-l) = C(n, l)
      rw [hsym_nl] at hmono
      -- hmono : C(n, n-l-1) ≤ C(n, l)
      have hsym_nl1 : Nat.choose n (n - l - 1) = Nat.choose n (l + 1) := by
        have := Nat.choose_symm (show l + 1 ≤ n by omega)
        rwa [show n - (l + 1) = n - l - 1 from by omega] at this
      rw [hsym_nl1] at hmono
      -- hmono : C(n, l+1) ≤ C(n, l)
      have : (Nat.choose n (l + 1) : ℝ) ≤ (Nat.choose n l : ℝ) := Nat.cast_le.mpr hmono
      linarith
    · -- g(l+1) ≥ g(n-l)
      simp only [g]
      have key := newton_general b hb hlc (n + 1 - l) (2 * l - n) (by omega)
      rw [show b (n + 1 - l + (2 * l - n)) = b (l + 1) from congrArg b (by omega),
          show b (n + 1 - l - 1) = b (n - l) from congrArg b (by omega),
          show b (n + 1 - l + (2 * l - n) + 1) = b (l + 2) from congrArg b (by omega)] at key
      have h1 : n + 2 - (l + 1) = n + 1 - l := by omega
      have h2 : n + 2 - (n - l) = l + 2 := by omega
      rw [h1, h2]; nlinarith [mul_comm (b (n + 1 - l)) (b (l + 1))]
  · -- Case 2l < n: coeff ≤ 0 and value ≤ 0 → product ≥ 0
    push_neg at h2l
    rw [mul_nonneg_iff]; right; constructor
    · -- C(n,l) ≤ C(n,l+1), i.e., a(l) - a(l+1) ≤ 0
      simp only [a]; push_cast
      by_cases hlt : l < n / 2
      · -- l < n/2: direct from choose_le_succ
        have hmono := Nat.choose_le_succ_of_lt_half_left hlt
        have : (Nat.choose n l : ℝ) ≤ (Nat.choose n (l+1) : ℝ) := Nat.cast_le.mpr hmono
        linarith
      · -- l = n/2 (n odd, 2l = n-1): C(n,l) = C(n,l+1) by symmetry
        push_neg at hlt
        have hsym := Nat.choose_symm (show l + 1 ≤ n by omega)
        rw [show n - (l + 1) = l from by omega] at hsym
        have : (Nat.choose n l : ℝ) = (Nat.choose n (l+1) : ℝ) := by exact_mod_cast hsym
        linarith
    · -- g(l+1) ≤ g(n-l), i.e., b(l+1)*b(n+1-l) ≤ b(n-l)*b(l+2)
      simp only [g]
      -- Use newton_general: b(l+2)*b(n-l) ≥ b(l+1)*b(n+1-l)
      -- when 2l+2 ≤ n (i.e., 2l < n, hence n-2l-2 ≥ 0)
      -- Edge case: 2l = n-1 → n-2l-2 = -1 in ℕ → need separate handling
      by_cases hlt2 : 2 * l + 2 ≤ n
      · have key := newton_general b hb hlc (l + 2) (n - 2 * l - 2) (by omega)
        rw [show b (l + 2 + (n - 2 * l - 2)) = b (n - l) from congrArg b (by omega),
            show b (l + 2 - 1) = b (l + 1) from congrArg b (by omega),
            show b (l + 2 + (n - 2 * l - 2) + 1) = b (n + 1 - l) from congrArg b (by omega)] at key
        have h1 : n + 2 - (l + 1) = n + 1 - l := by omega
        have h2 : n + 2 - (n - l) = l + 2 := by omega
        rw [h1, h2]; nlinarith [mul_comm (b (l + 2)) (b (n - l))]
      · -- 2l+2 > n, combined with 2l < n → 2l = n-1 → n-l = l+1
        have heq : n - l = l + 1 := by omega
        have h1 : n + 2 - (l + 1) = n + 1 - l := by omega
        have h2 : n + 2 - (n - l) = l + 2 := by omega
        rw [h1, h2, heq]
        -- Need: b(l+1)*b(n+1-l) ≤ b(l+1)*b(l+2)
        -- i.e., b(n+1-l) ≤ b(l+2). But n+1-l = l+2 (since 2l=n-1 → n+1-l = l+2).
        have : n + 1 - l = l + 2 := by omega
        rw [this]; linarith

end CausalAlgebraicGeometry.LaguerreSorry
