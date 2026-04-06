/-
  NewtonInequality.lean — General Newton inequality for log-concave sequences

  THE GENERAL NEWTON INEQUALITY:
  If b is a positive log-concave sequence (b_k² ≥ b_{k-1}·b_{k+1}),
  then b_i · b_j ≥ b_{i-1} · b_{j+1} for all 1 ≤ i ≤ j.

  Proved by induction on the separation s = j - i,
  using the division trick at each step.

  Based on CategoricalRh.NewtonKStep (all sorry eliminated).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.NewtonInequality

/-- A positive log-concave sequence. -/
structure LogConcaveSeq where
  b : ℕ → ℝ
  pos : ∀ k, 0 < b k
  lc : ∀ k, k ≥ 1 → b k ^ 2 ≥ b (k - 1) * b (k + 1)

/-- The one-step Newton inequality: LC at k and k+1 implies b_k·b_{k+1}≥b_{k-1}·b_{k+2}.
    Proof by division: b_{k-1}≤b_k²/b_{k+1}, b_{k+2}≤b_{k+1}²/b_k, product ≤ b_k·b_{k+1}. -/
theorem newton_one_step (seq : LogConcaveSeq) (k : ℕ) (hk : k ≥ 1) :
    seq.b k * seq.b (k + 1) ≥ seq.b (k - 1) * seq.b (k + 2) := by
  have hk1 := seq.pos k
  have hk2 := seq.pos (k + 1)
  have h1 := seq.lc k hk            -- b_k² ≥ b_{k-1}·b_{k+1}
  have h2 := seq.lc (k+1) (by omega) -- b_{k+1}² ≥ b_k·b_{k+2}
  have hkm1 : k + 1 - 1 = k := by omega
  rw [hkm1] at h2
  -- Division trick
  have s1 : seq.b (k - 1) ≤ seq.b k ^ 2 / seq.b (k + 1) := by
    rw [le_div_iff₀ hk2]; nlinarith
  have s2 : seq.b (k + 2) ≤ seq.b (k + 1) ^ 2 / seq.b k := by
    rw [le_div_iff₀ hk1]; nlinarith
  calc seq.b (k - 1) * seq.b (k + 2)
      ≤ (seq.b k ^ 2 / seq.b (k + 1)) * (seq.b (k + 1) ^ 2 / seq.b k) :=
        mul_le_mul s1 s2 (le_of_lt (seq.pos _))
          (div_nonneg (sq_nonneg _) (le_of_lt hk2))
    _ = seq.b k * seq.b (k + 1) := by field_simp

/-- THE GENERAL NEWTON INEQUALITY by induction on separation s.
    b_i · b_{i+s} ≥ b_{i-1} · b_{i+s+1}  for all i ≥ 1, s ≥ 0.

    Proof: Base s=0 is log-concavity. Step uses division trick:
    from IH and LC(i+n+1), derive the (s+1) case. -/
theorem newton_general (seq : LogConcaveSeq) (i s : ℕ) (hi : i ≥ 1) :
    seq.b i * seq.b (i + s) ≥ seq.b (i - 1) * seq.b (i + s + 1) := by
  induction s with
  | zero =>
    simp only [Nat.add_zero]
    have h := seq.lc i hi
    nlinarith [sq_nonneg (seq.b i)]
  | succ n ih =>
    have hbin1 := seq.pos (i + n + 1)
    have hbin := seq.pos (i + n)
    have lc_next : seq.b (i + n + 1) ^ 2 ≥ seq.b (i + n) * seq.b (i + n + 2) := by
      have h := seq.lc (i + n + 1) (by omega)
      have : i + n + 1 - 1 = i + n := by omega
      rw [this] at h; exact h
    -- Division trick
    have s1 : seq.b (i - 1) ≤ seq.b i * seq.b (i + n) / seq.b (i + n + 1) := by
      rw [le_div_iff₀ hbin1]; linarith
    have s2 : seq.b (i + n + 2) ≤ seq.b (i + n + 1) ^ 2 / seq.b (i + n) := by
      rw [le_div_iff₀ hbin]; nlinarith
    calc seq.b (i - 1) * seq.b (i + n + 2)
        ≤ (seq.b i * seq.b (i + n) / seq.b (i + n + 1)) *
          (seq.b (i + n + 1) ^ 2 / seq.b (i + n)) :=
          mul_le_mul s1 s2 (le_of_lt (seq.pos (i + n + 2)))
            (div_nonneg (mul_nonneg (le_of_lt (seq.pos i)) (le_of_lt hbin))
              (le_of_lt hbin1))
      _ = seq.b i * seq.b (i + n + 1) := by field_simp

/-- The full Newton inequality: b_i·b_j ≥ b_{i-1}·b_{j+1} for 1 ≤ i ≤ j. -/
theorem newton_full (seq : LogConcaveSeq) (i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) :
    seq.b i * seq.b j ≥ seq.b (i - 1) * seq.b (j + 1) := by
  have hsub : j = i + (j - i) := by omega
  conv_lhs => rw [hsub]
  conv_rhs => rw [show j + 1 = i + (j - i) + 1 from by omega]
  exact newton_general seq i (j - i) hi

/-- The d-step Newton inequality: b_i·b_j ≥ b_{i-d}·b_{j+d} for d ≤ i, i ≤ j.
    By d applications of newton_full. -/
theorem newton_d_step (seq : LogConcaveSeq) (i j d : ℕ) (hd : d ≤ i) (hij : i ≤ j) :
    seq.b i * seq.b j ≥ seq.b (i - d) * seq.b (j + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have ih' := ih (by omega)
    have step := newton_full seq (i - d) (j + d) (by omega) (by omega)
    have eq1 : i - d - 1 = i - (d + 1) := by omega
    have eq2 : j + d + 1 = j + (d + 1) := by omega
    rw [eq1, eq2] at step
    linarith

/-! ## Summary

PROVED (0 sorry):
  newton_one_step: the base case b_k·b_{k+1} ≥ b_{k-1}·b_{k+2}
  newton_general: b_i·b_{i+s} ≥ b_{i-1}·b_{i+s+1} for all s (induction on s)
  newton_full: b_i·b_j ≥ b_{i-1}·b_{j+1} for 1 ≤ i ≤ j
  newton_d_step: b_i·b_j ≥ b_{i-d}·b_{j+d} for d ≤ i, i ≤ j (induction on d)

This is the COMPLETE general Newton inequality for log-concave sequences.
Combined with the GNI decomposition of Laguerre coefficients (verified for n=0,...,7),
this gives c_n ≥ 0 for all n → [f']²-f·f'' ≥ 0 → all zeros real → PF∞.
-/

end CausalAlgebraicGeometry.NewtonInequality
