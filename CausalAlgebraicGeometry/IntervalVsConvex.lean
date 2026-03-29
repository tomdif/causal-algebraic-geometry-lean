/-
  IntervalVsConvex.lean — Intervals are a vanishing fraction of convex subsets

  For the grid [m]², the number of order-intervals (closed intervals [a,b]
  where a ≤ b componentwise, plus the empty set) grows polynomially in m,
  while the number of order-convex subsets grows exponentially (Θ(16^m)).

  Key results:
  1. numGridIntervals_le: |Int([m]²)| ≤ m⁴ + 1  (polynomial upper bound)
  2. numGridConvex_ge_two_pow: |CC([m]²)| ≥ 2^m  (exponential lower bound)
  3. intervals_lt_convex: for m ≥ 2, numGridIntervals m < numGridConvex m m
  4. Concrete computations at m = 2, 3, 4

  This demonstrates that an interval-only theory (capturing only comparable pairs)
  would miss almost all of the algebraic-geometric structure that CSpec captures
  through general convex subsets.

  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.RhoEquals16
import CausalAlgebraicGeometry.TightUpperBound

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.IntervalVsConvex

open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GridClassification
open CausalAlgebraicGeometry.TightUpperBound
open CausalAlgebraicGeometry.RhoEquals16

/-! ## Order-intervals in the grid -/

/-- An order-interval in [m]²: the set {c : a ≤ c ≤ b} for some a, b. -/
def gridInterval (m : ℕ) (a b : Fin m × Fin m) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun c => GridLE m m a c ∧ GridLE m m c b

/-- The set of all nonempty order-intervals in [m]². -/
def nonemptyIntervals (m : ℕ) : Finset (Finset (Fin m × Fin m)) :=
  ((Finset.univ : Finset (Fin m × Fin m)) ×ˢ Finset.univ).image
    (fun p => gridInterval m p.1 p.2) |>.filter (fun S => S.Nonempty)

/-- The set of all order-intervals in [m]² (including ∅). -/
def allIntervals (m : ℕ) : Finset (Finset (Fin m × Fin m)) :=
  Insert.insert ∅ (nonemptyIntervals m)

/-- The number of distinct order-intervals (including ∅). -/
def numGridIntervals (m : ℕ) : ℕ := (allIntervals m).card

/-! ## Every interval is convex -/

/-- Every order-interval is grid-convex. -/
theorem gridInterval_isConvex (m : ℕ) (a b : Fin m × Fin m) :
    IsGridConvex m m (gridInterval m a b) := by
  intro x hx y hy hxy z hxz hzy
  simp only [gridInterval, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
  exact ⟨⟨le_trans hx.1.1 hxz.1, le_trans hx.1.2 hxz.2⟩,
         ⟨le_trans hzy.1 hy.2.1, le_trans hzy.2 hy.2.2⟩⟩

/-! ## Polynomial upper bound on intervals -/

/-- The number of grid-intervals is at most m⁴ + 1. -/
theorem numGridIntervals_le (m : ℕ) : numGridIntervals m ≤ m ^ 4 + 1 := by
  unfold numGridIntervals allIntervals
  calc (Insert.insert ∅ (nonemptyIntervals m)).card
      ≤ (nonemptyIntervals m).card + 1 := Finset.card_insert_le ∅ _
    _ ≤ m ^ 4 + 1 := by
        apply Nat.add_le_add_right
        unfold nonemptyIntervals
        calc (((Finset.univ : Finset (Fin m × Fin m)) ×ˢ Finset.univ).image
              (fun p => gridInterval m p.1 p.2) |>.filter (fun S => S.Nonempty)).card
            ≤ (((Finset.univ : Finset (Fin m × Fin m)) ×ˢ Finset.univ).image
              (fun p => gridInterval m p.1 p.2)).card :=
                Finset.card_filter_le _ _
          _ ≤ ((Finset.univ : Finset (Fin m × Fin m)) ×ˢ Finset.univ).card :=
                Finset.card_image_le
          _ = Fintype.card (Fin m × Fin m) * Fintype.card (Fin m × Fin m) := by
                simp [Finset.card_product]
          _ = (m * m) * (m * m) := by
                simp [Fintype.card_prod, Fintype.card_fin]
          _ = m ^ 4 := by ring

/-! ## Concrete computations: the gap is already visible at small m -/

theorem numGridConvex_val_2 : numGridConvex 2 2 = 13 := by native_decide
theorem numGridConvex_val_3 : numGridConvex 3 3 = 114 := by native_decide
theorem numGridIntervals_val_2 : numGridIntervals 2 = 10 := by native_decide
theorem numGridIntervals_val_3 : numGridIntervals 3 = 37 := by native_decide

/-- At m = 2: 10 intervals vs 13 convex subsets (23% non-interval). -/
theorem interval_lt_convex_2 : numGridIntervals 2 < numGridConvex 2 2 := by native_decide

/-- At m = 3: 37 intervals vs 114 convex subsets (68% non-interval). -/
theorem interval_lt_convex_3 : numGridIntervals 3 < numGridConvex 3 3 := by native_decide

/-- At m = 4: the gap widens further. -/
theorem interval_lt_convex_4 : numGridIntervals 4 < numGridConvex 4 4 := by native_decide

/-! ## Exponential lower bound on convex subsets -/

/-- 2^m ≤ C(2m, m) for all m, by induction using Pascal + symmetry. -/
theorem two_pow_le_choose (m : ℕ) : 2 ^ m ≤ Nat.choose (2 * m) m := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hsymm : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n :=
      Nat.choose_symm_half n
    have hmono : Nat.choose (2 * n) n ≤ Nat.choose (2 * n + 1) n :=
      Nat.choose_le_succ (2 * n) n
    have hpascal : Nat.choose (2 * n + 2) (n + 1) =
      Nat.choose (2 * n + 1) n + Nat.choose (2 * n + 1) (n + 1) :=
      Nat.choose_succ_succ (2 * n + 1) n
    have hgoal : 2 ^ n * 2 ≤ Nat.choose (2 * n + 2) (n + 1) := by
      rw [hpascal, hsymm]; linarith
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
    linarith [pow_succ 2 n]

/-- 2 * (n + 6) ≤ 2^(n+5) for all n. -/
private theorem two_times_add6_le : ∀ n : ℕ, 2 * (n + 6) ≤ 2 ^ (n + 5) := by
  intro n; induction n with
  | zero => norm_num
  | succ k ih => linarith [show 2 ^ (k + 6) = 2 * 2 ^ (k + 5) from by ring]

/-- For m ≥ 1, 2^m ≤ numGridConvex m m. -/
theorem numGridConvex_ge_two_pow (m : ℕ) (hm : 1 ≤ m) : 2 ^ m ≤ numGridConvex m m := by
  match m with
  | 0 => omega
  | 1 => show 2 ≤ numGridConvex 1 1; native_decide
  | 2 => show 4 ≤ numGridConvex 2 2; native_decide
  | 3 => show 8 ≤ numGridConvex 3 3; native_decide
  | 4 => show 16 ≤ numGridConvex 4 4; native_decide
  | n + 5 =>
    have h2m : 0 < 2 * (n + 5 + 1) := by omega
    suffices h : 2 ^ (n + 5) ≤ Nat.choose (2 * (n + 5)) (n + 5) ^ 2 / (2 * (n + 5 + 1)) from
      le_trans h (numGridConvex_ge_catalan_bound (n + 5))
    rw [Nat.le_div_iff_mul_le h2m]
    have hc := two_pow_le_choose (n + 5)
    have h2n6 : 2 * (n + 6) ≤ 2 ^ (n + 5) := two_times_add6_le n
    calc 2 ^ (n + 5) * (2 * (n + 5 + 1))
        = 2 ^ (n + 5) * (2 * (n + 6)) := by ring
      _ ≤ Nat.choose (2 * (n + 5)) (n + 5) * Nat.choose (2 * (n + 5)) (n + 5) := by
          apply Nat.mul_le_mul
          · exact hc
          · exact le_trans h2n6 hc
      _ = Nat.choose (2 * (n + 5)) (n + 5) ^ 2 := by ring

/-! ## Polynomial vs exponential: the ratio vanishes -/

/-- For m ≥ 17, m⁴ + 1 < 2^m (polynomial < exponential). -/
theorem pow4_lt_exp (m : ℕ) (hm : 17 ≤ m) : m ^ 4 + 1 < 2 ^ m := by
  suffices h : ∀ k, (k + 17) ^ 4 + 1 < 2 ^ (k + 17) by
    have := h (m - 17)
    have hm17 : m - 17 + 17 = m := by omega
    rw [hm17] at this
    exact this
  intro k; induction k with
  | zero => norm_num
  | succ j ih =>
    have ht : j + 17 ≥ 17 := by omega
    have h2 : (j + 17) ^ 2 ≥ 289 := by nlinarith
    have h3 : (j + 17) ^ 3 ≥ 4913 := by nlinarith
    have hstep : (j + 18) ^ 4 < 2 * (j + 17) ^ 4 := by nlinarith
    have h2pow : 2 ^ (j + 1 + 17) = 2 * 2 ^ (j + 17) := by ring
    linarith

/-! ## The main structural theorem -/

/-- For m ≥ 5, m⁴ + 1 < C(2m,m)²/(2(m+1)), used to bridge
    the polynomial interval bound to the Catalan lower bound on convex subsets. -/
private theorem pow4_lt_catalan_aux (m : ℕ) (hm5 : 5 ≤ m) (hm16 : m ≤ 16) :
    m ^ 4 + 1 < Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) := by
  interval_cases m <;> native_decide

/-- For m ≥ 2, intervals are strictly fewer than convex subsets.
    Uses native_decide for m = 2, 3, 4, the Catalan bound for m = 5..16,
    and the polynomial-vs-exponential bound for m ≥ 17. -/
theorem intervals_lt_convex (m : ℕ) (hm : 2 ≤ m) :
    numGridIntervals m < numGridConvex m m := by
  by_cases h17 : 17 ≤ m
  · calc numGridIntervals m
        ≤ m ^ 4 + 1 := numGridIntervals_le m
      _ < 2 ^ m := pow4_lt_exp m h17
      _ ≤ numGridConvex m m := numGridConvex_ge_two_pow m (by omega)
  · by_cases h5 : 5 ≤ m
    · calc numGridIntervals m
          ≤ m ^ 4 + 1 := numGridIntervals_le m
        _ < Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) :=
            pow4_lt_catalan_aux m h5 (by omega)
        _ ≤ numGridConvex m m := numGridConvex_ge_catalan_bound m
    · -- m ∈ {2, 3, 4}
      interval_cases m <;> native_decide

/-! ## Summary

  The dimension-theoretic interpretation:

  dim_CSpec([m]²) = log₁₆(numGridConvex m m) ~ m  (grows linearly)
  dim_Int([m]²) = log(numGridIntervals m) ≤ 4 log(m)  (grows logarithmically)

  So CSpec sees m-dimensional geometry where intervals see only log(m)-dimensional.
  The interval theory is dimensionally blind to the true algebraic geometry.

  Concrete data:
    m=2: intervals/convex = 10/13 ≈ 77%
    m=3: intervals/convex = 37/114 ≈ 32%
    m→∞: intervals/convex → 0 (polynomial/exponential → 0)
-/

/-- Intervals grow at most polynomially: bounded by m⁴ + 1. -/
theorem interval_polynomial_bound (m : ℕ) : numGridIntervals m ≤ m ^ 4 + 1 :=
  numGridIntervals_le m

/-- Convex subsets grow exponentially: at least 2^m for m ≥ 1. -/
theorem convex_exponential_bound (m : ℕ) (hm : 1 ≤ m) : 2 ^ m ≤ numGridConvex m m :=
  numGridConvex_ge_two_pow m hm

/-- Convex subsets bounded above by 16^m. -/
theorem convex_upper_bound (m : ℕ) : numGridConvex m m ≤ 16 ^ m :=
  numGridConvex_le_sixteen_pow m

end CausalAlgebraicGeometry.IntervalVsConvex
