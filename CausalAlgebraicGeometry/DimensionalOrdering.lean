/-
  DimensionalOrdering.lean — Three-way dimensional ordering: chain < grid < antichain

  For the m×m grid (m ≥ 2), we prove a strict ordering of Noetherian ratios:

    γ(chain_{m²}) < γ([m]²) < γ(antichain_{m²})

  where γ = |ConvexSubsets| / |IntervalSubsets| (both including the empty set).

  Key facts:
  - γ(chain) = 1 for any chain (every convex subset is an interval)
  - γ(grid) > 1 for m ≥ 2 (from intervals_lt_convex in IntervalVsConvex.lean)
  - γ(antichain_n) = 2^n / (n+1) (every subset is convex, intervals are singletons + ∅)

  The first inequality follows directly from intervals_lt_convex.
  The second uses:
  - m = 2, 3, 4: native_decide on exact counts
  - m = 5: numGridConvex ≤ C(10,5)² = 63504, then 63504 · 26 < 2^25
  - m ≥ 6: 16^m · (m²+1) < 2^(m²) by induction

  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.IntervalVsConvex

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.DimensionalOrdering

open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GridClassification
open CausalAlgebraicGeometry.IntervalVsConvex
open CausalAlgebraicGeometry.TightUpperBound
open CausalAlgebraicGeometry.RhoEquals16

/-! ## Part 1: γ(chain) < γ(grid) for m ≥ 2

  For any chain (total order), every convex subset is an interval, so γ = 1.
  For the grid [m]², numGridIntervals m < numGridConvex m m for m ≥ 2,
  which means γ(grid) > 1 = γ(chain). -/

/-- **γ(chain) < γ(grid)**: For the m×m grid (m ≥ 2), the Noetherian ratio of
    any chain on m² elements is strictly less than that of the grid.

    Since γ(chain) = 1 (every convex set is an interval in a total order),
    this reduces to showing γ(grid) > 1, i.e., numGridIntervals < numGridConvex. -/
theorem gamma_chain_lt_grid (m : ℕ) (hm : 2 ≤ m) :
    numGridIntervals m < numGridConvex m m :=
  intervals_lt_convex m hm

/-! ## Part 2: γ(grid) < γ(antichain) for m ≥ 2

  The antichain on n = m² elements has:
  - numConvex = 2^n (every subset is convex)
  - numIntervals = n + 1 (n singletons plus the empty set)

  So γ(antichain) = 2^(m²) / (m² + 1).

  Cross-multiplied: numGridConvex m m · (m² + 1) < 2^(m²) · numGridIntervals m. -/

/-! ### Arithmetic: 16^m · (m²+1) < 2^(m²) for m ≥ 6 -/

/-- For n ≥ 2, n²+2n+2 ≤ 2·(n²+1). -/
private theorem sq_ineq (n : ℕ) (hn : 2 ≤ n) : n ^ 2 + 2 * n + 2 ≤ 2 * (n ^ 2 + 1) := by
  nlinarith

/-- 16^(n+1)·((n+1)²+1) < 2^((n+1)²) given 16^n·(n²+1) < 2^(n²) and n ≥ 6.

    The inductive step factored out as a standalone lemma. -/
private theorem inductive_step (n : ℕ) (hn : 6 ≤ n)
    (ih : 16 ^ n * (n ^ 2 + 1) < 2 ^ (n ^ 2)) :
    16 ^ (n + 1) * ((n + 1) ^ 2 + 1) < 2 ^ ((n + 1) ^ 2) := by
  -- Suffices to show the algebraically equivalent form
  suffices h : 16 * 16 ^ n * (n ^ 2 + 2 * n + 2) < 2 ^ (n ^ 2) * 2 ^ (2 * n + 1) by
    have h1 : 16 ^ (n + 1) * ((n + 1) ^ 2 + 1) = 16 * 16 ^ n * (n ^ 2 + 2 * n + 2) := by ring
    have h2 : 2 ^ ((n + 1) ^ 2) = 2 ^ (n ^ 2) * 2 ^ (2 * n + 1) := by
      rw [show (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) from by ring, pow_add]
    linarith
  -- n^2 + 2n + 2 ≤ 2*(n^2+1) for n ≥ 2
  have h_le : n ^ 2 + 2 * n + 2 ≤ 2 * (n ^ 2 + 1) := sq_ineq n (by omega)
  -- 32 ≤ 2^(2n+1) for n ≥ 6
  have h_pow : 32 ≤ 2 ^ (2 * n + 1) :=
    le_trans (show (32 : ℕ) ≤ 2 ^ 5 from by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- 16 * (n^2+2n+2) ≤ (n^2+1) * 2^(2n+1)
  have h_key : 16 * (n ^ 2 + 2 * n + 2) ≤ (n ^ 2 + 1) * 2 ^ (2 * n + 1) :=
    calc 16 * (n ^ 2 + 2 * n + 2)
        ≤ 16 * (2 * (n ^ 2 + 1)) := Nat.mul_le_mul_left 16 h_le
      _ = 32 * (n ^ 2 + 1) := by ring
      _ ≤ 2 ^ (2 * n + 1) * (n ^ 2 + 1) := Nat.mul_le_mul_right _ h_pow
      _ = (n ^ 2 + 1) * 2 ^ (2 * n + 1) := by ring
  -- Combine
  calc 16 * 16 ^ n * (n ^ 2 + 2 * n + 2)
      = 16 ^ n * (16 * (n ^ 2 + 2 * n + 2)) := by ring
    _ ≤ 16 ^ n * ((n ^ 2 + 1) * 2 ^ (2 * n + 1)) := Nat.mul_le_mul_left _ h_key
    _ = (16 ^ n * (n ^ 2 + 1)) * 2 ^ (2 * n + 1) := by ring
    _ < 2 ^ (n ^ 2) * 2 ^ (2 * n + 1) :=
        Nat.mul_lt_mul_of_pos_right ih (by positivity)

/-- 16^(k+6) · ((k+6)²+1) < 2^((k+6)²) for all k ≥ 0. -/
private theorem sixteen_pow_shifted (k : ℕ) :
    16 ^ (k + 6) * ((k + 6) ^ 2 + 1) < 2 ^ ((k + 6) ^ 2) := by
  induction k with
  | zero => norm_num
  | succ j ih =>
    -- j + 7 = (j + 6) + 1. Apply the inductive step.
    show 16 ^ (j + 6 + 1) * ((j + 6 + 1) ^ 2 + 1) < 2 ^ ((j + 6 + 1) ^ 2)
    exact inductive_step (j + 6) (by omega) ih

/-- 16^m · (m²+1) < 2^(m²) for m ≥ 6. -/
private theorem sixteen_pow_times_sq_lt (m : ℕ) (hm : 6 ≤ m) :
    16 ^ m * (m ^ 2 + 1) < 2 ^ (m ^ 2) := by
  have := sixteen_pow_shifted (m - 6)
  rwa [show m - 6 + 6 = m from by omega] at this

/-- numGridIntervals m ≥ 1 for all m (at least the empty set is an interval). -/
private theorem numGridIntervals_pos (m : ℕ) : 0 < numGridIntervals m := by
  unfold numGridIntervals allIntervals
  exact Finset.card_pos.mpr ⟨∅, Finset.mem_insert_self ∅ _⟩

/-- The cross-multiplied inequality for γ(grid) < γ(antichain) when m ≥ 6. -/
private theorem grid_lt_antichain_large (m : ℕ) (hm : 6 ≤ m) :
    numGridConvex m m * (m ^ 2 + 1) < 2 ^ (m ^ 2) * numGridIntervals m := by
  calc numGridConvex m m * (m ^ 2 + 1)
      ≤ 16 ^ m * (m ^ 2 + 1) :=
        Nat.mul_le_mul_right _ (numGridConvex_le_sixteen_pow m)
    _ < 2 ^ (m ^ 2) :=
        sixteen_pow_times_sq_lt m hm
    _ = 2 ^ (m ^ 2) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (m ^ 2) * numGridIntervals m :=
        Nat.mul_le_mul_left _ (numGridIntervals_pos m)

/-! ### The m = 5 case via the C(10,5)² upper bound -/

/-- C(10,5)² · 26 < 2^25, a pure arithmetic fact. -/
private theorem choose_10_5_sq_bound :
    Nat.choose 10 5 ^ 2 * 26 < 2 ^ 25 := by native_decide

/-- The cross-multiplied inequality for m = 5, using numGridConvex ≤ C(10,5)². -/
private theorem grid_lt_antichain_5 :
    numGridConvex 5 5 * (5 ^ 2 + 1) < 2 ^ (5 ^ 2) * numGridIntervals 5 := by
  calc numGridConvex 5 5 * (5 ^ 2 + 1)
      = numGridConvex 5 5 * 26 := by norm_num
    _ ≤ Nat.choose 10 5 ^ 2 * 26 :=
        Nat.mul_le_mul_right 26 (numGridConvex_le_choose_sq 5)
    _ < 2 ^ 25 := choose_10_5_sq_bound
    _ = 2 ^ (5 ^ 2) * 1 := by norm_num
    _ ≤ 2 ^ (5 ^ 2) * numGridIntervals 5 :=
        Nat.mul_le_mul_left _ (numGridIntervals_pos 5)

/-! ### The m = 2, 3, 4 cases by native_decide -/

/-- The cross-multiplied inequality for m = 2, 3, 4 by native_decide on exact values. -/
private theorem grid_lt_antichain_small (m : ℕ) (hm : 2 ≤ m) (hm5 : m ≤ 4) :
    numGridConvex m m * (m ^ 2 + 1) < 2 ^ (m ^ 2) * numGridIntervals m := by
  interval_cases m <;> native_decide

/-! ### Combining all cases -/

/-- **γ(grid) < γ(antichain)**: For the m×m grid (m ≥ 2), the Noetherian ratio
    of the grid is strictly less than that of the antichain on m² elements.

    Cross-multiplied form:
      numGridConvex m m · (m² + 1) < 2^(m²) · numGridIntervals m -/
theorem gamma_grid_lt_antichain (m : ℕ) (hm : 2 ≤ m) :
    numGridConvex m m * (m ^ 2 + 1) < 2 ^ (m ^ 2) * numGridIntervals m := by
  by_cases h6 : 6 ≤ m
  · exact grid_lt_antichain_large m h6
  · by_cases h5 : m = 5
    · subst h5; exact grid_lt_antichain_5
    · exact grid_lt_antichain_small m hm (by omega)

/-! ## The full three-way ordering -/

/-- **Dimensional Ordering Theorem**: For the m×m grid with m ≥ 2, the
    Noetherian ratios satisfy the strict ordering

      γ(chain_{m²}) < γ([m]²) < γ(antichain_{m²})

    where:
    - γ(chain) = 1 (every convex subset of a chain is an interval)
    - γ(grid) = numGridConvex m m / numGridIntervals m > 1
    - γ(antichain_{m²}) = 2^{m²} / (m² + 1)

    Part (a): γ(chain) < γ(grid) iff numGridIntervals m < numGridConvex m m
    Part (b): γ(grid) < γ(antichain) iff numGridConvex · (m²+1) < 2^{m²} · numGridIntervals -/
theorem dimensional_ordering (m : ℕ) (hm : 2 ≤ m) :
    numGridIntervals m < numGridConvex m m ∧
    numGridConvex m m * (m ^ 2 + 1) < 2 ^ (m ^ 2) * numGridIntervals m :=
  ⟨gamma_chain_lt_grid m hm, gamma_grid_lt_antichain m hm⟩

end CausalAlgebraicGeometry.DimensionalOrdering
