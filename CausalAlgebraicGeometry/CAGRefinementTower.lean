/-
  CAGRefinementTower.lean — Quantitative control along infinite sequences of
  past-closed causal refinements.

  Compatible state sequences satisfy an exact telescoping formula for tangent
  dimension: the degree at level n is the initial degree plus the sum of all
  newly created directions.  Uniform creation bounds imply linear growth,
  while eventual zero creation implies exact stabilization.

  The full directional curvature trace is universally bounded by degree
  squared.  Its rational normalization therefore lies in [0,1] at every
  refinement level, and every unnormalized trace is even.

  These are compactness-style prerequisites for a future continuum limit;
  they do not themselves construct that limit.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGCausalRefinement

namespace CausalAlgebraicGeometry.CAGRefinementTower

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGDirectionalGeometry
open CausalAlgebraicGeometry.CAGCausalRefinement

noncomputable section
open scoped Classical

/-! ## Universal curvature-density bound -/

variable {α : Type*} [PartialOrder α] [Fintype α]

theorem cubicalSectionalDefect_le_one
    (s a b : LowerSet α) :
    lowerSetCubicalSectionalDefect s a b ≤ 1 := by
  unfold lowerSetCubicalSectionalDefect cubicalSectionalDefect
  by_cases hinc :
      (lowerSetTransitionGraph (α := α)).Adj s a ∧
      (lowerSetTransitionGraph (α := α)).Adj s b ∧ a ≠ b
  · rw [if_pos hinc]
    split <;> omega
  · rw [if_neg hinc]
    omega

/-- The full ordered curvature trace is bounded by the square of tangent
dimension. -/
theorem totalDirectionalSectionalCurvature_le_degree_sq
    (s : LowerSet α) :
    totalDirectionalSectionalCurvature s ≤
      (lowerSetTransitionGraph (α := α)).degree s ^ 2 := by
  unfold totalDirectionalSectionalCurvature
  calc
    (∑ d : EventDirection s, ∑ e : EventDirection s,
        lowerSetCubicalSectionalDefect s d.1 e.1) ≤
      ∑ _d : EventDirection s, ∑ _e : EventDirection s, 1 := by
        apply Finset.sum_le_sum
        intro d _hd
        apply Finset.sum_le_sum
        intro e _he
        exact cubicalSectionalDefect_le_one s d.1 e.1
    _ = Fintype.card (EventDirection s) ^ 2 := by simp [pow_two]
    _ = (lowerSetTransitionGraph (α := α)).degree s ^ 2 := by
      rw [card_eventDirection_eq_degree]

/-- A dimensionless rational curvature density; the zero-dimensional case
uses the standard value `0 / 0 = 0` in `ℚ`. -/
def normalizedDirectionalCurvature (s : LowerSet α) : ℚ :=
  (totalDirectionalSectionalCurvature s : ℚ) /
    ((lowerSetTransitionGraph (α := α)).degree s ^ 2 : ℚ)

theorem normalizedDirectionalCurvature_nonneg (s : LowerSet α) :
    0 ≤ normalizedDirectionalCurvature s := by
  unfold normalizedDirectionalCurvature
  positivity

theorem normalizedDirectionalCurvature_le_one (s : LowerSet α) :
    normalizedDirectionalCurvature s ≤ 1 := by
  unfold normalizedDirectionalCurvature
  by_cases hdeg : (lowerSetTransitionGraph (α := α)).degree s = 0
  · simp [hdeg]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast totalDirectionalSectionalCurvature_le_degree_sq s

/-! ## Towers of past-closed refinements -/

section Tower

variable (P : ℕ → Type*)
  [∀ n, PartialOrder (P n)] [∀ n, Fintype (P n)]
variable (step : ∀ n, PastClosedEmbedding (P n) (P (n + 1)))
variable (state : ∀ n, LowerSet (P n))

/-- Tangent dimension at level `n`. -/
def towerDegree (n : ℕ) : ℕ :=
  (lowerSetTransitionGraph (α := P n)).degree (state n)

/-- New tangent directions introduced by refinement step `n`. -/
def towerNewDirectionCount (n : ℕ) : ℕ :=
  newDirectionCount (step n) (state n)

/-- Directional curvature trace at refinement level `n`. -/
def towerCurvature (n : ℕ) : ℕ :=
  totalDirectionalSectionalCurvature (state n)

/-- Dimensionless curvature density at level `n`. -/
def towerCurvatureDensity (n : ℕ) : ℚ :=
  normalizedDirectionalCurvature (state n)

/-- Exact one-step tangent-dimension recurrence. -/
theorem towerDegree_succ
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (n : ℕ) :
    towerDegree P state (n + 1) =
      towerDegree P state n + towerNewDirectionCount P step state n := by
  unfold towerDegree towerNewDirectionCount
  rw [compatible n]
  exact degree_extendState_eq_degree_add_newDirectionCount (step n) (state n)

/-- Exact telescoping formula for tangent dimension through `n` refinement
steps. -/
theorem towerDegree_eq_initial_add_sum
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (n : ℕ) :
    towerDegree P state n = towerDegree P state 0 +
      ∑ k ∈ Finset.range n, towerNewDirectionCount P step state k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [towerDegree_succ P step state compatible n, ih,
        Finset.sum_range_succ]
      omega

/-- Uniformly bounded direction creation gives at most linear tangent-degree
growth. -/
theorem towerDegree_le_initial_add_mul
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (B : ℕ) (hB : ∀ n, towerNewDirectionCount P step state n ≤ B)
    (n : ℕ) :
    towerDegree P state n ≤ towerDegree P state 0 + n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [towerDegree_succ P step state compatible n, Nat.succ_mul]
      have hn := hB n
      omega

/-- If no new directions appear after level `N`, tangent dimension stabilizes
exactly from that level onward. -/
theorem towerDegree_stabilizes
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (N : ℕ)
    (hzero : ∀ n, N ≤ n → towerNewDirectionCount P step state n = 0)
    (m : ℕ) :
    towerDegree P state (N + m) = towerDegree P state N := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, towerDegree_succ P step state compatible, ih,
        hzero (N + m) (Nat.le_add_right N m), add_zero]

/-- Curvature density is uniformly confined to the unit interval at every
level of every refinement tower. -/
theorem towerCurvatureDensity_mem_unitInterval (n : ℕ) :
    0 ≤ towerCurvatureDensity P state n ∧
      towerCurvatureDensity P state n ≤ 1 :=
  ⟨normalizedDirectionalCurvature_nonneg (state n),
    normalizedDirectionalCurvature_le_one (state n)⟩

/-- Every tower curvature trace remains even, because it counts both
orientations of each obstructed causal plane. -/
theorem towerCurvature_even (n : ℕ) :
    Even (towerCurvature P state n) := by
  unfold towerCurvature
  rw [totalDirectionalSectionalCurvature_eq_two_mul_incidenceCount]
  exact even_two_mul _

end Tower

end
end CausalAlgebraicGeometry.CAGRefinementTower
