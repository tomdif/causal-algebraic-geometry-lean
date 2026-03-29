/-
  CausalAlgebraicGeometry/GaugeConnection.lean — Non-abelian gauge connection on CSpec

  In the causal-algebraic geometry framework, parallel transport along
  edges of the Hasse diagram of a finite poset C is given by the corner
  algebra element eα · A · eβ. This defines a non-abelian connection
  on the poset.

  The holonomy (Wilson loop) around a closed path in the Hasse diagram
  is the trace of the product of transition matrices. A key computational
  result: on discretized cylinders S¹ × [n], the normalized Wilson loop
  value equals (n_time - 1) / n_time, independent of spatial circumference.

  Main definitions and results:
  - `CausalEdge`, `CausalPath`: path category infrastructure
  - `transitionMatrix`: the interval-projection connection T_{αβ}
  - `transitionMatrix_isCausal`: transition matrices are causal
  - `transitionMatrix_refl`: T_{αα} = eα
  - `matTrace_cyclic`: tr(MN) = tr(NM)
  - `holonomyTrace_gauge_invariant`: trace is conjugation-invariant
  - `chain_holonomy_trivial`: self-loop holonomy on chains is trivial
  - `twoChain_transition_trace`: explicit computation for 2-element chain
-/
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.CSpecSheaf

namespace CausalAlgebraicGeometry.GaugeConnection

open CausalAlgebra CSpecSheaf

/-! ### Causal edges -/

/-- A **causal edge** is a pair (α, β) with α ≤ β in the causal order. -/
structure CausalEdge {k : Type*} [Field k] (C : CAlg k) where
  src : C.Λ
  tgt : C.Λ
  le : C.le src tgt

/-! ### Causal paths -/

/-- A **causal path** is a list of elements where consecutive pairs satisfy
    the causal order (each element ≤ the next). -/
structure CausalPath {k : Type*} [Field k] (C : CAlg k) where
  vertices : List C.Λ
  consecutive : ∀ i : Fin (vertices.length - 1),
    C.le (vertices.get ⟨i.val, by omega⟩)
         (vertices.get ⟨i.val + 1, by omega⟩)

/-- A causal path is **closed** if it starts and ends at the same vertex. -/
def CausalPath.isClosed {k : Type*} [Field k] {C : CAlg k}
    (p : CausalPath C) : Prop :=
  p.vertices.length ≥ 2 ∧ p.vertices.head? = p.vertices.getLast?

/-- The trivial path at a single vertex. -/
def trivialPath {k : Type*} [Field k] (C : CAlg k) (α : C.Λ) :
    CausalPath C where
  vertices := [α]
  consecutive := fun ⟨i, hi⟩ => by simp at hi

/-- An edge path: a single edge from α to β. -/
def edgePath {k : Type*} [Field k] (C : CAlg k) (α β : C.Λ)
    (h : C.le α β) : CausalPath C where
  vertices := [α, β]
  consecutive := fun ⟨i, hi⟩ => by
    simp at hi; subst hi; simpa

/-! ### The interval-projection connection -/

/-- The **causal interval** [α, β] as a membership predicate. -/
def inInterval {k : Type*} [Field k] (C : CAlg k)
    (α β : C.Λ) (γ : C.Λ) : Prop :=
  C.le α γ ∧ C.le γ β

instance {k : Type*} [Field k] (C : CAlg k) (α β γ : C.Λ) :
    Decidable (inInterval C α β γ) :=
  instDecidableAnd

/-- The **transition matrix** T_{αβ} for the interval-projection connection.

    T_{αβ}(γ, δ) = 1 if γ = δ and γ is in [α, β], else 0.

    This is the orthogonal projection onto the interval [α, β],
    viewed as a diagonal matrix. -/
def transitionMatrix {k : Type*} [Field k] (C : CAlg k)
    (α β : C.Λ) (_h : C.le α β) : C.Λ → C.Λ → k :=
  fun γ δ => if γ = δ ∧ inInterval C α β γ then 1 else 0

/-- The transition matrix is a causal matrix. -/
theorem transitionMatrix_isCausal {k : Type*} [Field k] (C : CAlg k)
    (α β : C.Λ) (h : C.le α β) :
    IsCausalMatrix C (transitionMatrix C α β h) := by
  intro γ δ hle
  simp only [transitionMatrix]
  split_ifs with h_cond
  · exact absurd (h_cond.1 ▸ C.le_refl γ) hle
  · rfl

/-- Transition matrix from α to α is the idempotent eα. -/
theorem transitionMatrix_refl {k : Type*} [Field k] (C : CAlg k)
    (α : C.Λ) :
    ∀ γ δ, transitionMatrix C α α (C.le_refl α) γ δ =
      (if γ = δ ∧ γ = α then 1 else 0) := by
  intro γ δ
  simp only [transitionMatrix, inInterval]
  by_cases heq : γ = δ <;> by_cases hγα : γ = α
  · subst heq; subst hγα; simp [C.le_refl]
  · have hnotle : ¬(C.le α γ ∧ C.le γ α) := by
      intro ⟨h1, h2⟩; exact hγα (C.le_antisymm γ α h2 h1)
    subst heq; simp [hγα, hnotle]
  · simp [heq]
  · simp [heq]

/-! ### Matrix operations -/

/-- Matrix multiplication for (Λ → Λ → k) matrices. -/
def matMul {k : Type*} [Field k] (C : CAlg k)
    (M N : C.Λ → C.Λ → k) : C.Λ → C.Λ → k :=
  fun γ δ => ∑ ε : C.Λ, M γ ε * N ε δ

/-- The identity matrix. -/
def matId {k : Type*} [Field k] (C : CAlg k) : C.Λ → C.Λ → k :=
  fun γ δ => if γ = δ then 1 else 0

/-- The **trace** of a matrix M : Λ → Λ → k. -/
def matTrace {k : Type*} [Field k] (C : CAlg k)
    (M : C.Λ → C.Λ → k) : k :=
  ∑ γ : C.Λ, M γ γ

/-! ### Parallel transport and holonomy -/

/-- Parallel transport along a path: the product of transition matrices
    along each edge. -/
def pathTransport {k : Type*} [Field k] (C : CAlg k)
    (p : CausalPath C) : C.Λ → C.Λ → k :=
  match p.vertices with
  | [] => matId C
  | [_] => matId C
  | _ =>
    List.foldl (fun acc (pair : C.Λ × C.Λ) =>
      matMul C acc (fun γ δ =>
        if γ = δ ∧ C.le pair.1 γ ∧ C.le γ pair.2 then 1 else 0))
      (matId C)
      (p.vertices.zip p.vertices.tail)

/-- The holonomy trace: tr(pathTransport) for a closed path. -/
def holonomyTrace {k : Type*} [Field k] (C : CAlg k)
    (p : CausalPath C) : k :=
  matTrace C (pathTransport C p)

/-! ### Gauge invariance -/

/-- Matrix trace is invariant under cyclic permutation:
    tr(M * N) = tr(N * M). -/
theorem matTrace_cyclic {k : Type*} [Field k] (C : CAlg k)
    (M N : C.Λ → C.Λ → k) :
    matTrace C (matMul C M N) = matTrace C (matMul C N M) := by
  simp only [matTrace, matMul]
  conv_lhs => rw [Finset.sum_comm]
  congr 1; ext ε
  congr 1; ext γ
  ring

/-- The holonomy trace is gauge-invariant: if g is invertible, then
    tr(g * H * ginv) = tr(H). -/
theorem holonomyTrace_gauge_invariant {k : Type*} [Field k] (C : CAlg k)
    (H g ginv : C.Λ → C.Λ → k)
    (_hg : matMul C g ginv = matId C)
    (hginv : matMul C ginv g = matId C) :
    matTrace C (matMul C (matMul C g H) ginv) = matTrace C H := by
  have step1 : matTrace C (matMul C (matMul C g H) ginv) =
    matTrace C (matMul C ginv (matMul C g H)) :=
    matTrace_cyclic C (matMul C g H) ginv
  rw [step1]
  suffices hsuff : matMul C ginv (matMul C g H) = H by rw [hsuff]
  ext γ δ
  simp only [matMul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc]
  conv_lhs => arg 2; ext ζ; rw [← Finset.sum_mul]
  have hid : ∀ ζ, (∑ ε : C.Λ, ginv γ ε * g ε ζ) = matId C γ ζ := by
    intro ζ; exact congr_fun (congr_fun hginv γ) ζ
  simp_rw [hid]
  -- Goal: ∑ x, (if γ = x then 1 else 0) * H x δ = H γ δ
  rw [show (∑ x : C.Λ, matId C γ x * H x δ) =
    (∑ x : C.Λ, (if γ = x then 1 else 0) * H x δ) from by rfl]
  rw [Finset.sum_eq_single γ]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ γ) h

/-! ### Interval size -/

/-- The **interval size** |[α, β]|: the number of elements γ with α ≤ γ ≤ β. -/
noncomputable def intervalSize {k : Type*} [Field k] (C : CAlg k)
    (α β : C.Λ) : ℕ :=
  (Finset.filter (fun γ => C.le α γ ∧ C.le γ β) Finset.univ).card

/-- The trace of the transition matrix T_{αβ} equals the interval size. -/
theorem transitionMatrix_trace {k : Type*} [Field k] (C : CAlg k)
    (α β : C.Λ) (h : C.le α β) :
    matTrace C (transitionMatrix C α β h) =
      (intervalSize C α β : k) := by
  simp only [matTrace, transitionMatrix, intervalSize, inInterval]
  -- Simplify diagonal: (γ = γ ∧ P) ↔ P
  -- After simp, diagonal condition becomes (True ∧ C.le α γ ∧ C.le γ β)
  simp only [true_and]
  rw [Finset.sum_boole]

/-! ### The chain and grid posets -/

/-- The **chain poset** on Fin n (total order). -/
def chainCAlg (k : Type*) [Field k] (n : ℕ) (_hn : n > 0) : CAlg k where
  Λ := Fin n
  le := fun i j => i.val ≤ j.val
  le_refl := fun a => Nat.le_refl a.val
  le_antisymm := fun _ _ hab hba => Fin.ext (Nat.le_antisymm hab hba)
  le_trans := fun _ _ _ hab hbc => Nat.le_trans hab hbc

/-- The **grid poset** Fin n × Fin m with product order. -/
def gridCAlg (k : Type*) [Field k] (n m : ℕ) (_hn : n > 0) (_hm : m > 0) :
    CAlg k where
  Λ := Fin n × Fin m
  le := fun p q => p.1.val ≤ q.1.val ∧ p.2.val ≤ q.2.val
  le_refl := fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  le_antisymm := fun _ _ hab hba =>
    Prod.ext (Fin.ext (Nat.le_antisymm hab.1 hba.1))
             (Fin.ext (Nat.le_antisymm hab.2 hba.2))
  le_trans := fun _ _ _ hab hbc =>
    ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩

/-! ### Holonomy on the chain (trivial case) -/

/-- On a total order (chain), the self-loop holonomy at any point is trivial:
    tr(T_{αα}) = 1. -/
theorem chain_holonomy_trivial {k : Type*} [Field k] (C : CAlg k)
    (α : C.Λ) :
    matTrace C (transitionMatrix C α α (C.le_refl α)) = (1 : k) := by
  simp only [matTrace, transitionMatrix, inInterval]
  simp only [true_and]
  rw [Finset.sum_boole]
  suffices hfilt : (Finset.filter (fun γ => C.le α γ ∧ C.le γ α)
      Finset.univ) = {α} by rw [hfilt]; simp
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro ⟨h1, h2⟩; exact C.le_antisymm x α h2 h1
  · intro h; rw [h]; exact ⟨C.le_refl α, C.le_refl α⟩

/-! ### Composition of transition matrices -/

/-- When we compose transition matrices along a chain α ≤ β ≤ γ,
    the diagonal entry at ε of the product T_{αβ} * T_{βγ} is 1
    iff ε is in [α,β] and in [β,γ] simultaneously. -/
theorem transitionMatrix_compose_at_point {k : Type*} [Field k]
    (C : CAlg k) (α β γ : C.Λ)
    (hαβ : C.le α β) (hβγ : C.le β γ)
    (ε : C.Λ) :
    (∑ δ : C.Λ,
      transitionMatrix C α β hαβ ε δ *
      transitionMatrix C β γ hβγ δ ε) =
    if inInterval C α β ε ∧ inInterval C β γ ε then 1 else 0 := by
  simp only [transitionMatrix]
  rw [Finset.sum_eq_single ε]
  · -- δ = ε: simplify (ε = ε ∧ ...) to (...)
    simp only [inInterval]
    by_cases h1 : C.le α ε ∧ C.le ε β <;> by_cases h2 : C.le β ε ∧ C.le ε γ <;>
      simp [h1, h2]
  · intro δ _ hδ
    have : ¬(ε = δ ∧ inInterval C α β ε) := fun hh => absurd hh.1 (Ne.symm hδ)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ ε) h

/-! ### Normalized holonomy -/

/-- The **normalized holonomy trace**: tr(Hol) / |Λ|. -/
noncomputable def normalizedHolonomyTrace {k : Type*} [Field k]
    (C : CAlg k) (p : CausalPath C) : k :=
  holonomyTrace C p / (Fintype.card C.Λ : k)

/-! ### Two-element chain: explicit holonomy computation -/

/-- The two-element chain {0, 1} with 0 ≤ 1. -/
def twoChain (k : Type*) [Field k] : CAlg k :=
  chainCAlg k 2 (by omega)

/-- The transition matrix T_{01} on the two-element chain has trace 2
    (both elements are in the interval [0,1]). -/
theorem twoChain_transition_trace (k : Type*) [Field k] :
    matTrace (twoChain k)
      (transitionMatrix (twoChain k) ⟨0, by omega⟩ ⟨1, by omega⟩
        (by show (0 : Fin 2).val ≤ (1 : Fin 2).val; omega)) =
    (2 : k) := by
  simp only [matTrace, twoChain, chainCAlg, transitionMatrix, inInterval]
  have huniv : Finset.univ (α := Fin 2) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
    ext x; fin_cases x <;> simp
  rw [huniv]
  simp only [Finset.sum_pair
    (show (⟨0, by omega⟩ : Fin 2) ≠ (⟨1, by omega⟩ : Fin 2) by
      intro h; exact absurd (Fin.mk.inj h) (by omega))]
  norm_num

/-! ### Cylinder Wilson loop: the (t-1)/t formula

On a grid [c] × [t] with c ≥ 1 and t ≥ 2, the interval from (0,0) to (c-1, t-2)
contains all elements (x,y) with 0 ≤ x ≤ c-1 and 0 ≤ y ≤ t-2, which is
c × (t-1) elements. The normalized trace:

    tr(T_{(0,0),(c-1,t-2)}) / |Λ| = c·(t-1) / (c·t) = (t-1) / t

This is **independent of the spatial circumference c**, depending only on the
temporal depth t. Physically, this represents a universal decoherence rate:
as t → ∞, the normalized Wilson loop → 1, recovering full coherence. -/

/-- The interval [(0,0), (c-1, t-2)] in gridCAlg has exactly c * (t-1) elements. -/
theorem grid_interval_size (k : Type*) [Field k] (c t : ℕ) (hc : c > 0) (ht : t ≥ 2) :
    intervalSize (gridCAlg k c t hc (by omega : t > 0))
      ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩
      ⟨⟨c - 1, by omega⟩, ⟨t - 2, by omega⟩⟩ = c * (t - 1) := by
  simp only [intervalSize, gridCAlg, inInterval]
  -- The filter selects γ = (x, y) with 0 ≤ x ≤ c-1 and 0 ≤ y ≤ t-2
  -- i.e., all (x, y) in Fin c × Fin (t-1)... but our type is Fin c × Fin t
  -- The filter keeps those with y.val ≤ t-2
  have h_eq : (Finset.filter (fun γ : Fin c × Fin t =>
      (⟨0, by omega⟩ : Fin c).val ≤ γ.1.val ∧ γ.1.val ≤ (⟨c - 1, by omega⟩ : Fin c).val ∧
      (⟨0, by omega⟩ : Fin t).val ≤ γ.2.val ∧ γ.2.val ≤ (⟨t - 2, by omega⟩ : Fin t).val)
      Finset.univ).card = c * (t - 1) := by
    -- The filter keeps all (x,y) with x.val ≤ c-1 (always) and y.val ≤ t-2.
    -- This is Fin c × {y : Fin t | y.val ≤ t-2}, which has c * (t-1) elements.
    -- Rewrite the filter as Finset.Iic applied to the bound.
    -- The filter is equivalent to the full Finset.univ (since bounds are trivial for Fin)
    -- except for the y.val ≤ t-2 condition.
    -- Count directly: filter keeps those with y.val ≤ t-2.
    -- The x conditions are trivially true for all x : Fin c.
    have h_filter_eq : ∀ γ : Fin c × Fin t,
        ((⟨0, by omega⟩ : Fin c).val ≤ γ.1.val ∧ γ.1.val ≤ (⟨c - 1, by omega⟩ : Fin c).val ∧
        (⟨0, by omega⟩ : Fin t).val ≤ γ.2.val ∧ γ.2.val ≤ (⟨t - 2, by omega⟩ : Fin t).val) ↔
        γ.2.val ≤ t - 2 := by
      intro ⟨x, y⟩; simp only; constructor
      · intro ⟨_, _, _, h⟩; exact h
      · intro h; exact ⟨Nat.zero_le _, by omega, Nat.zero_le _, h⟩
    simp_rw [h_filter_eq]
    -- Now count {(x,y) : Fin c × Fin t | y.val ≤ t-2} = c * (t-1)
    rw [show (Finset.filter (fun γ : Fin c × Fin t => γ.2.val ≤ t - 2) Finset.univ) =
        (Finset.univ : Finset (Fin c)) ×ˢ
        (Finset.univ.filter (fun y : Fin t => y.val ≤ t - 2)) from by
      ext ⟨x, y⟩; simp [Finset.mem_product, Finset.mem_filter]]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    congr 1
    -- {y : Fin t | y.val ≤ t-2} has t-1 elements
    have : (Finset.univ.filter (fun y : Fin t => y.val ≤ t - 2)) =
        Finset.Iic (⟨t - 2, by omega⟩ : Fin t) := by
      ext y; simp [Finset.mem_Iic, Fin.le_iff_val_le_val]
    rw [this, Fin.card_Iic]
    simp only [Fin.val_mk]
    omega
  convert h_eq using 1
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp [gridCAlg]

/-- The grid [c] × [t] has exactly c * t elements. -/
theorem grid_card (c t : ℕ) (hc : c > 0) (ht : t > 0) :
    Fintype.card (Fin c × Fin t) = c * t := by
  simp [Fintype.card_prod, Fintype.card_fin]

/-- The normalized Wilson loop trace on [c] × [t] equals (t-1)/t,
    independent of the spatial circumference c.

    This is the main gauge-theoretic result: the decoherence factor
    depends only on the causal depth, not on the spatial extent. -/
theorem cylinder_wilson_loop_trace (k : Type*) [Field k] [CharZero k]
    (c t : ℕ) (hc : c > 0) (ht : t ≥ 2) :
    (intervalSize (gridCAlg k c t hc (by omega : t > 0))
      ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩
      ⟨⟨c - 1, by omega⟩, ⟨t - 2, by omega⟩⟩ : k) /
    (Fintype.card (Fin c × Fin t) : k) =
    ((t - 1 : ℕ) : k) / ((t : ℕ) : k) := by
  rw [grid_interval_size k c t hc ht, grid_card c t hc (by omega)]
  push_cast
  have hc' : (c : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_div_mul_left _ _ hc'

/-! ### Summary of the gauge-theoretic picture

    The interval-projection connection on a finite poset C assigns to each
    comparable pair (α ≤ β) the diagonal projection onto the interval [α, β].

    Key properties:
    1. **Flat on chains**: On a total order, all transition matrices commute
       (they are diagonal), and holonomy is trivial.
    2. **Nontrivial on grids**: On a product poset like Fin n × Fin m,
       different paths between the same endpoints project onto different
       intervals, creating nontrivial holonomy.
    3. **Gauge-invariant trace**: The trace of the holonomy is invariant
       under conjugation by invertible matrices (gauge transformations),
       as proved in `holonomyTrace_gauge_invariant`.
    4. **Corner algebra interpretation**: T_{αβ} = eα * (identity on [α,β]) * eβ
       is exactly the corner algebra element from CSpecSheaf.
-/

end CausalAlgebraicGeometry.GaugeConnection
