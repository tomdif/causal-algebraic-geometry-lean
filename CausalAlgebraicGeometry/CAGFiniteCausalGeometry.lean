/-
  CAGFiniteCausalGeometry.lean — Intrinsic cubical geometry of finite causal
  posets and finite causal algebras.

  A causal state is a lower set of events.  Its characteristic function is a
  Boolean coordinate vector indexed by the events themselves.  This file
  proves that the graph of single-event changes is the undirected Hasse graph
  of the lower-set lattice, that its shortest-path metric is exactly Hamming
  distance, and that it is a median graph and an explicit partial cube.

  The final section defines a graph-intrinsic square-completion defect.  It
  counts ordered pairs of incident moves which do not extend to a square.  It
  is a rigorous local obstruction to commuting causal moves; it is not
  asserted to be a Riemannian curvature tensor.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGTransitionGeometry
import CausalAlgebraicGeometry.CausalAlgebra
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.Preorder.Finite

namespace CausalAlgebraicGeometry.CAGFiniteCausalGeometry

open CausalAlgebraicGeometry.CAGTransitionGeometry
open CausalAlgebraicGeometry.CausalAlgebra

noncomputable section
open scoped Classical

section FinitePoset

variable {α : Type*} [PartialOrder α] [Fintype α]

/-! ## Event coordinates and intrinsic distance -/

/-- Boolean occupancy coordinates of a finite causal downset. -/
def lowerSetCode (s : LowerSet α) : α → Bool :=
  fun a => decide (a ∈ s)

/-- The number of causal events on which two downset states disagree. -/
def lowerSetDistance (s t : LowerSet α) : ℕ :=
  hammingDist (lowerSetCode s) (lowerSetCode t)

omit [Fintype α] in
theorem lowerSetCode_injective :
    Function.Injective (lowerSetCode : LowerSet α → α → Bool) := by
  intro s t hst
  apply LowerSet.ext
  ext a
  have ha := congrFun hst a
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;>
    simp_all [lowerSetCode]

@[simp]
theorem lowerSetDistance_self (s : LowerSet α) :
    lowerSetDistance s s = 0 := by
  simp [lowerSetDistance]

theorem lowerSetDistance_comm (s t : LowerSet α) :
    lowerSetDistance s t = lowerSetDistance t s := by
  exact hammingDist_comm _ _

theorem lowerSetDistance_triangle (s t u : LowerSet α) :
    lowerSetDistance s u ≤ lowerSetDistance s t + lowerSetDistance t u := by
  exact hammingDist_triangle _ _ _

@[simp]
theorem lowerSetDistance_eq_zero_iff (s t : LowerSet α) :
    lowerSetDistance s t = 0 ↔ s = t := by
  constructor
  · intro h
    apply lowerSetCode_injective
    exact hammingDist_eq_zero.mp h
  · rintro rfl
    exact lowerSetDistance_self s

private theorem hammingDist_eq_sum_indicator {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, DecidableEq (β i)] (x y : ∀ i, β i) :
    hammingDist x y = ∑ i, if x i ≠ y i then 1 else 0 := by
  unfold hammingDist
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private def boolDistance (a b : Bool) : ℕ :=
  if a ≠ b then 1 else 0

private theorem lowerSetDistance_eq_sum_boolDistance (s t : LowerSet α) :
    lowerSetDistance s t =
      ∑ a : α, boolDistance (lowerSetCode s a) (lowerSetCode t a) := by
  unfold lowerSetDistance boolDistance
  exact hammingDist_eq_sum_indicator _ _

/-- The lower-set distance is the cardinality of the symmetric difference of
the occupied causal events. -/
theorem lowerSetDistance_eq_card_filter (s t : LowerSet α) :
    lowerSetDistance s t =
      (Finset.univ.filter fun a : α => (a ∈ s) ≠ (a ∈ t)).card := by
  unfold lowerSetDistance hammingDist lowerSetCode
  congr 1
  ext a
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp_all

/-- Inclusion chains split the event Hamming distance exactly. -/
theorem lowerSetDistance_split_of_le {s r t : LowerSet α}
    (hsr : s ≤ r) (hrt : r ≤ t) :
    lowerSetDistance s t = lowerSetDistance s r + lowerSetDistance r t := by
  unfold lowerSetDistance
  simp_rw [hammingDist_eq_sum_indicator]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hsr' : (s : Set α) ⊆ (r : Set α) := hsr
  have hrt' : (r : Set α) ⊆ (t : Set α) := hrt
  by_cases hs : a ∈ s
  · have hr : a ∈ r := hsr' hs
    have ht : a ∈ t := hrt' hr
    simp [lowerSetCode, hs, hr, ht]
  · by_cases hr : a ∈ r
    · have ht : a ∈ t := hrt' hr
      simp [lowerSetCode, hs, hr, ht]
    · by_cases ht : a ∈ t <;> simp [lowerSetCode, hs, hr, ht]

/-- The intersection is a canonical metric waypoint between two downsets. -/
theorem lowerSetDistance_split_inf (s t : LowerSet α) :
    lowerSetDistance s t =
      lowerSetDistance s (s ⊓ t) + lowerSetDistance (s ⊓ t) t := by
  unfold lowerSetDistance
  simp_rw [hammingDist_eq_sum_indicator]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;>
    simp_all [lowerSetCode]

/-! ## The canonical lower-set median -/

/-- Majority of three causal-event occupancy states. -/
def lowerSetMedian (s t u : LowerSet α) : LowerSet α :=
  (s ⊓ t) ⊔ ((t ⊓ u) ⊔ (u ⊓ s))

omit [Fintype α] in
@[simp]
theorem mem_lowerSetMedian_iff {s t u : LowerSet α} {a : α} :
    a ∈ lowerSetMedian s t u ↔
      (a ∈ s ∧ a ∈ t) ∨ (a ∈ t ∧ a ∈ u) ∨ (a ∈ u ∧ a ∈ s) := by
  rfl

/-- The lower-set majority lies simultaneously on all three pairwise metric
intervals. -/
theorem lowerSetMedian_three_geodesics (s t u : LowerSet α) :
    (lowerSetDistance s t =
      lowerSetDistance s (lowerSetMedian s t u) +
        lowerSetDistance (lowerSetMedian s t u) t) ∧
    (lowerSetDistance t u =
      lowerSetDistance t (lowerSetMedian s t u) +
        lowerSetDistance (lowerSetMedian s t u) u) ∧
    (lowerSetDistance u s =
      lowerSetDistance u (lowerSetMedian s t u) +
        lowerSetDistance (lowerSetMedian s t u) s) := by
  unfold lowerSetDistance
  simp_rw [hammingDist_eq_sum_indicator]
  constructor
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> by_cases hu : a ∈ u <;>
      simp_all [lowerSetCode, lowerSetMedian]
  constructor
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> by_cases hu : a ∈ u <;>
      simp_all [lowerSetCode, lowerSetMedian]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> by_cases hu : a ∈ u <;>
      simp_all [lowerSetCode, lowerSetMedian]

/-- Metric-interval predicate for arbitrary finite causal downsets. -/
def OnLowerSetInterval (s x t : LowerSet α) : Prop :=
  lowerSetDistance s t = lowerSetDistance s x + lowerSetDistance x t

private theorem boolDistance_triangle (a b c : Bool) :
    boolDistance a c ≤ boolDistance a b + boolDistance b c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Global Hamming-interval saturation forces interval saturation in each
individual event coordinate. -/
theorem onLowerSetInterval_pointwise {s x t : LowerSet α}
    (h : OnLowerSetInterval s x t) (a : α) :
    boolDistance (lowerSetCode s a) (lowerSetCode t a) =
      boolDistance (lowerSetCode s a) (lowerSetCode x a) +
        boolDistance (lowerSetCode x a) (lowerSetCode t a) := by
  have hsum :
      (∑ i : α,
        (boolDistance (lowerSetCode s i) (lowerSetCode x i) +
          boolDistance (lowerSetCode x i) (lowerSetCode t i) -
          boolDistance (lowerSetCode s i) (lowerSetCode t i))) = 0 := by
    rw [Finset.sum_tsub_distrib]
    · rw [Finset.sum_add_distrib]
      rw [← lowerSetDistance_eq_sum_boolDistance,
        ← lowerSetDistance_eq_sum_boolDistance,
        ← lowerSetDistance_eq_sum_boolDistance]
      unfold OnLowerSetInterval at h
      rw [← h]
      exact Nat.sub_self _
    · intro i _
      exact boolDistance_triangle _ _ _
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (s := (Finset.univ : Finset α))
    (f := fun i =>
      boolDistance (lowerSetCode s i) (lowerSetCode x i) +
        boolDistance (lowerSetCode x i) (lowerSetCode t i) -
        boolDistance (lowerSetCode s i) (lowerSetCode t i))
    (fun _ _ => Nat.zero_le _)).mp hsum
  have hreverse :
      boolDistance (lowerSetCode s a) (lowerSetCode x a) +
          boolDistance (lowerSetCode x a) (lowerSetCode t a) ≤
        boolDistance (lowerSetCode s a) (lowerSetCode t a) :=
    Nat.sub_eq_zero_iff_le.mp (hall a (Finset.mem_univ a))
  exact le_antisymm (boolDistance_triangle _ _ _) hreverse

/-- Majority is the unique common point of the three downset intervals. -/
theorem lowerSetMedian_unique (s t u x : LowerSet α)
    (hst : OnLowerSetInterval s x t)
    (htu : OnLowerSetInterval t x u)
    (hus : OnLowerSetInterval u x s) :
    x = lowerSetMedian s t u := by
  apply LowerSet.ext
  ext a
  have hst' := onLowerSetInterval_pointwise hst a
  have htu' := onLowerSetInterval_pointwise htu a
  have hus' := onLowerSetInterval_pointwise hus a
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;>
    by_cases hu : a ∈ u <;> by_cases hx : a ∈ x <;>
    simp_all [lowerSetCode, boolDistance, lowerSetMedian]

theorem existsUnique_lowerSetMedian (s t u : LowerSet α) :
    ∃! x : LowerSet α,
      OnLowerSetInterval s x t ∧ OnLowerSetInterval t x u ∧
        OnLowerSetInterval u x s := by
  refine ⟨lowerSetMedian s t u, lowerSetMedian_three_geodesics s t u, ?_⟩
  intro x hx
  exact lowerSetMedian_unique s t u x hx.1 hx.2.1 hx.2.2

/-! ## One admissible event insertion -/

/-- Every strict inclusion of finite causal downsets contains a legal
single-event insertion. -/
theorem exists_singleEvent_above_of_lt {s t : LowerSet α} (hst : s < t) :
    ∃ r : LowerSet α,
      s ≤ r ∧ r ≤ t ∧ lowerSetDistance s r = 1 := by
  let D : Finset α :=
    Finset.univ.filter (fun a => a ∈ t ∧ a ∉ s)
  have hDne : D.Nonempty := by
    by_contra hD
    rw [Finset.not_nonempty_iff_eq_empty] at hD
    have hts : t ≤ s := by
      intro a ha
      by_contra hna
      have : a ∈ D :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha, hna⟩
      rw [hD] at this
      simp at this
    exact (not_le_of_gt hst) hts
  obtain ⟨a, hamin⟩ := D.exists_minimal hDne
  have haD : a ∈ D := hamin.1
  have hat : a ∈ t := (Finset.mem_filter.mp haD).2.1
  have has : a ∉ s := (Finset.mem_filter.mp haD).2.2
  let r : LowerSet α :=
    { carrier := Set.insert a (s : Set α)
      lower' := by
        intro b c hbc hb
        change b ∈ Set.insert a (s : Set α) at hb
        rcases Set.mem_insert_iff.mp hb with hba | hbs
        · subst b
          by_cases hcs : c ∈ s
          · exact Set.mem_insert_of_mem a hcs
          · apply Set.mem_insert_iff.mpr
            apply Or.inl
            have hct : c ∈ t := t.lower hbc hat
            have hcD : c ∈ D := by simp [D, hct, hcs]
            exact le_antisymm hbc (hamin.2 hcD hbc)
        · exact Set.mem_insert_of_mem a (s.lower hbc hbs) }
  have hsr : s ≤ r := by
    intro b hb
    exact Set.mem_insert_iff.mpr (Or.inr hb)
  have hrt : r ≤ t := by
    intro b hb
    rcases Set.mem_insert_iff.mp hb with rfl | hbs
    · exact hat
    · exact hst.le hbs
  have hdist : lowerSetDistance s r = 1 := by
    unfold lowerSetDistance hammingDist
    have hfilter :
        Finset.univ.filter (fun b : α => lowerSetCode s b ≠ lowerSetCode r b) =
          {a} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      unfold lowerSetCode
      change (decide (b ∈ s) ≠ decide (b ∈ Set.insert a (s : Set α))) ↔ b = a
      by_cases hba : b = a
      · subst b
        have hai : a ∈ Set.insert a (s : Set α) := Set.mem_insert a _
        simp [has, hai]
      · by_cases hbs : b ∈ s
        · have hbi : b ∈ Set.insert a (s : Set α) := Set.mem_insert_of_mem a hbs
          simp [hbs, hbi, hba]
        · have hbni : b ∉ Set.insert a (s : Set α) := by
            intro hb
            rcases Set.mem_insert_iff.mp hb with h | h
            · exact hba h
            · exact hbs h
          simp [hbs, hbni, hba]
    rw [hfilter]
    simp
  exact ⟨r, hsr, hrt, hdist⟩

/-! ## The Hasse graph and exact path metric -/

/-- Single-event transition graph of finite causal downsets. -/
def lowerSetTransitionGraph : SimpleGraph (LowerSet α) where
  Adj s t := lowerSetDistance s t = 1
  symm := by
    intro s t h
    rwa [lowerSetDistance_comm]
  loopless := by
    constructor
    intro s h
    rw [lowerSetDistance_self] at h
    omega

@[simp]
theorem lowerSetTransitionGraph_adj_iff (s t : LowerSet α) :
    lowerSetTransitionGraph.Adj s t ↔ lowerSetDistance s t = 1 := Iff.rfl

theorem lowerSetDistance_le_walk_length {s t : LowerSet α}
    (w : lowerSetTransitionGraph.Walk s t) :
    lowerSetDistance s t ≤ w.length := by
  induction w with
  | nil => simp
  | @cons s r t hsr w ih =>
      have hstep : lowerSetDistance s r = 1 := hsr
      have htri := lowerSetDistance_triangle s r t
      simp only [SimpleGraph.Walk.length_cons]
      omega

theorem covBy_of_le_lowerSetDistance_eq_one {s t : LowerSet α}
    (hst : s ≤ t) (hdist : lowerSetDistance s t = 1) : s ⋖ t := by
  have hne : s ≠ t := by
    intro h
    subst t
    simp at hdist
  refine ⟨lt_of_le_of_ne hst hne, ?_⟩
  intro r hsr hrt
  have hsplit := lowerSetDistance_split_of_le hsr.le hrt.le
  have hsrpos : 0 < lowerSetDistance s r := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hsr.ne ((lowerSetDistance_eq_zero_iff s r).mp hz)
  have hrtpos : 0 < lowerSetDistance r t := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hrt.ne ((lowerSetDistance_eq_zero_iff r t).mp hz)
  omega

theorem lowerSetDistance_eq_one_of_covBy {s t : LowerSet α}
    (hst : s ⋖ t) : lowerSetDistance s t = 1 := by
  obtain ⟨r, hsr, hrt, hstep⟩ := exists_singleEvent_above_of_lt hst.lt
  rcases hst.eq_or_eq hsr hrt with hrs | hrt'
  · subst r
    simp at hstep
  · subst r
    exact hstep

theorem lowerSetTransitionGraph_adj_iff_covBy (s t : LowerSet α) :
    lowerSetTransitionGraph.Adj s t ↔ s ⋖ t ∨ t ⋖ s := by
  constructor
  · intro hdist
    have hdist' : lowerSetDistance s t = 1 := hdist
    have hsplit := lowerSetDistance_split_inf s t
    have hzero : lowerSetDistance s (s ⊓ t) = 0 ∨
        lowerSetDistance (s ⊓ t) t = 0 := by omega
    rcases hzero with hs0 | ht0
    · have hsinf := (lowerSetDistance_eq_zero_iff s (s ⊓ t)).mp hs0
      have hst : s ≤ t := by rw [hsinf]; exact inf_le_right
      exact Or.inl (covBy_of_le_lowerSetDistance_eq_one hst hdist')
    · have hinft := (lowerSetDistance_eq_zero_iff (s ⊓ t) t).mp ht0
      have hts : t ≤ s := by rw [← hinft]; exact inf_le_left
      exact Or.inr (covBy_of_le_lowerSetDistance_eq_one hts
        (by rwa [lowerSetDistance_comm]))
  · rintro (hst | hts)
    · exact lowerSetDistance_eq_one_of_covBy hst
    · change lowerSetDistance s t = 1
      rw [lowerSetDistance_comm]
      exact lowerSetDistance_eq_one_of_covBy hts

theorem exists_exact_lowerSet_walk_of_le {s t : LowerSet α} (hst : s ≤ t) :
    ∃ w : lowerSetTransitionGraph.Walk s t,
      w.length = lowerSetDistance s t := by
  let P : ℕ → Prop := fun n =>
    ∀ (a b : LowerSet α), a ≤ b → lowerSetDistance a b = n →
      ∃ w : lowerSetTransitionGraph.Walk a b, w.length = n
  have hP : ∀ n : ℕ, (∀ k < n, P k) → P n := by
    intro n ih a b hab hdist
    by_cases heq : a = b
    · subst b
      have hn : n = 0 := by simpa using hdist.symm
      subst n
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · have hlt : a < b := lt_of_le_of_ne hab heq
      obtain ⟨r, har, hrb, hstep⟩ := exists_singleEvent_above_of_lt hlt
      have hsplit := lowerSetDistance_split_of_le har hrb
      have hrlt : lowerSetDistance r b < n := by omega
      obtain ⟨w, hw⟩ := ih (lowerSetDistance r b) hrlt r b hrb rfl
      refine ⟨SimpleGraph.Walk.cons ?_ w, ?_⟩
      · exact hstep
      · simp only [SimpleGraph.Walk.length_cons, hw]
        omega
  have hall : ∀ n, P n := fun n => Nat.strong_induction_on n hP
  exact hall (lowerSetDistance s t) s t hst rfl

theorem exists_exact_lowerSet_walk (s t : LowerSet α) :
    ∃ w : lowerSetTransitionGraph.Walk s t,
      w.length = lowerSetDistance s t := by
  obtain ⟨ws, hws⟩ := exists_exact_lowerSet_walk_of_le
    (inf_le_left : s ⊓ t ≤ s)
  obtain ⟨wt, hwt⟩ := exists_exact_lowerSet_walk_of_le
    (inf_le_right : s ⊓ t ≤ t)
  refine ⟨ws.reverse.append wt, ?_⟩
  have hsplit := lowerSetDistance_split_inf s t
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    hws, hwt]
  rw [lowerSetDistance_comm (s ⊓ t) s]
  exact hsplit.symm

theorem lowerSetTransitionGraph_connected :
    (lowerSetTransitionGraph (α := α)).Connected := by
  refine { nonempty := ⟨⊥⟩, preconnected := ?_ }
  intro s t
  obtain ⟨w, _⟩ := exists_exact_lowerSet_walk s t
  exact ⟨w⟩

/-- Graph shortest-path distance equals the number of separating causal
events. -/
theorem lowerSetTransitionGraph_dist_eq (s t : LowerSet α) :
    lowerSetTransitionGraph.dist s t = lowerSetDistance s t := by
  obtain ⟨w, hw⟩ := exists_exact_lowerSet_walk s t
  apply le_antisymm
  · exact (SimpleGraph.dist_le w).trans_eq hw
  · have hconn : (lowerSetTransitionGraph (α := α)).Connected :=
      lowerSetTransitionGraph_connected (α := α)
    obtain ⟨v, hv⟩ := hconn.exists_walk_length_eq_dist s t
    exact (lowerSetDistance_le_walk_length v).trans_eq hv

/-- The downset Hasse graph of every finite causal poset is a median graph. -/
theorem lowerSetTransitionGraph_hasUniqueGraphMedian :
    HasUniqueGraphMedian (lowerSetTransitionGraph (α := α)) := by
  intro s t u
  obtain ⟨μ, hμ, huniq⟩ := existsUnique_lowerSetMedian s t u
  refine ⟨μ, ?_, ?_⟩
  · simpa only [lowerSetTransitionGraph_dist_eq] using hμ
  · intro x hx
    apply huniq
    simpa only [lowerSetTransitionGraph_dist_eq] using hx

/-- Explicit partial-cube embedding for the downset geometry of every finite
causal poset. -/
theorem lowerSetTransitionGraph_partialCubeEmbedding :
    Function.Injective (lowerSetCode : LowerSet α → α → Bool) ∧
      ∀ s t : LowerSet α,
        lowerSetTransitionGraph.dist s t =
          hammingDist (lowerSetCode s) (lowerSetCode t) := by
  refine ⟨lowerSetCode_injective, ?_⟩
  intro s t
  exact lowerSetTransitionGraph_dist_eq s t

end FinitePoset

/-! ## Specialization to finite causal algebras -/

/-- Wrapper installing the order carried internally by a causal algebra as a
Lean `PartialOrder`, without creating a global instance on `C.Λ`. -/
structure CausalPoint {k : Type*} [Field k] (C : CAlg k) where
  val : C.Λ

namespace CausalPoint

variable {k : Type*} [Field k] (C : CAlg k)

instance : Fintype (CausalPoint C) :=
  Fintype.ofEquiv C.Λ
    { toFun := fun a => ⟨a⟩
      invFun := fun a => a.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : DecidableEq (CausalPoint C) := fun a b =>
  decidable_of_iff (a.val = b.val) ⟨fun h => by cases a; cases b; cases h; rfl,
    fun h => congrArg CausalPoint.val h⟩

instance : LE (CausalPoint C) where
  le a b := C.le a.val b.val

instance : PartialOrder (CausalPoint C) where
  le_refl a := C.le_refl a.val
  le_trans a b c := C.le_trans a.val b.val c.val
  le_antisymm a b hab hba := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        simp only [CausalPoint.mk.injEq]
        exact C.le_antisymm a b hab hba

end CausalPoint

/-- Intrinsic finite causal states of an arbitrary causal algebra. -/
abbrev CausalDownsetState {k : Type*} [Field k] (C : CAlg k) :=
  LowerSet (CausalPoint C)

/-- The original predicate-based notion of causal-algebra downset is
equivalent to the bundled lower-set state space used by the geometry. -/
def causalDownsetEquiv {k : Type*} [Field k] (C : CAlg k) :
    CausalDownsetState C ≃ {S : Set C.Λ // IsDownset C S} where
  toFun s :=
    ⟨{a | (⟨a⟩ : CausalPoint C) ∈ s}, by
      intro a b hb hab
      exact s.lower hab hb⟩
  invFun S :=
    { carrier := {a | a.val ∈ S.1}
      lower' := by
        intro a b hab hb
        exact S.2 b.val a.val hb hab }
  left_inv s := by
    apply LowerSet.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

/-- Every finite causal algebra therefore has an intrinsic median partial-cube
state geometry, with one Boolean coordinate per causal idempotent/event. -/
theorem causalAlgebra_hasMedianPartialCube {k : Type*} [Field k] (C : CAlg k) :
    HasUniqueGraphMedian
        (lowerSetTransitionGraph (α := CausalPoint C)) ∧
      Function.Injective
        (lowerSetCode : CausalDownsetState C → CausalPoint C → Bool) ∧
      ∀ s t : CausalDownsetState C,
        (lowerSetTransitionGraph (α := CausalPoint C)).dist s t =
          hammingDist (lowerSetCode s) (lowerSetCode t) := by
  exact ⟨lowerSetTransitionGraph_hasUniqueGraphMedian,
    lowerSetTransitionGraph_partialCubeEmbedding⟩

/-! ## A first intrinsic cubical defect -/

section CubicalDefect

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered pairs of distinct edges incident to a vertex. -/
def incidentOrderedPairs (G : SimpleGraph V) (v : V) : Finset (V × V) :=
  Finset.univ.filter fun p => G.Adj v p.1 ∧ G.Adj v p.2 ∧ p.1 ≠ p.2

/-- Incident ordered pairs which extend to a nondegenerate graph square. -/
def squareCompletingOrderedPairs (G : SimpleGraph V) (v : V) : Finset (V × V) :=
  (incidentOrderedPairs G v).filter fun p =>
    ∃ w : V, w ≠ v ∧ G.Adj p.1 w ∧ G.Adj p.2 w

/-- A local, graph-intrinsic two-direction curvature kernel: it is one exactly
when two distinct moves based at `v` do not commute around a square, and zero
otherwise.  This is a discrete sectional obstruction, not a multilinear
Riemann tensor. -/
def cubicalSectionalDefect (G : SimpleGraph V) (v a b : V) : ℕ :=
  if G.Adj v a ∧ G.Adj v b ∧ a ≠ b then
    if ∃ w : V, w ≠ v ∧ G.Adj a w ∧ G.Adj b w then 0 else 1
  else 0

theorem cubicalSectionalDefect_symm (G : SimpleGraph V) (v a b : V) :
    cubicalSectionalDefect G v a b = cubicalSectionalDefect G v b a := by
  unfold cubicalSectionalDefect
  by_cases hinc : G.Adj v a ∧ G.Adj v b ∧ a ≠ b
  · have hinc' : G.Adj v b ∧ G.Adj v a ∧ b ≠ a :=
      ⟨hinc.2.1, hinc.1, Ne.symm hinc.2.2⟩
    rw [if_pos hinc, if_pos hinc']
    by_cases hs : ∃ w : V, w ≠ v ∧ G.Adj a w ∧ G.Adj b w
    · have hs' : ∃ w : V, w ≠ v ∧ G.Adj b w ∧ G.Adj a w := by
        obtain ⟨w, hwv, haw, hbw⟩ := hs
        exact ⟨w, hwv, hbw, haw⟩
      rw [if_pos hs, if_pos hs']
    · have hs' : ¬ ∃ w : V, w ≠ v ∧ G.Adj b w ∧ G.Adj a w := by
        rintro ⟨w, hwv, hbw, haw⟩
        exact hs ⟨w, hwv, haw, hbw⟩
      rw [if_neg hs, if_neg hs']
  · have hinc' : ¬ (G.Adj v b ∧ G.Adj v a ∧ b ≠ a) := by
      rintro ⟨hvb, hva, hba⟩
      exact hinc ⟨hva, hvb, Ne.symm hba⟩
    rw [if_neg hinc, if_neg hinc']

@[simp]
theorem cubicalSectionalDefect_self (G : SimpleGraph V) (v a : V) :
    cubicalSectionalDefect G v a a = 0 := by
  simp [cubicalSectionalDefect]

/-- Number of ordered incident move-pairs which fail to commute by completing
to a square.  Zero means every pair of local directions commutes. -/
def squareCompletionDefect (G : SimpleGraph V) (v : V) : ℕ :=
  (incidentOrderedPairs G v).card - (squareCompletingOrderedPairs G v).card

theorem squareCompletingOrderedPairs_subset (G : SimpleGraph V) (v : V) :
    squareCompletingOrderedPairs G v ⊆ incidentOrderedPairs G v := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem squareCompletingOrderedPairs_card_le (G : SimpleGraph V) (v : V) :
    (squareCompletingOrderedPairs G v).card ≤ (incidentOrderedPairs G v).card :=
  Finset.card_le_card (squareCompletingOrderedPairs_subset G v)

@[simp]
theorem squareCompletionDefect_eq_zero_iff (G : SimpleGraph V) (v : V) :
    squareCompletionDefect G v = 0 ↔
      squareCompletingOrderedPairs G v = incidentOrderedPairs G v := by
  rw [squareCompletionDefect, Nat.sub_eq_zero_iff_le]
  constructor
  · intro hle
    apply Finset.eq_of_subset_of_card_le
      (squareCompletingOrderedPairs_subset G v)
    exact hle
  · intro h
    rw [h]

/-- Semantic zero-curvature criterion: the local defect vanishes exactly when
every pair of distinct incident directions completes to a square. -/
theorem squareCompletionDefect_eq_zero_iff_every_pair
    (G : SimpleGraph V) (v : V) :
    squareCompletionDefect G v = 0 ↔
      ∀ a b : V, G.Adj v a → G.Adj v b → a ≠ b →
        ∃ w : V, w ≠ v ∧ G.Adj a w ∧ G.Adj b w := by
  rw [squareCompletionDefect_eq_zero_iff]
  constructor
  · intro heq a b hva hvb hab
    have hp : (a, b) ∈ incidentOrderedPairs G v := by
      simp [incidentOrderedPairs, hva, hvb, hab]
    have hp' : (a, b) ∈ squareCompletingOrderedPairs G v := by
      rw [heq]
      exact hp
    exact (Finset.mem_filter.mp hp').2
  · intro h
    apply Finset.Subset.antisymm (squareCompletingOrderedPairs_subset G v)
    intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨hp, ?_⟩
    have hp' : G.Adj v p.1 ∧ G.Adj v p.2 ∧ p.1 ≠ p.2 := by
      simpa [incidentOrderedPairs] using hp
    exact h p.1 p.2 hp'.1 hp'.2.1 hp'.2.2

/-- A positive local defect is witnessed by a concrete pair of causal moves
which cannot be performed in either order around a square. -/
theorem squareCompletionDefect_pos_of_noncommuting_pair
    (G : SimpleGraph V) (v a b : V)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    (hnosquare : ¬ ∃ w : V, w ≠ v ∧ G.Adj a w ∧ G.Adj b w) :
    0 < squareCompletionDefect G v := by
  rw [Nat.pos_iff_ne_zero]
  intro hzero
  have hall := (squareCompletionDefect_eq_zero_iff_every_pair G v).mp hzero
  exact hnosquare (hall a b hva hvb hab)

end CubicalDefect

/-! ### A certified causal-order obstruction -/

/-- The state graph of a two-event causal chain: the three vertices represent
the empty downset, the first event, and both events. -/
def twoEventChainStateGraph : SimpleGraph (Fin 3) where
  Adj a b := Nat.dist a.val b.val = 1
  symm := by
    intro a b h
    rwa [Nat.dist_comm]
  loopless := by
    constructor
    intro a h
    simp at h

/-- At the middle state of a two-event causal chain, undoing the first event
and doing the second event are two incident moves which cannot commute around
a square.  Hence the intrinsic cubical defect is strictly positive. -/
theorem twoEventChain_middle_has_positive_defect :
    0 < squareCompletionDefect twoEventChainStateGraph (1 : Fin 3) := by
  apply squareCompletionDefect_pos_of_noncommuting_pair
    twoEventChainStateGraph (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)
  · rfl
  · rfl
  · decide
  · rintro ⟨w, hwne, h0w, h2w⟩
    have hwval : w.val = 1 := by
      change Nat.dist 0 w.val = 1 at h0w
      rw [Nat.dist_zero_left] at h0w
      exact h0w
    apply hwne
    apply Fin.ext
    exact hwval

section LowerSetDefect

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

noncomputable instance : Fintype (LowerSet α) :=
  Fintype.ofInjective
    (lowerSetCode : LowerSet α → α → Bool) lowerSetCode_injective

/-- The local square-completion defect specialized to finite causal states. -/
def lowerSetSquareCompletionDefect (s : LowerSet α) : ℕ :=
  squareCompletionDefect (lowerSetTransitionGraph (α := α)) s

/-- Two-direction cubical obstruction specialized to finite causal states. -/
def lowerSetCubicalSectionalDefect (s a b : LowerSet α) : ℕ :=
  cubicalSectionalDefect (lowerSetTransitionGraph (α := α)) s a b

end LowerSetDefect

section CausalAlgebraDefect

variable {k : Type*} [Field k] (C : CAlg k)

/-- Total local noncommutation defect of a state of a finite causal algebra. -/
def causalAlgebraSquareCompletionDefect (s : CausalDownsetState C) : ℕ :=
  lowerSetSquareCompletionDefect s

/-- Sectional noncommutation kernel for two moves based at a causal-algebra
state. -/
def causalAlgebraCubicalSectionalDefect
    (s a b : CausalDownsetState C) : ℕ :=
  lowerSetCubicalSectionalDefect s a b

end CausalAlgebraDefect

end
end CausalAlgebraicGeometry.CAGFiniteCausalGeometry
