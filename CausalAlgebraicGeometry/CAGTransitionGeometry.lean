/-
  CAGTransitionGeometry.lean — The single-cell transition graph of CAG
  boundary profiles.

  Two boundary states are adjacent when their intrinsic L¹ distance is one.
  This file proves constructively that every pair is joined by a walk whose
  length is exactly that distance.  Hence the graph shortest-path metric is
  the boundary metric, and the unique profile median from
  `CAGMedianGeometry` is also the unique graph median.

  The key local lemma raises a profile at a minimal point where it differs
  from a larger profile.  Minimality makes the one-cell move antitone-safe.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGMedianGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.InformationTheory.Hamming
import Mathlib.Order.Preorder.Finite

namespace CausalAlgebraicGeometry.CAGTransitionGeometry

open CausalAlgebraicGeometry.C3BarrierLowerBound
open CausalAlgebraicGeometry.CAGBoundaryGeometry
open CausalAlgebraicGeometry.CAGMedianGeometry

noncomputable section
open scoped Classical

/-! ## One admissible cell move -/

/-- Raise one height by one.  The safety condition says every strict
predecessor has enough clearance to preserve antitonicity. -/
def raiseProfileAt {d m : ℕ} (p : AntitoneProfile d m)
    (x : Fin d → Fin m) (hx : (p.toFun x).val < m)
    (hsafe : ∀ y, y ≤ x → y ≠ x → (p.toFun x).val < (p.toFun y).val) :
    AntitoneProfile d m where
  toFun f := if f = x then
      ⟨(p.toFun x).val + 1, by omega⟩
    else p.toFun f
  antitone := by
    intro f g hfg
    by_cases hfx : f = x
    · subst f
      by_cases hgx : g = x
      · subst g
        exact le_rfl
      · change (if g = x then _ else p.toFun g) ≤
          (if x = x then _ else p.toFun x)
        rw [if_neg hgx, if_pos rfl]
        exact (p.antitone hfg).trans (Fin.mk_le_mk.mpr (Nat.le_succ _))
    · by_cases hgx : g = x
      · subst g
        change (if x = x then _ else p.toFun x) ≤
          (if f = x then _ else p.toFun f)
        rw [if_pos rfl, if_neg hfx]
        apply Fin.mk_le_mk.mpr
        exact Nat.succ_le_of_lt (hsafe f hfg hfx)
      · change (if g = x then _ else p.toFun g) ≤
          (if f = x then _ else p.toFun f)
        rw [if_neg hgx, if_neg hfx]
        exact p.antitone hfg

@[simp]
theorem raiseProfileAt_self_val {d m : ℕ} (p : AntitoneProfile d m)
    (x : Fin d → Fin m) (hx) (hsafe) :
    ((raiseProfileAt p x hx hsafe).toFun x).val = (p.toFun x).val + 1 := by
  simp [raiseProfileAt]

theorem raiseProfileAt_other {d m : ℕ} (p : AntitoneProfile d m)
    (x : Fin d → Fin m) (hx) (hsafe) {f : Fin d → Fin m} (hfx : f ≠ x) :
    (raiseProfileAt p x hx hsafe).toFun f = p.toFun f := by
  simp [raiseProfileAt, hfx]

theorem le_raiseProfileAt {d m : ℕ} (p : AntitoneProfile d m)
    (x : Fin d → Fin m) (hx) (hsafe) :
    p ≤ raiseProfileAt p x hx hsafe := by
  intro f
  by_cases hfx : f = x
  · subst f
    change p.toFun x ≤
      (if x = x then ⟨(p.toFun x).val + 1, by omega⟩ else p.toFun x)
    rw [if_pos rfl]
    apply Fin.mk_le_mk.mpr
    simpa only [Fin.val_mk] using Nat.le_succ (p.toFun x).val
  · rw [raiseProfileAt_other p x hx hsafe hfx]

/-- A safe raise changes exactly one unit cell. -/
theorem boundaryDistanceNat_raiseProfileAt {d m : ℕ}
    (p : AntitoneProfile d m) (x : Fin d → Fin m) (hx) (hsafe) :
    boundaryDistanceNat p (raiseProfileAt p x hx hsafe) = 1 := by
  unfold boundaryDistanceNat
  rw [Finset.sum_eq_single x]
  · simp only [raiseProfileAt_self_val, Nat.dist]
    omega
  · intro f _ hfx
    rw [raiseProfileAt_other p x hx hsafe hfx]
    exact Nat.dist_self _
  · intro hxmem
    exact False.elim (hxmem (Finset.mem_univ x))

/-- Between any two strictly ordered profiles there is an admissible
one-cell state immediately above the lower profile and still below the upper
profile. -/
theorem exists_singleCell_above_of_lt {d m : ℕ}
    {p q : AntitoneProfile d m} (hpq : p < q) :
    ∃ r : AntitoneProfile d m,
      p ≤ r ∧ r ≤ q ∧ boundaryDistanceNat p r = 1 := by
  let S : Finset (Fin d → Fin m) :=
    Finset.univ.filter (fun f => p.toFun f < q.toFun f)
  have hneFun : p.toFun ≠ q.toFun := by
    intro h
    exact hpq.ne (AntitoneProfile.ext h)
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hneFun
  have hx₀le : p.toFun x₀ ≤ q.toFun x₀ := hpq.le x₀
  have hx₀lt : p.toFun x₀ < q.toFun x₀ := lt_of_le_of_ne hx₀le hx₀
  have hSne : S.Nonempty := by
    exact ⟨x₀, by simp [S, hx₀lt]⟩
  obtain ⟨x, hxmin⟩ := S.exists_minimal hSne
  have hxdisc : p.toFun x < q.toFun x := by
    simpa [S] using hxmin.1
  have hxbound : (p.toFun x).val < m := by
    have hqbound := (q.toFun x).isLt
    exact lt_of_lt_of_le (Fin.mk_lt_mk.mp hxdisc) (Nat.le_of_lt_succ hqbound)
  have hsafe : ∀ y, y ≤ x → y ≠ x →
      (p.toFun x).val < (p.toFun y).val := by
    intro y hyx hyne
    have hpanti := Fin.le_def.mp (p.antitone hyx)
    have hqanti := Fin.le_def.mp (q.antitone hyx)
    by_contra hnot
    have heq : (p.toFun y).val = (p.toFun x).val := by omega
    have hydisc : p.toFun y < q.toFun y := by
      apply Fin.mk_lt_mk.mpr
      have hxd := Fin.mk_lt_mk.mp hxdisc
      calc
        (p.toFun y).val = (p.toFun x).val := heq
        _ < (q.toFun x).val := hxd
        _ ≤ (q.toFun y).val := hqanti
    have hymem : y ∈ S := by simp [S, hydisc]
    have hxy : x ≤ y := hxmin.2 hymem hyx
    exact hyne (le_antisymm hyx hxy)
  let r := raiseProfileAt p x hxbound hsafe
  have hpr : p ≤ r := le_raiseProfileAt p x hxbound hsafe
  have hrq : r ≤ q := by
    intro f
    by_cases hfx : f = x
    · subst f
      change (raiseProfileAt p x hxbound hsafe).toFun x ≤ q.toFun x
      change (if x = x then ⟨(p.toFun x).val + 1, by omega⟩ else p.toFun x) ≤
        q.toFun x
      rw [if_pos rfl]
      apply Fin.mk_le_mk.mpr
      exact Nat.succ_le_of_lt (Fin.mk_lt_mk.mp hxdisc)
    · change (raiseProfileAt p x hxbound hsafe).toFun f ≤ q.toFun f
      rw [raiseProfileAt_other p x hxbound hsafe hfx]
      exact hpq.le f
  exact ⟨r, hpr, hrq, boundaryDistanceNat_raiseProfileAt p x hxbound hsafe⟩

/-! ## The transition graph and exact walks -/

/-- The graph whose edges are admissible one-cell changes of boundary state. -/
def boundaryTransitionGraph (d m : ℕ) : SimpleGraph (AntitoneProfile d m) where
  Adj p q := boundaryDistanceNat p q = 1
  symm := by
    intro p q hpq
    rwa [boundaryDistanceNat_comm]
  loopless := by
    constructor
    intro p hp
    rw [boundaryDistanceNat_self] at hp
    omega

@[simp]
theorem boundaryTransitionGraph_adj_iff {d m : ℕ}
    (p q : AntitoneProfile d m) :
    (boundaryTransitionGraph d m).Adj p q ↔ boundaryDistanceNat p q = 1 :=
  Iff.rfl

/-- Every graph walk is at least as long as the boundary metric between its
endpoints. -/
theorem boundaryDistanceNat_le_walk_length {d m : ℕ}
    {p q : AntitoneProfile d m}
    (w : (boundaryTransitionGraph d m).Walk p q) :
    boundaryDistanceNat p q ≤ w.length := by
  induction w with
  | nil => simp
  | @cons p r q hpr w ih =>
      have hstep : boundaryDistanceNat p r = 1 := hpr
      have htri := boundaryDistanceNat_triangle p r q
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- A state lying pointwise between two comparable profiles saturates the
metric triangle inequality. -/
theorem boundaryDistanceNat_split_of_le {d m : ℕ}
    {p r q : AntitoneProfile d m} (hpr : p ≤ r) (hrq : r ≤ q) :
    boundaryDistanceNat p q =
      boundaryDistanceNat p r + boundaryDistanceNat r q := by
  unfold boundaryDistanceNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  have h₁ := Fin.le_def.mp (hpr f)
  have h₂ := Fin.le_def.mp (hrq f)
  rw [Nat.dist_eq_sub_of_le (h₁.trans h₂),
    Nat.dist_eq_sub_of_le h₁, Nat.dist_eq_sub_of_le h₂]
  omega

/-- An ordered unit-distance pair is a cover in the profile lattice. -/
theorem covBy_of_le_boundaryDistanceNat_eq_one {d m : ℕ}
    {p q : AntitoneProfile d m} (hpq : p ≤ q)
    (hdist : boundaryDistanceNat p q = 1) : p ⋖ q := by
  have hpqne : p ≠ q := by
    intro heq
    subst q
    simp at hdist
  refine ⟨lt_of_le_of_ne hpq hpqne, ?_⟩
  intro r hpr hrq
  have hsplit := boundaryDistanceNat_split_of_le hpr.le hrq.le
  have hprpos : 0 < boundaryDistanceNat p r := by
    apply Nat.pos_of_ne_zero
    intro hz
    have heq := (boundaryDistanceNat_eq_zero_iff p r).mp hz
    exact hpr.ne heq
  have hrqpos : 0 < boundaryDistanceNat r q := by
    apply Nat.pos_of_ne_zero
    intro hz
    have heq := (boundaryDistanceNat_eq_zero_iff r q).mp hz
    exact hrq.ne heq
  omega

/-- Every cover in the profile lattice changes exactly one unit cell. -/
theorem boundaryDistanceNat_eq_one_of_covBy {d m : ℕ}
    {p q : AntitoneProfile d m} (hpq : p ⋖ q) :
    boundaryDistanceNat p q = 1 := by
  obtain ⟨r, hpr, hrq, hstep⟩ := exists_singleCell_above_of_lt hpq.lt
  rcases hpq.eq_or_eq hpr hrq with hrp | hrq'
  · subst r
    simp at hstep
  · subst r
    exact hstep

/-- The single-cell graph is exactly the undirected Hasse graph of the finite
profile lattice. -/
theorem boundaryTransitionGraph_adj_iff_covBy {d m : ℕ}
    (p q : AntitoneProfile d m) :
    (boundaryTransitionGraph d m).Adj p q ↔ p ⋖ q ∨ q ⋖ p := by
  constructor
  · intro hdist
    have hdist' : boundaryDistanceNat p q = 1 := hdist
    have hsplit := boundaryDistanceNat_split_inf p q
    have hzero : boundaryDistanceNat p (p ⊓ q) = 0 ∨
        boundaryDistanceNat (p ⊓ q) q = 0 := by
      omega
    rcases hzero with hpzero | hqzero
    · have hpinf := (boundaryDistanceNat_eq_zero_iff p (p ⊓ q)).mp hpzero
      have hpq : p ≤ q := by rw [hpinf]; exact inf_le_right
      exact Or.inl (covBy_of_le_boundaryDistanceNat_eq_one hpq hdist')
    · have hinfq := (boundaryDistanceNat_eq_zero_iff (p ⊓ q) q).mp hqzero
      have hqp : q ≤ p := by rw [← hinfq]; exact inf_le_left
      exact Or.inr (covBy_of_le_boundaryDistanceNat_eq_one hqp
        (by rwa [boundaryDistanceNat_comm]))
  · rintro (hpq | hqp)
    · change boundaryDistanceNat p q = 1
      exact boundaryDistanceNat_eq_one_of_covBy hpq
    · change boundaryDistanceNat p q = 1
      rw [boundaryDistanceNat_comm]
      exact boundaryDistanceNat_eq_one_of_covBy hqp

/-- Comparable profiles admit a monotone one-cell walk of exactly their L¹
distance. -/
theorem exists_exact_walk_of_le {d m : ℕ}
    {p q : AntitoneProfile d m} (hpq : p ≤ q) :
    ∃ w : (boundaryTransitionGraph d m).Walk p q,
      w.length = boundaryDistanceNat p q := by
  let P : ℕ → Prop := fun n =>
    ∀ (a b : AntitoneProfile d m), a ≤ b →
      boundaryDistanceNat a b = n →
      ∃ w : (boundaryTransitionGraph d m).Walk a b, w.length = n
  have hP : ∀ n : ℕ, (∀ k < n, P k) → P n := by
    intro n ih a b hab hdist
    by_cases heq : a = b
    · subst b
      have hn : n = 0 := by simpa using hdist.symm
      subst n
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      simp
    · have hlt : a < b := lt_of_le_of_ne hab heq
      obtain ⟨r, har, hrb, hstep⟩ := exists_singleCell_above_of_lt hlt
      have hsplit := boundaryDistanceNat_split_of_le har hrb
      have hrlt : boundaryDistanceNat r b < n := by omega
      obtain ⟨w, hw⟩ := ih (boundaryDistanceNat r b) hrlt r b hrb rfl
      refine ⟨SimpleGraph.Walk.cons ?_ w, ?_⟩
      · exact hstep
      · simp only [SimpleGraph.Walk.length_cons, hw]
        omega
  have hall : ∀ n, P n := fun n => Nat.strong_induction_on n hP
  exact hall (boundaryDistanceNat p q) p q hpq rfl

/-- Every two profiles admit a one-cell walk whose length is exactly their
boundary distance. -/
theorem exists_exact_boundary_walk {d m : ℕ}
    (p q : AntitoneProfile d m) :
    ∃ w : (boundaryTransitionGraph d m).Walk p q,
      w.length = boundaryDistanceNat p q := by
  obtain ⟨wp, hwp⟩ := exists_exact_walk_of_le (inf_le_left : p ⊓ q ≤ p)
  obtain ⟨wq, hwq⟩ := exists_exact_walk_of_le (inf_le_right : p ⊓ q ≤ q)
  let w := wp.reverse.append wq
  refine ⟨w, ?_⟩
  have hsplit := boundaryDistanceNat_split_inf p q
  have hcomm := boundaryDistanceNat_comm (p ⊓ q) p
  simp only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    hwp, hwq]
  omega

/-- The one-cell transition graph is connected. -/
theorem boundaryTransitionGraph_connected (d m : ℕ) :
    (boundaryTransitionGraph d m).Connected := by
  refine { nonempty := ⟨emptyProfile d m⟩, preconnected := ?_ }
  intro p q
  obtain ⟨w, _⟩ := exists_exact_boundary_walk p q
  exact ⟨w⟩

/-- **EXACT TRANSITION-METRIC THEOREM.**  Graph shortest-path distance in the
single-cell transition graph equals the intrinsic CAG boundary metric. -/
theorem boundaryTransitionGraph_dist_eq {d m : ℕ}
    (p q : AntitoneProfile d m) :
    (boundaryTransitionGraph d m).dist p q = boundaryDistanceNat p q := by
  obtain ⟨w, hw⟩ := exists_exact_boundary_walk p q
  apply le_antisymm
  · exact (SimpleGraph.dist_le w).trans_eq hw
  · have hconn := boundaryTransitionGraph_connected d m
    obtain ⟨v, hv⟩ := hconn.exists_walk_length_eq_dist p q
    exact (boundaryDistanceNat_le_walk_length v).trans_eq hv

/-! ## Median graph consequence -/

/-- Metric characterization of a median graph, stated directly to avoid
depending on a separate graph-class API. -/
def HasUniqueGraphMedian {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ p q r : V, ∃! x : V,
    G.dist p q = G.dist p x + G.dist x q ∧
    G.dist q r = G.dist q x + G.dist x r ∧
    G.dist r p = G.dist r x + G.dist x p

/-- The CAG one-cell transition graph is a median graph: every triple has a
unique vertex on shortest paths between all three pairs. -/
theorem boundaryTransitionGraph_hasUniqueGraphMedian (d m : ℕ) :
    HasUniqueGraphMedian (boundaryTransitionGraph d m) := by
  intro p q r
  obtain ⟨μ, hμ, huniq⟩ := existsUnique_profileMedian p q r
  refine ⟨μ, ?_, ?_⟩
  · simpa only [boundaryTransitionGraph_dist_eq] using hμ
  · intro x hx
    apply huniq
    simpa only [boundaryTransitionGraph_dist_eq] using hx

/-! ## Explicit partial-cube embedding -/

/-- A vertical unit cell over a boundary base point. -/
abbrev BoundaryCell (d m : ℕ) := (Fin d → Fin m) × Fin m

/-- Unary threshold code for a bounded height. -/
def unaryHeightCode {m : ℕ} (a : Fin (m + 1)) (z : Fin m) : Bool :=
  decide (z.val < a.val)

private theorem hammingDist_unaryHeightCode_of_le {m : ℕ}
    (a b : Fin (m + 1)) (hab : a.val ≤ b.val) :
    hammingDist (unaryHeightCode a) (unaryHeightCode b) = b.val - a.val := by
  let D : Finset (Fin m) :=
    Finset.univ.filter (fun z => unaryHeightCode a z ≠ unaryHeightCode b z)
  let I : Finset (Fin m) :=
    Finset.univ.filter (fun z => a.val ≤ z.val ∧ z.val < b.val)
  let A : Finset (Fin m) := Finset.univ.filter (fun z => z.val < a.val)
  let B : Finset (Fin m) := Finset.univ.filter (fun z => z.val < b.val)
  have hdiff : D = I := by
    ext z
    by_cases hza : z.val < a.val <;> by_cases hzb : z.val < b.val
      <;> simp [D, I, unaryHeightCode, hza, hzb]
      <;> omega
  have hsdiff : I = B \ A := by
    ext z
    simp only [I, A, B, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    omega
  have hsubset : A ⊆ B := by
    intro z hz
    have hz' : z.val < a.val := by simpa [A] using hz
    have : z.val < b.val := lt_of_lt_of_le hz' hab
    simpa [B] using this
  unfold hammingDist
  change D.card = b.val - a.val
  rw [hdiff, hsdiff, Finset.card_sdiff_of_subset hsubset]
  simp only [A, B, Fin.card_filter_val_lt]
  have ha : a.val ≤ m := Nat.le_of_lt_succ a.isLt
  have hb : b.val ≤ m := Nat.le_of_lt_succ b.isLt
  rw [min_eq_right ha, min_eq_right hb]

theorem hammingDist_unaryHeightCode {m : ℕ} (a b : Fin (m + 1)) :
    hammingDist (unaryHeightCode a) (unaryHeightCode b) =
      Nat.dist a.val b.val := by
  rcases le_total a.val b.val with hab | hba
  · rw [hammingDist_unaryHeightCode_of_le a b hab,
      Nat.dist_eq_sub_of_le hab]
  · rw [hammingDist_comm,
      hammingDist_unaryHeightCode_of_le b a hba,
      Nat.dist_eq_sub_of_le_right hba]

/-- Binary occupancy vector of all unit cells below a profile. -/
def profileCellCode {d m : ℕ} (p : AntitoneProfile d m) :
    BoundaryCell d m → Bool :=
  fun c => unaryHeightCode (p.toFun c.1) c.2

private theorem hammingDist_eq_sum_indicator {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, DecidableEq (β i)] (x y : ∀ i, β i) :
    hammingDist x y = ∑ i, if x i ≠ y i then 1 else 0 := by
  unfold hammingDist
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Cell occupancy is an exact Hamming realization of the boundary metric. -/
theorem hammingDist_profileCellCode {d m : ℕ}
    (p q : AntitoneProfile d m) :
    hammingDist (profileCellCode p) (profileCellCode q) =
      boundaryDistanceNat p q := by
  rw [hammingDist_eq_sum_indicator]
  unfold boundaryDistanceNat
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro f _
  rw [← hammingDist_eq_sum_indicator]
  exact hammingDist_unaryHeightCode (p.toFun f) (q.toFun f)

/-- The Boolean cell code loses no boundary-state information. -/
theorem profileCellCode_injective {d m : ℕ} :
    Function.Injective (profileCellCode : AntitoneProfile d m → BoundaryCell d m → Bool) := by
  intro p q hpq
  apply (boundaryDistanceNat_eq_zero_iff p q).mp
  have hdist := hammingDist_profileCellCode p q
  rw [hpq, hammingDist_self] at hdist
  exact hdist.symm

/-- **EXPLICIT PARTIAL-CUBE THEOREM.**  The transition graph embeds
injectively and isometrically into the Boolean Hamming cube indexed by causal
unit cells.  This is the concrete partial-cube realization of CAG boundary
geometry. -/
theorem boundaryTransitionGraph_partialCubeEmbedding (d m : ℕ) :
    Function.Injective
        (profileCellCode : AntitoneProfile d m → BoundaryCell d m → Bool) ∧
      ∀ p q : AntitoneProfile d m,
        (boundaryTransitionGraph d m).dist p q =
          hammingDist (profileCellCode p) (profileCellCode q) := by
  refine ⟨profileCellCode_injective, ?_⟩
  intro p q
  rw [boundaryTransitionGraph_dist_eq, hammingDist_profileCellCode]

end
end CausalAlgebraicGeometry.CAGTransitionGeometry
