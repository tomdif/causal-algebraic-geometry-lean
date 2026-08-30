/-
  CAGCubicalComplex.lean — Higher cubes, event hyperplanes, and link
  operators for finite causal-state geometry.

  Causal states are lower sets.  A family of events which are all addable at
  one state can be toggled independently, producing a Boolean cube inside the
  transition graph.  This file defines those cubes and proves that every one
  is embedded isometrically, with distance equal to symmetric-difference
  cardinality of its direction subsets.

  Every causal event also defines a canonical hyperplane/wall.  The number of
  such walls separating two states is exactly their graph distance.  Finally,
  the cubical link at a state records precisely which incident moves complete
  to squares, and its graph Laplacian supplies the first intrinsic link
  operator.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGFiniteCausalDynamics
import Mathlib.Data.Finset.SymmDiff

namespace CausalAlgebraicGeometry.CAGCubicalComplex

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGFiniteCausalDynamics

noncomputable section
open scoped Classical symmDiff

/-! ## Event hyperplanes and wall distance -/

section EventWalls

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Causal-event coordinates whose occupancies distinguish two states. -/
def separatingEvents (s t : LowerSet α) : Finset α :=
  Finset.univ.filter fun a => (a ∈ s) ≠ (a ∈ t)

@[simp]
theorem mem_separatingEvents_iff {s t : LowerSet α} {a : α} :
    a ∈ separatingEvents s t ↔ (a ∈ s) ≠ (a ∈ t) := by
  simp [separatingEvents]

/-- Each event is a canonical Boolean hyperplane, and distance is exactly the
number of event hyperplanes separating the two causal states. -/
theorem lowerSetDistance_eq_card_separatingEvents (s t : LowerSet α) :
    lowerSetDistance s t = (separatingEvents s t).card := by
  simpa [separatingEvents] using lowerSetDistance_eq_card_filter s t

/-- Hyperplane separation is also the exact transition-graph distance. -/
theorem lowerSetGraphDistance_eq_card_separatingEvents (s t : LowerSet α) :
    (lowerSetTransitionGraph (α := α)).dist s t =
      (separatingEvents s t).card := by
  rw [lowerSetTransitionGraph_dist_eq,
    lowerSetDistance_eq_card_separatingEvents]

@[simp]
theorem separatingEvents_eq_empty_iff (s t : LowerSet α) :
    separatingEvents s t = ∅ ↔ s = t := by
  constructor
  · intro h
    apply (lowerSetDistance_eq_zero_iff s t).mp
    rw [lowerSetDistance_eq_card_separatingEvents, h]
    rfl
  · rintro rfl
    ext a
    simp

/-- Every transition edge crosses one and only one event hyperplane. -/
theorem existsUnique_separatingEvent_of_adj {s t : LowerSet α}
    (hst : (lowerSetTransitionGraph (α := α)).Adj s t) :
    ∃! a : α, a ∈ separatingEvents s t := by
  have hcard : (separatingEvents s t).card = 1 := by
    rw [← lowerSetDistance_eq_card_separatingEvents]
    exact hst
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ?_, ?_⟩
  · rw [ha]
    simp
  · intro b hb
    rw [ha] at hb
    simpa using hb

end EventWalls

/-! ## Higher-dimensional causal cubes -/

section CausalCubes

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- An event is addable at a causal state when it is absent but all of its
strict causal predecessors are already present. -/
def AddableEvent (s : LowerSet α) (a : α) : Prop :=
  a ∉ s ∧ ∀ b : α, b ≤ a → b ≠ a → b ∈ s

/-- A causal cube consists of a base state and a finite family of events all
independently addable at that base. -/
structure CausalCube (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] where
  base : LowerSet α
  directions : Finset α
  addable : ∀ a ∈ directions, AddableEvent base a

namespace CausalCube

/-- Dimension of a causal cube. -/
def dimension (Q : CausalCube α) : ℕ := Q.directions.card

/-- Direction subsets indexing the Boolean faces/vertices of a cube. -/
abbrev Face (Q : CausalCube α) :=
  {T : Finset α // T ⊆ Q.directions}

/-- The state obtained by adding a selected subset of independent cube
directions to the base state. -/
def vertex (Q : CausalCube α) (T : Q.Face) : LowerSet α where
  carrier := (Q.base : Set α) ∪ (T.1 : Set α)
  lower' := by
    intro a b hab hb
    rcases hb with hb | hb
    · exact Or.inl (Q.base.lower hab hb)
    · by_cases hab' : a = b
      · subst b
        exact Or.inr hb
      · exact Or.inl
          ((Q.addable a (T.2 hb)).2 b hab (Ne.symm hab'))

@[simp]
theorem mem_vertex_iff (Q : CausalCube α) (T : Q.Face) (a : α) :
    a ∈ Q.vertex T ↔ a ∈ Q.base ∨ a ∈ T.1 :=
  Iff.rfl

/-- Cube directions are pairwise causally incomparable.  This is why they can
be added in arbitrary order. -/
theorem directions_incomparable (Q : CausalCube α) {a b : α}
    (ha : a ∈ Q.directions) (hb : b ∈ Q.directions) (hne : a ≠ b) :
    ¬ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro hab
    exact (Q.addable a ha).1 ((Q.addable b hb).2 a hab hne)
  · intro hba
    exact (Q.addable b hb).1 ((Q.addable a ha).2 b hba (Ne.symm hne))

/-- Distinct Boolean faces of a causal cube give distinct causal states. -/
theorem vertex_injective (Q : CausalCube α) :
    Function.Injective Q.vertex := by
  intro T U hTU
  apply Subtype.ext
  apply Finset.ext
  intro a
  constructor
  · intro haT
    have haD : a ∈ Q.directions := T.2 haT
    have ha0 : a ∉ Q.base := (Q.addable a haD).1
    have hva : a ∈ Q.vertex T := (mem_vertex_iff Q T a).2 (Or.inr haT)
    have hva' : a ∈ Q.vertex U := by rwa [← hTU]
    exact ((mem_vertex_iff Q U a).1 hva').resolve_left ha0
  · intro haU
    have haD : a ∈ Q.directions := U.2 haU
    have ha0 : a ∉ Q.base := (Q.addable a haD).1
    have hva : a ∈ Q.vertex U := (mem_vertex_iff Q U a).2 (Or.inr haU)
    have hva' : a ∈ Q.vertex T := by rwa [hTU]
    exact ((mem_vertex_iff Q T a).1 hva').resolve_left ha0

/-- Inside a causal cube, the separating event walls are precisely the
symmetric difference of the chosen direction subsets. -/
theorem separatingEvents_vertex (Q : CausalCube α) (T U : Q.Face) :
    separatingEvents (Q.vertex T) (Q.vertex U) = T.1 ∆ U.1 := by
  ext a
  by_cases haT : a ∈ T.1
  · have haD : a ∈ Q.directions := T.2 haT
    have ha0 : a ∉ Q.base := (Q.addable a haD).1
    by_cases haU : a ∈ U.1 <;>
      simp [separatingEvents, Finset.mem_symmDiff, mem_vertex_iff,
        haT, haU, ha0]
  · by_cases haU : a ∈ U.1
    · have haD : a ∈ Q.directions := U.2 haU
      have ha0 : a ∉ Q.base := (Q.addable a haD).1
      simp [separatingEvents, Finset.mem_symmDiff, mem_vertex_iff,
        haT, haU, ha0]
    · by_cases ha0 : a ∈ Q.base <;>
        simp [separatingEvents, Finset.mem_symmDiff, mem_vertex_iff,
          haT, haU, ha0]

/-- Every causal cube is an exact Hamming/Boolean metric cube. -/
theorem distance_vertex_eq_card_symmDiff (Q : CausalCube α) (T U : Q.Face) :
    lowerSetDistance (Q.vertex T) (Q.vertex U) = (T.1 ∆ U.1).card := by
  rw [lowerSetDistance_eq_card_separatingEvents,
    separatingEvents_vertex]

/-- The cube is isometric for the intrinsic shortest-path metric as well. -/
theorem graphDistance_vertex_eq_card_symmDiff
    (Q : CausalCube α) (T U : Q.Face) :
    (lowerSetTransitionGraph (α := α)).dist (Q.vertex T) (Q.vertex U) =
      (T.1 ∆ U.1).card := by
  rw [lowerSetTransitionGraph_dist_eq,
    distance_vertex_eq_card_symmDiff]

/-- Cube vertices are adjacent exactly when their direction subsets differ in
one coordinate. -/
theorem vertex_adj_iff_card_symmDiff_eq_one
    (Q : CausalCube α) (T U : Q.Face) :
    (lowerSetTransitionGraph (α := α)).Adj (Q.vertex T) (Q.vertex U) ↔
      (T.1 ∆ U.1).card = 1 := by
  change lowerSetDistance (Q.vertex T) (Q.vertex U) = 1 ↔ _
  rw [distance_vertex_eq_card_symmDiff]

/-- Restricting the directions produces a cubical face. -/
def restrict (Q : CausalCube α) (D : Finset α) (hD : D ⊆ Q.directions) :
    CausalCube α where
  base := Q.base
  directions := D
  addable a ha := Q.addable a (hD ha)

@[simp]
theorem dimension_restrict (Q : CausalCube α) (D : Finset α)
    (hD : D ⊆ Q.directions) :
    (Q.restrict D hD).dimension = D.card := rfl

/-- The upper face based at a selected cube vertex, using all directions not
already selected.  Together with `restrict`, this gives closure under the two
types of Boolean cubical face. -/
def upperFace (Q : CausalCube α) (T : Q.Face) : CausalCube α where
  base := Q.vertex T
  directions := Q.directions \ T.1
  addable a ha := by
    have haD : a ∈ Q.directions := (Finset.mem_sdiff.mp ha).1
    have haT : a ∉ T.1 := (Finset.mem_sdiff.mp ha).2
    have hadd := Q.addable a haD
    constructor
    · intro hav
      rcases (mem_vertex_iff Q T a).1 hav with ha0 | haT'
      · exact hadd.1 ha0
      · exact haT haT'
    · intro b hba hne
      exact (mem_vertex_iff Q T b).2 (Or.inl (hadd.2 b hba hne))

/-- Empty direction selection. -/
def emptyFace (Q : CausalCube α) : Q.Face :=
  ⟨∅, Finset.empty_subset _⟩

/-- A one-direction cube vertex. -/
def singletonFace (Q : CausalCube α) (a : α) (ha : a ∈ Q.directions) : Q.Face :=
  ⟨{a}, by simpa using ha⟩

/-- A two-direction cube vertex. -/
def pairFace (Q : CausalCube α) (a b : α)
    (ha : a ∈ Q.directions) (hb : b ∈ Q.directions) : Q.Face :=
  ⟨{a, b}, by simp [Finset.insert_subset_iff, ha, hb]⟩

@[simp]
theorem vertex_emptyFace (Q : CausalCube α) :
    Q.vertex Q.emptyFace = Q.base := by
  apply LowerSet.ext
  ext a
  simp [vertex, emptyFace]

theorem base_adj_singletonVertex (Q : CausalCube α) (a : α)
    (ha : a ∈ Q.directions) :
    (lowerSetTransitionGraph (α := α)).Adj Q.base
      (Q.vertex (Q.singletonFace a ha)) := by
  rw [← vertex_emptyFace Q]
  apply (vertex_adj_iff_card_symmDiff_eq_one Q _ _).2
  have hsd : (∅ ∆ {a} : Finset α) = {a} := by
    ext x
    simp [Finset.mem_symmDiff]
  change (∅ ∆ {a} : Finset α).card = 1
  rw [hsd]
  simp

theorem singletonVertex_adj_pairVertex_left (Q : CausalCube α) {a b : α}
    (ha : a ∈ Q.directions) (hb : b ∈ Q.directions) (hne : a ≠ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (Q.vertex (Q.singletonFace a ha))
      (Q.vertex (Q.pairFace a b ha hb)) := by
  apply (vertex_adj_iff_card_symmDiff_eq_one Q _ _).2
  have hsd : ({a} ∆ {a, b} : Finset α) = {b} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    aesop
  change ({a} ∆ {a, b} : Finset α).card = 1
  rw [hsd]
  simp

theorem singletonVertex_adj_pairVertex_right (Q : CausalCube α) {a b : α}
    (ha : a ∈ Q.directions) (hb : b ∈ Q.directions) (hne : a ≠ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (Q.vertex (Q.singletonFace b hb))
      (Q.vertex (Q.pairFace a b ha hb)) := by
  apply (vertex_adj_iff_card_symmDiff_eq_one Q _ _).2
  have hsd : ({b} ∆ {a, b} : Finset α) = {a} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    aesop
  change ({b} ∆ {a, b} : Finset α).card = 1
  rw [hsd]
  simp

/-- Every pair of cube directions produces an actual graph square.  Thus the
higher cube definition is not merely set-theoretic: its two-faces are exactly
commuting causal transitions. -/
theorem two_directions_complete_square (Q : CausalCube α) {a b : α}
    (ha : a ∈ Q.directions) (hb : b ∈ Q.directions) (hne : a ≠ b) :
    ∃ va vb vab : LowerSet α,
      (lowerSetTransitionGraph (α := α)).Adj Q.base va ∧
      (lowerSetTransitionGraph (α := α)).Adj Q.base vb ∧
      va ≠ vb ∧
      (lowerSetTransitionGraph (α := α)).Adj va vab ∧
      (lowerSetTransitionGraph (α := α)).Adj vb vab ∧
      vab ≠ Q.base := by
  let Ta := Q.singletonFace a ha
  let Tb := Q.singletonFace b hb
  let Tab := Q.pairFace a b ha hb
  refine ⟨Q.vertex Ta, Q.vertex Tb, Q.vertex Tab,
    base_adj_singletonVertex Q a ha,
    base_adj_singletonVertex Q b hb, ?_, ?_, ?_, ?_⟩
  · intro hv
    have hface : Ta = Tb := Q.vertex_injective hv
    have hsets : ({a} : Finset α) = {b} := congrArg Subtype.val hface
    exact hne (Finset.singleton_injective hsets)
  · exact singletonVertex_adj_pairVertex_left Q ha hb hne
  · exact singletonVertex_adj_pairVertex_right Q ha hb hne
  · intro hv
    have hav : a ∈ Q.vertex Tab :=
      (mem_vertex_iff Q Tab a).2 (Or.inr (by simp [Tab, pairFace]))
    rw [hv] at hav
    exact (Q.addable a ha).1 hav

end CausalCube
end CausalCubes

/-! Cubes of a finite causal algebra are obtained by using its intrinsic
event order as directions. -/

abbrev CausalAlgebraCube {k : Type*} [Field k]
    (C : CausalAlgebra.CAlg k) :=
  CausalCube (CausalPoint C)

/-! ## Cubical links and the link Laplacian -/

section CubicalLinks

variable {V : Type*} [Fintype V]

/-- An incident direction at `v` is a neighboring graph state. -/
abbrev IncidentDirection (G : SimpleGraph V) (v : V) :=
  {a : V // G.Adj v a}

/-- The cubical link: two incident directions are joined precisely when their
moves commute by extending to a nondegenerate square. -/
def cubicalLink (G : SimpleGraph V) (v : V) :
    SimpleGraph (IncidentDirection G v) where
  Adj a b := a ≠ b ∧
    ∃ w : V, w ≠ v ∧ G.Adj a.1 w ∧ G.Adj b.1 w
  symm := by
    rintro a b ⟨hab, w, hwv, haw, hbw⟩
    exact ⟨Ne.symm hab, w, hwv, hbw, haw⟩
  loopless := by
    constructor
    intro a h
    exact h.1 rfl

/-- The local link is complete when every pair of distinct incident moves
commutes around a square. -/
def CubicalLinkComplete (G : SimpleGraph V) (v : V) : Prop :=
  ∀ a b : IncidentDirection G v, a ≠ b → (cubicalLink G v).Adj a b

/-- The previously defined square-completion defect vanishes exactly when the
cubical link is complete. -/
theorem squareCompletionDefect_eq_zero_iff_cubicalLinkComplete
    (G : SimpleGraph V) (v : V) :
    squareCompletionDefect G v = 0 ↔ CubicalLinkComplete G v := by
  rw [squareCompletionDefect_eq_zero_iff_every_pair]
  constructor
  · intro h a b hab
    have habv : a.1 ≠ b.1 := by
      intro heq
      exact hab (Subtype.ext heq)
    exact ⟨hab, h a.1 b.1 a.2 b.2 habv⟩
  · intro h a b hva hvb hab
    let a' : IncidentDirection G v := ⟨a, hva⟩
    let b' : IncidentDirection G v := ⟨b, hvb⟩
    have hab' : a' ≠ b' := by
      intro heq
      exact hab (congrArg Subtype.val heq)
    exact (h a' b' hab').2

/-- Graph Laplacian of the cubical link.  This operator probes variation
among the locally commuting causal directions at a state. -/
def cubicalLinkLaplacian (G : SimpleGraph V) (v : V)
    (φ : IncidentDirection G v → ℝ) (a : IncidentDirection G v) : ℝ :=
  graphLaplacian (cubicalLink G v) φ a

@[simp]
theorem cubicalLinkLaplacian_const (G : SimpleGraph V) (v : V)
    (c : ℝ) (a : IncidentDirection G v) :
    cubicalLinkLaplacian G v (fun _ => c) a = 0 := by
  exact graphLaplacian_const (cubicalLink G v) c a

end CubicalLinks

section CausalStateLinks

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Cubical link of a finite causal-poset state. -/
abbrev causalStateLink (s : LowerSet α) :=
  cubicalLink (lowerSetTransitionGraph (α := α)) s

/-- Link Laplacian specialized to a finite causal-poset state. -/
def causalStateLinkLaplacian (s : LowerSet α)
    (φ : IncidentDirection (lowerSetTransitionGraph (α := α)) s → ℝ)
    (a : IncidentDirection (lowerSetTransitionGraph (α := α)) s) : ℝ :=
  cubicalLinkLaplacian (lowerSetTransitionGraph (α := α)) s φ a

end CausalStateLinks

section CubeLinks

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

namespace CausalCube

/-- Each direction of a causal cube determines an incident vertex in the link
of the cube's base state. -/
def linkDirection (Q : CausalCube α)
    (a : {x : α // x ∈ Q.directions}) :
    IncidentDirection (lowerSetTransitionGraph (α := α)) Q.base :=
  ⟨Q.vertex (Q.singletonFace a.1 a.2),
    Q.base_adj_singletonVertex a.1 a.2⟩

theorem linkDirection_injective (Q : CausalCube α) :
    Function.Injective Q.linkDirection := by
  intro a b hab
  apply Subtype.ext
  have hv :
      Q.vertex (Q.singletonFace a.1 a.2) =
        Q.vertex (Q.singletonFace b.1 b.2) :=
    congrArg Subtype.val hab
  have hf := Q.vertex_injective hv
  have hs : ({a.1} : Finset α) = {b.1} := congrArg Subtype.val hf
  exact Finset.singleton_injective hs

/-- The directions of every causal cube form a clique in the cubical link of
its base.  Higher cells therefore agree with the link's square-commutation
relation. -/
theorem linkDirection_adj (Q : CausalCube α)
    (a b : {x : α // x ∈ Q.directions}) (hab : a ≠ b) :
    (cubicalLink (lowerSetTransitionGraph (α := α)) Q.base).Adj
      (Q.linkDirection a) (Q.linkDirection b) := by
  have habv : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  let Tab := Q.pairFace a.1 b.1 a.2 b.2
  refine ⟨?_, Q.vertex Tab, ?_, ?_, ?_⟩
  · exact fun h => hab (Q.linkDirection_injective h)
  · intro hv
    have hav : a.1 ∈ Q.vertex Tab :=
      (mem_vertex_iff Q Tab a.1).2 (Or.inr (by simp [Tab, pairFace]))
    rw [hv] at hav
    exact (Q.addable a.1 a.2).1 hav
  · exact Q.singletonVertex_adj_pairVertex_left a.2 b.2 habv
  · exact Q.singletonVertex_adj_pairVertex_right a.2 b.2 habv

end CausalCube
end CubeLinks

end
end CausalAlgebraicGeometry.CAGCubicalComplex
