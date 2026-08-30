/-
  CAGFunctorialGeometry.lean — Coordinate invariance of finite CAG geometry.

  Every order isomorphism of finite causal event posets induces an isometry
  of their lower-set state spaces and an isomorphism of transition graphs.
  It also induces an equivalence of intrinsic event directions which
  intertwines the event-wall connection and preserves the positive-definite
  tangent norm, cubical sectional kernel, and total directional curvature.

  These results prove that the metric, connection, and curvature constructions
  depend only on causal order, not on event names or a chosen presentation.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGDiscreteConnection

namespace CausalAlgebraicGeometry.CAGFunctorialGeometry

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGCubicalComplex
open CausalAlgebraicGeometry.CAGDirectionalGeometry
open CausalAlgebraicGeometry.CAGDiscreteConnection

noncomputable section
open scoped Classical

variable {α β : Type*}
  [PartialOrder α] [Fintype α]
  [PartialOrder β] [Fintype β]

/-! ## Relabeling finite causal states -/

/-- Push a lower-set state through an order isomorphism of causal events. -/
def relabelState (e : α ≃o β) (s : LowerSet α) : LowerSet β where
  carrier := {b | e.symm b ∈ s}
  lower' := by
    intro b c hcb hb
    exact s.lower (e.symm.monotone hcb) hb

omit [Fintype α] [Fintype β] in
@[simp]
theorem mem_relabelState_iff (e : α ≃o β) (s : LowerSet α) (b : β) :
    b ∈ relabelState e s ↔ e.symm b ∈ s :=
  Iff.rfl

omit [Fintype α] [Fintype β] in
@[simp]
theorem relabelState_symm_relabelState (e : α ≃o β) (s : LowerSet α) :
    relabelState e.symm (relabelState e s) = s := by
  apply LowerSet.ext
  ext a
  simp [relabelState]

omit [Fintype α] [Fintype β] in
@[simp]
theorem relabelState_relabelState_symm (e : α ≃o β) (t : LowerSet β) :
    relabelState e (relabelState e.symm t) = t := by
  apply LowerSet.ext
  ext b
  simp [relabelState]

/-- Order relabeling gives an equivalence of causal-state spaces. -/
def relabelStateEquiv (e : α ≃o β) : LowerSet α ≃ LowerSet β where
  toFun := relabelState e
  invFun := relabelState e.symm
  left_inv := relabelState_symm_relabelState e
  right_inv := relabelState_relabelState_symm e

omit [Fintype α] [Fintype β] in
@[simp]
theorem relabelStateEquiv_apply (e : α ≃o β) (s : LowerSet α) :
    relabelStateEquiv e s = relabelState e s :=
  rfl

theorem separatingEvents_relabelState (e : α ≃o β)
    (s t : LowerSet α) :
    separatingEvents (relabelState e s) (relabelState e t) =
      (separatingEvents s t).map e.toEmbedding := by
  ext b
  simp only [mem_separatingEvents_iff, mem_relabelState_iff,
    Finset.mem_map]
  constructor
  · intro h
    refine ⟨e.symm b, ?_, ?_⟩
    · simpa [mem_separatingEvents_iff] using h
    · simp
  · rintro ⟨a, ha, hab⟩
    subst b
    simpa using ha

/-- Event-Hamming distance is invariant under causal-order relabeling. -/
theorem lowerSetDistance_relabelState (e : α ≃o β)
    (s t : LowerSet α) :
    lowerSetDistance (relabelState e s) (relabelState e t) =
      lowerSetDistance s t := by
  rw [lowerSetDistance_eq_card_separatingEvents,
    separatingEvents_relabelState, Finset.card_map,
    ← lowerSetDistance_eq_card_separatingEvents]

/-- Relabeling is an isomorphism of causal-state transition graphs. -/
theorem adj_relabelState_iff (e : α ≃o β) (s t : LowerSet α) :
    (lowerSetTransitionGraph (α := β)).Adj
        (relabelState e s) (relabelState e t) ↔
      (lowerSetTransitionGraph (α := α)).Adj s t := by
  change lowerSetDistance (relabelState e s) (relabelState e t) = 1 ↔
    lowerSetDistance s t = 1
  rw [lowerSetDistance_relabelState]

/-! ## Natural transport of tangent directions -/

/-- Relabel an incident direction together with its adjacency certificate. -/
def relabelDirection (e : α ≃o β) (s : LowerSet α)
    (d : EventDirection s) : EventDirection (relabelState e s) := by
  refine ⟨relabelState e d.1, ?_⟩
  apply ((lowerSetTransitionGraph (α := β)).mem_neighborFinset
    (v := relabelState e s) (relabelState e d.1)).mpr
  rw [adj_relabelState_iff]
  exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
    (v := s) d.1).mp d.2

@[simp]
theorem directionEvent_relabelDirection (e : α ≃o β)
    (s : LowerSet α) (d : EventDirection s) :
    directionEvent (relabelState e s) (relabelDirection e s d) =
      e (directionEvent s d) := by
  have hmem : e (directionEvent s d) ∈
      separatingEvents (relabelState e s) (relabelState e d.1) := by
    rw [separatingEvents_relabelState]
    exact Finset.mem_map.mpr
      ⟨directionEvent s d, directionEvent_mem_separatingEvents s d, rfl⟩
  change e (directionEvent s d) ∈
    separatingEvents (relabelState e s) (relabelDirection e s d).1 at hmem
  rw [separatingEvents_direction_eq_singleton] at hmem
  exact (Finset.mem_singleton.mp hmem).symm

theorem relabelDirection_injective (e : α ≃o β) (s : LowerSet α) :
    Function.Injective (relabelDirection e s) := by
  intro d f hdf
  apply directionEvent_injective s
  apply e.injective
  simpa using congrArg (directionEvent (relabelState e s)) hdf

theorem relabelDirection_surjective (e : α ≃o β) (s : LowerSet α) :
    Function.Surjective (relabelDirection e s) := by
  intro q
  let t := relabelState e.symm q.1
  have ht : relabelState e t = q.1 := by
    simp [t]
  have hqadj : (lowerSetTransitionGraph (α := β)).Adj
      (relabelState e s) q.1 :=
    ((lowerSetTransitionGraph (α := β)).mem_neighborFinset
      (v := relabelState e s) q.1).mp q.2
  have hadj : (lowerSetTransitionGraph (α := α)).Adj s t := by
    rw [← adj_relabelState_iff e]
    simpa [ht] using hqadj
  let d : EventDirection s :=
    ⟨t, ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
      (v := s) t).mpr hadj⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  exact ht

/-- Every causal-order isomorphism induces an equivalence of intrinsic
tangent frames. -/
noncomputable def relabelDirectionEquiv (e : α ≃o β) (s : LowerSet α) :
    EventDirection s ≃ EventDirection (relabelState e s) :=
  Equiv.ofBijective (relabelDirection e s)
    ⟨relabelDirection_injective e s, relabelDirection_surjective e s⟩

/-- The event-frame metric is natural under causal-order relabeling. -/
theorem eventFrameMetric_relabelDirection (e : α ≃o β)
    (s : LowerSet α) (d f : EventDirection s) :
    eventFrameMetric (relabelDirection e s d) (relabelDirection e s f) =
      eventFrameMetric d f := by
  unfold eventFrameMetric
  simp only [directionEvent_relabelDirection]
  rw [e.injective.eq_iff]

/-- Persistence of a direction is preserved under relabeling. -/
def relabelTransportable (e : α ≃o β) {s t : LowerSet α}
    (d : EventDirection s) (h : DirectionTransportable s t d) :
    DirectionTransportable (relabelState e s) (relabelState e t)
      (relabelDirection e s d) :=
  ⟨relabelDirection e t (transportDirection d h), by simp⟩

/-- Relabeling commutes exactly with the canonical discrete connection. -/
theorem transportDirection_relabelDirection (e : α ≃o β)
    {s t : LowerSet α} (d : EventDirection s)
    (h : DirectionTransportable s t d) :
    transportDirection (relabelDirection e s d) (relabelTransportable e d h) =
      relabelDirection e t (transportDirection d h) := by
  apply transportDirection_unique
  simp

/-! ## Naturality of the fiber norm and cubical curvature -/

/-- Push a tangent vector through the relabeled directional frame. -/
def relabelDirectionalVector (e : α ≃o β) (s : LowerSet α)
    (X : DirectionalVector s) : DirectionalVector (relabelState e s) :=
  fun q => X ((relabelDirectionEquiv e s).symm q)

/-- Relabeling is an isometry of the positive-definite tangent fibers. -/
theorem eventFrameNormSq_relabelDirectionalVector (e : α ≃o β)
    (s : LowerSet α) (X : DirectionalVector s) :
    eventFrameNormSq (relabelDirectionalVector e s X) =
      eventFrameNormSq X := by
  unfold eventFrameNormSq eventFrameInnerProduct relabelDirectionalVector
  let E := relabelDirectionEquiv e s
  exact E.symm.sum_comp (fun d => X d * X d)

omit [Fintype α] [Fintype β] in
theorem relabelState_ne_iff (e : α ≃o β) (s t : LowerSet α) :
    relabelState e s ≠ relabelState e t ↔ s ≠ t := by
  constructor
  · intro hst h
    exact hst (congrArg (relabelState e) h)
  · intro hst h
    exact hst ((relabelStateEquiv e).injective h)

/-- Square completion is invariant under causal-order relabeling. -/
theorem squareCompletion_relabelState_iff (e : α ≃o β)
    (s a b : LowerSet α) :
    (∃ w : LowerSet β, w ≠ relabelState e s ∧
      (lowerSetTransitionGraph (α := β)).Adj (relabelState e a) w ∧
      (lowerSetTransitionGraph (α := β)).Adj (relabelState e b) w) ↔
    (∃ w : LowerSet α, w ≠ s ∧
      (lowerSetTransitionGraph (α := α)).Adj a w ∧
      (lowerSetTransitionGraph (α := α)).Adj b w) := by
  constructor
  · rintro ⟨w, hws, haw, hbw⟩
    let v := relabelState e.symm w
    have hev : relabelState e v = w := by simp [v]
    refine ⟨v, ?_, ?_, ?_⟩
    · intro hvs
      apply hws
      rw [← hev, hvs]
    · rw [← adj_relabelState_iff e]
      simpa [hev] using haw
    · rw [← adj_relabelState_iff e]
      simpa [hev] using hbw
  · rintro ⟨w, hws, haw, hbw⟩
    refine ⟨relabelState e w, ?_, ?_, ?_⟩
    · exact (relabelState_ne_iff e w s).mpr hws
    · exact (adj_relabelState_iff e a w).mpr haw
    · exact (adj_relabelState_iff e b w).mpr hbw

/-- The graph-intrinsic sectional kernel is invariant under order
isomorphism. -/
theorem cubicalSectionalDefect_relabelState (e : α ≃o β)
    (s a b : LowerSet α) :
    lowerSetCubicalSectionalDefect (relabelState e s)
        (relabelState e a) (relabelState e b) =
      lowerSetCubicalSectionalDefect s a b := by
  unfold lowerSetCubicalSectionalDefect cubicalSectionalDefect
  by_cases hinc :
      (lowerSetTransitionGraph (α := α)).Adj s a ∧
      (lowerSetTransitionGraph (α := α)).Adj s b ∧ a ≠ b
  · have hinc' :
        (lowerSetTransitionGraph (α := β)).Adj
            (relabelState e s) (relabelState e a) ∧
        (lowerSetTransitionGraph (α := β)).Adj
            (relabelState e s) (relabelState e b) ∧
        relabelState e a ≠ relabelState e b :=
      ⟨(adj_relabelState_iff e s a).mpr hinc.1,
        (adj_relabelState_iff e s b).mpr hinc.2.1,
        (relabelState_ne_iff e a b).mpr hinc.2.2⟩
    rw [if_pos hinc, if_pos hinc']
    by_cases hsquare : ∃ w : LowerSet α, w ≠ s ∧
        (lowerSetTransitionGraph (α := α)).Adj a w ∧
        (lowerSetTransitionGraph (α := α)).Adj b w
    · have hsquare' := (squareCompletion_relabelState_iff e s a b).mpr hsquare
      rw [if_pos hsquare, if_pos hsquare']
    · have hsquare' := not_congr
        (squareCompletion_relabelState_iff e s a b) |>.mpr hsquare
      rw [if_neg hsquare, if_neg hsquare']
  · have hinc' : ¬
        ((lowerSetTransitionGraph (α := β)).Adj
            (relabelState e s) (relabelState e a) ∧
        (lowerSetTransitionGraph (α := β)).Adj
            (relabelState e s) (relabelState e b) ∧
        relabelState e a ≠ relabelState e b) := by
      rintro ⟨hsa, hsb, hab⟩
      exact hinc ⟨(adj_relabelState_iff e s a).mp hsa,
        (adj_relabelState_iff e s b).mp hsb,
        (relabelState_ne_iff e a b).mp hab⟩
    rw [if_neg hinc, if_neg hinc']

/-- Consequently every sectional component in the event frame is natural. -/
theorem cubicalSectionalDefect_relabelDirection (e : α ≃o β)
    (s : LowerSet α) (d f : EventDirection s) :
    lowerSetCubicalSectionalDefect (relabelState e s)
        (relabelDirection e s d).1 (relabelDirection e s f).1 =
      lowerSetCubicalSectionalDefect s d.1 f.1 := by
  change lowerSetCubicalSectionalDefect (relabelState e s)
      (relabelState e d.1) (relabelState e f.1) = _
  exact cubicalSectionalDefect_relabelState e s d.1 f.1

/-- The full directional curvature trace is a causal-order isomorphism
invariant. -/
theorem totalDirectionalSectionalCurvature_relabelState
    (e : α ≃o β) (s : LowerSet α) :
    totalDirectionalSectionalCurvature (relabelState e s) =
      totalDirectionalSectionalCurvature s := by
  unfold totalDirectionalSectionalCurvature
  let E := relabelDirectionEquiv e s
  calc
    (∑ q : EventDirection (relabelState e s),
        ∑ r : EventDirection (relabelState e s),
          lowerSetCubicalSectionalDefect (relabelState e s) q.1 r.1) =
      ∑ d : EventDirection s,
        ∑ r : EventDirection (relabelState e s),
          lowerSetCubicalSectionalDefect (relabelState e s) (E d).1 r.1 := by
      exact (E.sum_comp (fun q =>
        ∑ r : EventDirection (relabelState e s),
          lowerSetCubicalSectionalDefect (relabelState e s) q.1 r.1)).symm
    _ = ∑ d : EventDirection s, ∑ f : EventDirection s,
          lowerSetCubicalSectionalDefect (relabelState e s)
            (E d).1 (E f).1 := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact (E.sum_comp (fun r =>
        lowerSetCubicalSectionalDefect (relabelState e s) (E d).1 r.1)).symm
    _ = ∑ d : EventDirection s, ∑ f : EventDirection s,
          lowerSetCubicalSectionalDefect s d.1 f.1 := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro f _hf
      exact cubicalSectionalDefect_relabelDirection e s d f

end
end CausalAlgebraicGeometry.CAGFunctorialGeometry
