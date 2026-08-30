/-
  CAGCausalRefinement.lean — Isometric growth along past-closed causal
  embeddings.

  An old finite causal poset may embed into a refined one with no new event
  below an old event.  Old lower-set states then extend by retaining exactly
  their old events.  Extension is an isometric induced embedding of transition
  graphs; old tangent directions inject, retain their event labels and metric,
  and intertwine the canonical connection.

  The refined local degree is proved to split exactly into the old degree plus
  `newDirectionCount`, giving the first quantitative control of directions
  entering a CAG frame under genuine causal growth.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGFunctorialGeometry

namespace CausalAlgebraicGeometry.CAGCausalRefinement

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGCubicalComplex
open CausalAlgebraicGeometry.CAGDirectionalGeometry
open CausalAlgebraicGeometry.CAGDiscreteConnection

noncomputable section
open scoped Classical

variable {α β : Type*}
  [PartialOrder α] [Fintype α]
  [PartialOrder β] [Fintype β]

/-- An embedding of an old causal event poset as a past-closed subposet of a
refined one.  No new event is allowed below an old event. -/
structure PastClosedEmbedding (α β : Type*) [PartialOrder α] [PartialOrder β]
    where
  toOrderEmbedding : α ↪o β
  past_closed : ∀ {b : β} {a : α}, b ≤ toOrderEmbedding a →
    ∃ x : α, toOrderEmbedding x = b

instance : CoeFun (PastClosedEmbedding α β) (fun _ => α → β) :=
  ⟨fun i => i.toOrderEmbedding⟩

omit [Fintype α] [Fintype β] in
theorem PastClosedEmbedding.injective (i : PastClosedEmbedding α β) :
    Function.Injective i :=
  i.toOrderEmbedding.injective

/-- Extend an old causal state into the refinement by keeping exactly its old
events. Past-closedness guarantees this image is still a lower set. -/
def extendState (i : PastClosedEmbedding α β) (s : LowerSet α) : LowerSet β where
  carrier := {b | ∃ a : α, a ∈ s ∧ i a = b}
  lower' := by
    intro b c hcb hb
    rcases hb with ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := i.past_closed hcb
    refine ⟨x, s.lower ?_ ha, hx⟩
    apply i.toOrderEmbedding.le_iff_le.mp
    simpa [hx] using hcb

omit [Fintype α] [Fintype β] in
@[simp]
theorem mem_extendState_iff (i : PastClosedEmbedding α β)
    (s : LowerSet α) (b : β) :
    b ∈ extendState i s ↔ ∃ a : α, a ∈ s ∧ i a = b :=
  Iff.rfl

/-- Restrict a refined state to its old event coordinates. -/
def restrictState (i : PastClosedEmbedding α β) (t : LowerSet β) : LowerSet α where
  carrier := {a | i a ∈ t}
  lower' := by
    intro a c hca ha
    exact t.lower (i.toOrderEmbedding.monotone hca) ha

omit [Fintype α] [Fintype β] in
@[simp]
theorem mem_restrictState_iff (i : PastClosedEmbedding α β)
    (t : LowerSet β) (a : α) :
    a ∈ restrictState i t ↔ i a ∈ t :=
  Iff.rfl

omit [Fintype α] [Fintype β] in
/-- Restriction is a left inverse to past-closed extension. -/
@[simp]
theorem restrictState_extendState (i : PastClosedEmbedding α β)
    (s : LowerSet α) : restrictState i (extendState i s) = s := by
  apply LowerSet.ext
  ext a
  constructor
  · rintro ⟨x, hx, hxa⟩
    exact (i.injective hxa).symm ▸ hx
  · intro ha
    exact ⟨a, ha, rfl⟩

omit [Fintype α] [Fintype β] in
theorem extendState_injective (i : PastClosedEmbedding α β) :
    Function.Injective (extendState i) := by
  intro s t h
  have := congrArg (restrictState i) h
  simpa using this

theorem separatingEvents_extendState (i : PastClosedEmbedding α β)
    (s t : LowerSet α) :
    separatingEvents (extendState i s) (extendState i t) =
      (separatingEvents s t).map i.toOrderEmbedding.toEmbedding := by
  ext b
  by_cases hb : ∃ a : α, i a = b
  · obtain ⟨a, rfl⟩ := hb
    simp [mem_separatingEvents_iff, extendState, i.injective.eq_iff]
  · simp only [mem_separatingEvents_iff, mem_extendState_iff, Finset.mem_map]
    have hnone : ∀ a : α, i a ≠ b := by
      intro a h
      exact hb ⟨a, h⟩
    simp [hnone]

/-- Past-closed refinement preserves all old state distances exactly. -/
theorem lowerSetDistance_extendState (i : PastClosedEmbedding α β)
    (s t : LowerSet α) :
    lowerSetDistance (extendState i s) (extendState i t) =
      lowerSetDistance s t := by
  rw [lowerSetDistance_eq_card_separatingEvents,
    separatingEvents_extendState, Finset.card_map,
    ← lowerSetDistance_eq_card_separatingEvents]

/-- The old transition graph embeds as an induced graph on extended states. -/
theorem adj_extendState_iff (i : PastClosedEmbedding α β)
    (s t : LowerSet α) :
    (lowerSetTransitionGraph (α := β)).Adj
        (extendState i s) (extendState i t) ↔
      (lowerSetTransitionGraph (α := α)).Adj s t := by
  change lowerSetDistance (extendState i s) (extendState i t) = 1 ↔
    lowerSetDistance s t = 1
  rw [lowerSetDistance_extendState]

/-- Every old tangent direction injects into the refined tangent frame. -/
def extendDirection (i : PastClosedEmbedding α β) (s : LowerSet α)
    (d : EventDirection s) : EventDirection (extendState i s) := by
  refine ⟨extendState i d.1, ?_⟩
  apply ((lowerSetTransitionGraph (α := β)).mem_neighborFinset
    (v := extendState i s) (extendState i d.1)).mpr
  rw [adj_extendState_iff]
  exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
    (v := s) d.1).mp d.2

@[simp]
theorem directionEvent_extendDirection (i : PastClosedEmbedding α β)
    (s : LowerSet α) (d : EventDirection s) :
    directionEvent (extendState i s) (extendDirection i s d) =
      i (directionEvent s d) := by
  have hmem : i (directionEvent s d) ∈
      separatingEvents (extendState i s) (extendState i d.1) := by
    rw [separatingEvents_extendState]
    exact Finset.mem_map.mpr
      ⟨directionEvent s d, directionEvent_mem_separatingEvents s d, rfl⟩
  change i (directionEvent s d) ∈
    separatingEvents (extendState i s) (extendDirection i s d).1 at hmem
  rw [separatingEvents_direction_eq_singleton] at hmem
  exact (Finset.mem_singleton.mp hmem).symm

theorem extendDirection_injective (i : PastClosedEmbedding α β)
    (s : LowerSet α) : Function.Injective (extendDirection i s) := by
  intro d f h
  apply Subtype.ext
  apply extendState_injective i
  exact congrArg Subtype.val h

/-- The old orthonormal event-wall metric is preserved inside the refined
tangent fiber. -/
theorem eventFrameMetric_extendDirection (i : PastClosedEmbedding α β)
    (s : LowerSet α) (d f : EventDirection s) :
    eventFrameMetric (extendDirection i s d) (extendDirection i s f) =
      eventFrameMetric d f := by
  unfold eventFrameMetric
  simp only [directionEvent_extendDirection]
  rw [i.injective.eq_iff]

/-- Persistence of an old direction remains valid after refinement. -/
def extendTransportable (i : PastClosedEmbedding α β)
    {s t : LowerSet α} (d : EventDirection s)
    (h : DirectionTransportable s t d) :
    DirectionTransportable (extendState i s) (extendState i t)
      (extendDirection i s d) :=
  ⟨extendDirection i t (transportDirection d h), by simp⟩

/-- Past-closed refinement commutes with the canonical event-wall
connection on every old persistent direction. -/
theorem transportDirection_extendDirection (i : PastClosedEmbedding α β)
    {s t : LowerSet α} (d : EventDirection s)
    (h : DirectionTransportable s t d) :
    transportDirection (extendDirection i s d) (extendTransportable i d h) =
      extendDirection i t (transportDirection d h) := by
  apply transportDirection_unique
  simp

theorem card_eventDirection_eq_degree
    {γ : Type*} [PartialOrder γ] [Fintype γ] (s : LowerSet γ) :
    Fintype.card (EventDirection s) =
      (lowerSetTransitionGraph (α := γ)).degree s := by
  rw [show Fintype.card (EventDirection s) =
      ((lowerSetTransitionGraph (α := γ)).neighborFinset s).card by
    exact Fintype.card_coe _]
  rfl

/-- The dimension of the old tangent fiber cannot decrease under a
past-closed causal refinement. -/
theorem degree_le_degree_extendState (i : PastClosedEmbedding α β)
    (s : LowerSet α) :
    (lowerSetTransitionGraph (α := α)).degree s ≤
      (lowerSetTransitionGraph (α := β)).degree (extendState i s) := by
  rw [← card_eventDirection_eq_degree, ← card_eventDirection_eq_degree]
  exact Fintype.card_le_of_injective (extendDirection i s)
    (extendDirection_injective i s)

/-- Number of genuinely new tangent directions created at an extended state. -/
def newDirectionCount (i : PastClosedEmbedding α β) (s : LowerSet α) : ℕ :=
  (lowerSetTransitionGraph (α := β)).degree (extendState i s) -
    (lowerSetTransitionGraph (α := α)).degree s

/-- Refined fiber dimension splits into old and newly created directions. -/
theorem degree_extendState_eq_degree_add_newDirectionCount
    (i : PastClosedEmbedding α β) (s : LowerSet α) :
    (lowerSetTransitionGraph (α := β)).degree (extendState i s) =
      (lowerSetTransitionGraph (α := α)).degree s +
        newDirectionCount i s := by
  unfold newDirectionCount
  have hle := degree_le_degree_extendState i s
  omega

end
end CausalAlgebraicGeometry.CAGCausalRefinement
