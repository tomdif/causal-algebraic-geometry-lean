/-
  CAGDiscreteConnection.lean — Canonical partial transport on intrinsic CAG
  event frames.

  A direction at a causal state is labeled by the unique global event wall
  it crosses.  When the same wall is incident at another state, this file
  defines its unique parallel transport by label preservation.  Transport
  has exact identity, inverse, composition, and path-independence laws; along
  a transition edge it sends the edge direction to the reverse edge.

  The directional fiber carries the positive-definite Euclidean metric in
  its orthonormal event-wall basis.  Parallel transport preserves this metric,
  and global event-labeled fields have zero covariant finite difference.
  Frame support is finite and its cardinality equals local graph degree.

  This is a flat partial discrete connection.  It is partial because causal
  dependencies can create or destroy incident directions.  It is not claimed
  to be a continuum Levi-Civita connection.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGDirectionalGeometry

namespace CausalAlgebraicGeometry.CAGDiscreteConnection

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGDirectionalGeometry
open CausalAlgebraicGeometry.CAGCubicalComplex

noncomputable section
open scoped Classical

variable {α : Type*} [PartialOrder α] [Fintype α]

/-! ## The partial event-wall connection -/

/-- A direction based at `s` is transportable to `t` when its global event
wall is also incident at `t`. -/
def DirectionTransportable (s t : LowerSet α) (d : EventDirection s) : Prop :=
  ∃ e : EventDirection t, directionEvent t e = directionEvent s d

/-- Parallel transport is the unique target direction carrying the same
event-wall label.  It is partial because that label need not be incident at
the target state. -/
noncomputable def transportDirection {s t : LowerSet α}
    (d : EventDirection s) (h : DirectionTransportable s t d) :
    EventDirection t :=
  Classical.choose h

@[simp]
theorem directionEvent_transportDirection {s t : LowerSet α}
    (d : EventDirection s) (h : DirectionTransportable s t d) :
    directionEvent t (transportDirection d h) = directionEvent s d :=
  Classical.choose_spec h

/-- Label injectivity makes parallel transport unique. -/
theorem transportDirection_unique {s t : LowerSet α}
    (d : EventDirection s) (h : DirectionTransportable s t d)
    (e : EventDirection t)
    (he : directionEvent t e = directionEvent s d) :
    transportDirection d h = e := by
  apply directionEvent_injective t
  rw [directionEvent_transportDirection, he]

/-- Every direction transports to itself. -/
def selfTransportable (s : LowerSet α) (d : EventDirection s) :
    DirectionTransportable s s d :=
  ⟨d, rfl⟩

@[simp]
theorem transportDirection_self (s : LowerSet α) (d : EventDirection s) :
    transportDirection d (selfTransportable s d) = d := by
  exact transportDirection_unique d (selfTransportable s d) d rfl

/-- A transported direction can be transported back along the same common
event wall. -/
def reverseTransportable {s t : LowerSet α} (d : EventDirection s)
    (h : DirectionTransportable s t d) :
    DirectionTransportable t s (transportDirection d h) :=
  ⟨d, (directionEvent_transportDirection d h).symm⟩

@[simp]
theorem transportDirection_inverse {s t : LowerSet α}
    (d : EventDirection s) (h : DirectionTransportable s t d) :
    transportDirection (transportDirection d h) (reverseTransportable d h) = d := by
  exact transportDirection_unique _ (reverseTransportable d h) d
    (directionEvent_transportDirection d h).symm

/-! ### Transport along an actual transition edge -/

/-- The reverse of an incident graph direction is the same edge based at its
other endpoint. -/
def reverseEdgeDirection (s : LowerSet α) (d : EventDirection s) :
    EventDirection d.1 := by
  have hadj : (lowerSetTransitionGraph (α := α)).Adj s d.1 :=
    ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
      (v := s) d.1).mp d.2
  refine ⟨s, ?_⟩
  exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
    (v := d.1) s).mpr hadj.symm

/-- Reversing an edge preserves its event-wall label. -/
@[simp]
theorem directionEvent_reverseEdgeDirection
    (s : LowerSet α) (d : EventDirection s) :
    directionEvent d.1 (reverseEdgeDirection s d) = directionEvent s d := by
  have hrev := directionEvent_mem_separatingEvents d.1
    (reverseEdgeDirection s d)
  change directionEvent d.1 (reverseEdgeDirection s d) ∈
    separatingEvents d.1 s at hrev
  have hsymm : separatingEvents d.1 s = separatingEvents s d.1 := by
    ext a
    rw [mem_separatingEvents_iff, mem_separatingEvents_iff]
    exact ne_comm
  rw [hsymm, separatingEvents_direction_eq_singleton] at hrev
  exact Finset.mem_singleton.mp hrev

/-- Every transition edge transports its own direction to the reverse edge. -/
def edgeDirectionTransportable (s : LowerSet α) (d : EventDirection s) :
    DirectionTransportable s d.1 d :=
  ⟨reverseEdgeDirection s d, directionEvent_reverseEdgeDirection s d⟩

@[simp]
theorem transportDirection_along_edge
    (s : LowerSet α) (d : EventDirection s) :
    transportDirection d (edgeDirectionTransportable s d) =
      reverseEdgeDirection s d := by
  exact transportDirection_unique d (edgeDirectionTransportable s d)
    (reverseEdgeDirection s d) (directionEvent_reverseEdgeDirection s d)

@[simp]
theorem reverseEdgeDirection_involutive
    (s : LowerSet α) (d : EventDirection s) :
    reverseEdgeDirection d.1 (reverseEdgeDirection s d) = d := by
  apply Subtype.ext
  rfl

/-- Composable persistence certificates give a direct persistence
certificate. -/
def composeTransportable {s t u : LowerSet α} (d : EventDirection s)
    (hst : DirectionTransportable s t d)
    (htu : DirectionTransportable t u (transportDirection d hst)) :
    DirectionTransportable s u d :=
  ⟨transportDirection (transportDirection d hst) htu,
    (directionEvent_transportDirection _ htu).trans
      (directionEvent_transportDirection d hst)⟩

/-- Parallel transport obeys the connection composition law wherever all
three transports are defined. -/
theorem transportDirection_comp {s t u : LowerSet α}
    (d : EventDirection s)
    (hst : DirectionTransportable s t d)
    (htu : DirectionTransportable t u (transportDirection d hst)) :
    transportDirection d (composeTransportable d hst htu) =
      transportDirection (transportDirection d hst) htu := by
  apply directionEvent_injective u
  simp

/-- The connection has zero holonomy on its domain: two transport paths with
the same endpoints and initial event direction have the same endpoint. -/
theorem transportDirection_path_independent
    {s x y t : LowerSet α} (d : EventDirection s)
    (hsx : DirectionTransportable s x d)
    (hxt : DirectionTransportable x t (transportDirection d hsx))
    (hsy : DirectionTransportable s y d)
    (hyt : DirectionTransportable y t (transportDirection d hsy)) :
    transportDirection (transportDirection d hsx) hxt =
      transportDirection (transportDirection d hsy) hyt := by
  apply directionEvent_injective t
  simp

/-! ## Local metric compatibility -/

/-- Orthonormal event-wall metric on the intrinsic directional frame. -/
def eventFrameMetric {s : LowerSet α} (d e : EventDirection s) : ℝ :=
  if directionEvent s d = directionEvent s e then 1 else 0

@[simp]
theorem eventFrameMetric_self {s : LowerSet α} (d : EventDirection s) :
    eventFrameMetric d d = 1 := by
  simp [eventFrameMetric]

theorem eventFrameMetric_eq_zero_of_ne {s : LowerSet α}
    {d e : EventDirection s} (hne : d ≠ e) :
    eventFrameMetric d e = 0 := by
  have hlabel : directionEvent s d ≠ directionEvent s e := by
    intro h
    exact hne (directionEvent_injective s h)
  simp [eventFrameMetric, hlabel]

/-- Simultaneous transport preserves the event-frame metric. -/
theorem eventFrameMetric_transport {s t : LowerSet α}
    (d e : EventDirection s)
    (hd : DirectionTransportable s t d)
    (he : DirectionTransportable s t e) :
    eventFrameMetric (transportDirection d hd) (transportDirection e he) =
      eventFrameMetric d e := by
  simp [eventFrameMetric]

/-- A tangent vector is a real coefficient on each incident event wall. -/
abbrev DirectionalVector (s : LowerSet α) := EventDirection s → ℝ

/-- Euclidean inner product in the orthonormal event-wall frame. -/
def eventFrameInnerProduct {s : LowerSet α}
    (X Y : DirectionalVector s) : ℝ :=
  ∑ d : EventDirection s, X d * Y d

/-- Squared norm induced by the event-frame inner product. -/
def eventFrameNormSq {s : LowerSet α} (X : DirectionalVector s) : ℝ :=
  eventFrameInnerProduct X X

theorem eventFrameNormSq_nonneg {s : LowerSet α}
    (X : DirectionalVector s) : 0 ≤ eventFrameNormSq X := by
  unfold eventFrameNormSq eventFrameInnerProduct
  apply Finset.sum_nonneg
  intro d _hd
  exact mul_self_nonneg (X d)

/-- The event-frame metric is positive definite. -/
@[simp]
theorem eventFrameNormSq_eq_zero_iff {s : LowerSet α}
    (X : DirectionalVector s) :
    eventFrameNormSq X = 0 ↔ X = 0 := by
  unfold eventFrameNormSq eventFrameInnerProduct
  constructor
  · intro h
    funext d
    have hd := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e _he => mul_self_nonneg (X e))).mp h d (Finset.mem_univ d)
    simpa using (mul_self_eq_zero.mp hd)
  · intro h
    subst X
    simp

/-! ## Covariant finite differences -/

/-- Covariant finite difference of a directional field along the partial
event-wall connection. -/
def covariantDifference
    (X : ∀ s : LowerSet α, EventDirection s → ℝ)
    {s t : LowerSet α} (d : EventDirection s)
    (h : DirectionTransportable s t d) : ℝ :=
  X t (transportDirection d h) - X s d

/-- A field determined only by the global event-wall label. -/
def eventLabeledDirectionField (F : α → ℝ) :
    ∀ s : LowerSet α, EventDirection s → ℝ :=
  fun s d => F (directionEvent s d)

/-- Global event-labeled fields are parallel for the canonical connection. -/
@[simp]
theorem covariantDifference_eventLabeledDirectionField
    (F : α → ℝ) {s t : LowerSet α} (d : EventDirection s)
    (h : DirectionTransportable s t d) :
    covariantDifference (eventLabeledDirectionField F) d h = 0 := by
  simp [covariantDifference, eventLabeledDirectionField]

/-- Covariant differences telescope under composable transport. -/
theorem covariantDifference_comp
    (X : ∀ s : LowerSet α, EventDirection s → ℝ)
    {s t u : LowerSet α} (d : EventDirection s)
    (hst : DirectionTransportable s t d)
    (htu : DirectionTransportable t u (transportDirection d hst)) :
    covariantDifference X d (composeTransportable d hst htu) =
      covariantDifference X d hst +
        covariantDifference X (transportDirection d hst) htu := by
  unfold covariantDifference
  rw [transportDirection_comp d hst htu]
  ring

/-! ## Finite frame support -/

/-- Finite set of global event walls incident at a state. -/
noncomputable def directionLabelFinset (s : LowerSet α) : Finset α :=
  ((lowerSetTransitionGraph (α := α)).neighborFinset s).attach.image
    (directionEvent s)

theorem mem_directionLabelFinset_iff (s : LowerSet α) (a : α) :
    a ∈ directionLabelFinset s ↔
      ∃ d : EventDirection s, directionEvent s d = a := by
  simp [directionLabelFinset]

/-- Transportability is exactly membership of the source label in the target
frame support. -/
theorem directionTransportable_iff_mem_labelFinset
    (s t : LowerSet α) (d : EventDirection s) :
    DirectionTransportable s t d ↔
      directionEvent s d ∈ directionLabelFinset t := by
  rw [mem_directionLabelFinset_iff]
  rfl

/-- The number of frame labels equals the local graph degree. -/
theorem card_directionLabelFinset_eq_degree (s : LowerSet α) :
    (directionLabelFinset s).card =
      (lowerSetTransitionGraph (α := α)).degree s := by
  rw [directionLabelFinset,
    Finset.card_image_of_injective _ (directionEvent_injective s),
    Finset.card_attach]
  rfl

end
end CausalAlgebraicGeometry.CAGDiscreteConnection
