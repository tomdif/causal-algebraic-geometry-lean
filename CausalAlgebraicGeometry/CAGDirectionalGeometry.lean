/-
  CAGDirectionalGeometry.lean — Intrinsic event frames and exact frontier
  order-curvature for finite causal states.

  Every edge incident to a downset state has a unique causal-event label,
  distinct edges have distinct labels, and every edge is exactly either a
  legal maximal-event removal or a legal minimal-event addition.  The
  causal-state graph Laplacian is therefore the trace of an intrinsic
  event-labeled finite-difference frame without product coordinates.

  For one removal label `a` and one addition label `b`, the two moves fail to
  complete to a graph square exactly when `a ≤ b`.  Consequently their
  cubical sectional defect is the order-indicator kernel, and total mixed
  frontier curvature is exactly the number of causal incidences crossing
  the active frontier.  Same-sign pairs always complete squares, so the full
  ordered directional curvature trace is twice that incidence count.

  This is a graph-intrinsic discrete sectional curvature formula.  It does
  not assert that the kernel is a multilinear continuum Riemann tensor.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGNonproductScalingLimit
import CausalAlgebraicGeometry.CAGCubicalComplex

namespace CausalAlgebraicGeometry.CAGDirectionalGeometry

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGFiniteCausalDynamics
open CausalAlgebraicGeometry.CAGCubicalComplex

noncomputable section
open scoped Classical

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Outside the separating-event set, two states have identical occupancy. -/
theorem mem_iff_of_not_mem_separatingEvents
    (s t : LowerSet α) (x : α) (hx : x ∉ separatingEvents s t) :
    x ∈ s ↔ x ∈ t := by
  rw [mem_separatingEvents_iff] at hx
  have h := not_ne_iff.mp hx
  constructor
  · intro hs
    exact h ▸ hs
  · intro ht
    exact h.symm ▸ ht

/-! ## Intrinsic event-labeled tangent frame -/

/-- Incident graph directions based at `s`, represented by the neighboring
state together with its adjacency certificate. -/
abbrev EventDirection (s : LowerSet α) :=
  {t : LowerSet α //
    t ∈ (lowerSetTransitionGraph (α := α)).neighborFinset s}

/-- The unique causal event whose occupancy is toggled by an incident
direction. -/
def directionEvent (s : LowerSet α) (d : EventDirection s) : α := by
  have hadj : (lowerSetTransitionGraph (α := α)).Adj s d.1 := by
    exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
      (v := s) d.1).mp d.2
  exact Classical.choose (existsUnique_separatingEvent_of_adj hadj)

theorem directionEvent_mem_separatingEvents
    (s : LowerSet α) (d : EventDirection s) :
    directionEvent s d ∈ separatingEvents s d.1 := by
  have hadj : (lowerSetTransitionGraph (α := α)).Adj s d.1 := by
    exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
      (v := s) d.1).mp d.2
  simpa [directionEvent] using
    (Classical.choose_spec (existsUnique_separatingEvent_of_adj hadj)).1

theorem separatingEvents_direction_eq_singleton
    (s : LowerSet α) (d : EventDirection s) :
    separatingEvents s d.1 = {directionEvent s d} := by
  have hadj : (lowerSetTransitionGraph (α := α)).Adj s d.1 := by
    exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
      (v := s) d.1).mp d.2
  have hu := Classical.choose_spec (existsUnique_separatingEvent_of_adj hadj)
  apply Finset.Subset.antisymm
  · intro x hx
    simpa [directionEvent] using hu.2 x hx
  · intro x hx
    have hxe : x = directionEvent s d := by simpa using hx
    subst x
    exact directionEvent_mem_separatingEvents s d

/-- Distinct incident directions have distinct event-wall labels. -/
theorem directionEvent_injective (s : LowerSet α) :
    Function.Injective (directionEvent s) := by
  intro d e hde
  apply Subtype.ext
  apply LowerSet.ext
  ext x
  by_cases hx : x = directionEvent s d
  · subst x
    have hd := mem_separatingEvents_iff.mp
      (directionEvent_mem_separatingEvents s d)
    have he := mem_separatingEvents_iff.mp
      (directionEvent_mem_separatingEvents s e)
    rw [← hde] at he
    by_cases hs : directionEvent s d ∈ s <;>
      by_cases hdmem : directionEvent s d ∈ d.1 <;>
      by_cases hemel : directionEvent s d ∈ e.1 <;>
      simp_all
  · have hxd : x ∉ separatingEvents s d.1 := by
      rw [separatingEvents_direction_eq_singleton]
      simpa
    have hxe : x ∉ separatingEvents s e.1 := by
      rw [separatingEvents_direction_eq_singleton, ← hde]
      simpa
    have hd := mem_iff_of_not_mem_separatingEvents s d.1 x hxd
    have he := mem_iff_of_not_mem_separatingEvents s e.1 x hxe
    exact hd.symm.trans he

/-- One directional finite difference in the intrinsic event frame. -/
def directionalDifference (φ : LowerSet α → ℝ) (s : LowerSet α)
    (d : EventDirection s) : ℝ :=
  φ s - φ d.1

/-- The causal-state Laplacian is the trace of its event-labeled directional
differences.  No product coordinates are required. -/
theorem causalStateLaplacian_directional_decomposition
    (φ : LowerSet α → ℝ) (s : LowerSet α) :
    causalStateLaplacian φ s =
      Finset.sum
        ((lowerSetTransitionGraph (α := α)).neighborFinset s).attach
        (fun d => directionalDifference φ s d) := by
  unfold causalStateLaplacian graphLaplacian
  simpa only [directionalDifference] using
    (Finset.sum_attach
      ((lowerSetTransitionGraph (α := α)).neighborFinset s)
      (fun t => φ s - φ t)).symm

variable [DecidableEq α]

/-- An occupied event is removable when it is maximal in the current
downset. -/
def RemovableEvent (s : LowerSet α) (a : α) : Prop :=
  a ∈ s ∧ ∀ b : α, b ∈ s → a ≤ b → b = a

/-- State obtained by performing one addable event. -/
def addEventState (s : LowerSet α) (a : α) (ha : AddableEvent s a) :
    LowerSet α where
  carrier := Set.insert a (s : Set α)
  lower' := by
    intro b c hcb hb
    rcases hb with hba | hbs
    · subst b
      by_cases hca : c = a
      · exact Set.mem_insert_iff.mpr (Or.inl hca)
      · exact Set.mem_insert_iff.mpr (Or.inr (ha.2 c hcb hca))
    · exact Set.mem_insert_iff.mpr (Or.inr (s.lower hcb hbs))

omit [Fintype α] in
@[simp]
theorem mem_addEventState_iff (s : LowerSet α) (a : α)
    (ha : AddableEvent s a) (x : α) :
    x ∈ addEventState s a ha ↔ x = a ∨ x ∈ s :=
  Set.mem_insert_iff

/-- State obtained by deleting one removable event. -/
def removeEventState (s : LowerSet α) (a : α) (ha : RemovableEvent s a) :
    LowerSet α where
  carrier := {x | x ∈ s ∧ x ≠ a}
  lower' := by
    intro b c hcb hb
    refine ⟨s.lower hcb hb.1, ?_⟩
    intro hca
    subst c
    exact hb.2 (ha.2 b hb.1 hcb)

omit [Fintype α] [DecidableEq α] in
@[simp]
theorem mem_removeEventState_iff (s : LowerSet α) (a : α)
    (ha : RemovableEvent s a) (x : α) :
    x ∈ removeEventState s a ha ↔ x ∈ s ∧ x ≠ a :=
  Iff.rfl

theorem lowerSetDistance_addEventState (s : LowerSet α) (a : α)
    (ha : AddableEvent s a) :
    lowerSetDistance s (addEventState s a ha) = 1 := by
  rw [lowerSetDistance_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ s) ≠ (x ∈ addEventState s a ha)) = {a} := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha.1]
    · simp [hxa]
  rw [hfilter]
  simp

theorem lowerSetDistance_removeEventState (s : LowerSet α) (a : α)
    (ha : RemovableEvent s a) :
    lowerSetDistance s (removeEventState s a ha) = 1 := by
  rw [lowerSetDistance_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ s) ≠ (x ∈ removeEventState s a ha)) = {a} := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha.1]
    · simp [hxa]
  rw [hfilter]
  simp

theorem adj_addEventState (s : LowerSet α) (a : α)
    (ha : AddableEvent s a) :
    (lowerSetTransitionGraph (α := α)).Adj s (addEventState s a ha) :=
  lowerSetDistance_addEventState s a ha

theorem adj_removeEventState (s : LowerSet α) (a : α)
    (ha : RemovableEvent s a) :
    (lowerSetTransitionGraph (α := α)).Adj s (removeEventState s a ha) :=
  lowerSetDistance_removeEventState s a ha

/-- Every incident event direction is exactly one legal frontier move: it
either removes its occupied label or adds its unoccupied label. -/
theorem direction_eq_remove_or_add (s : LowerSet α) (d : EventDirection s) :
    (∃ ha : RemovableEvent s (directionEvent s d),
        d.1 = removeEventState s (directionEvent s d) ha) ∨
      (∃ ha : AddableEvent s (directionEvent s d),
        d.1 = addEventState s (directionEvent s d) ha) := by
  let e := directionEvent s d
  have hesep : e ∈ separatingEvents s d.1 :=
    directionEvent_mem_separatingEvents s d
  have hediff : (e ∈ s) ≠ (e ∈ d.1) :=
    mem_separatingEvents_iff.mp hesep
  by_cases hes : e ∈ s
  · have hed : e ∉ d.1 := by
      intro hed
      exact hediff (propext ⟨fun _ => hed, fun _ => hes⟩)
    have hrem : RemovableEvent s e := by
      refine ⟨hes, ?_⟩
      intro b hbs heb
      by_contra hbe
      have hbd : b ∉ d.1 := by
        intro hbd
        exact hed (d.1.lower heb hbd)
      have hbsep : b ∈ separatingEvents s d.1 :=
        mem_separatingEvents_iff.mpr (by simp [hbs, hbd])
      have : b = e := by
        rw [separatingEvents_direction_eq_singleton] at hbsep
        simpa using hbsep
      exact hbe this
    exact Or.inl ⟨hrem, by
      apply LowerSet.ext
      ext x
      by_cases hxe : x = e
      · subst x
        simp [e, hes, hed]
      · have hxsep : x ∉ separatingEvents s d.1 := by
          rw [separatingEvents_direction_eq_singleton]
          simpa [e] using hxe
        have hxiff := mem_iff_of_not_mem_separatingEvents s d.1 x hxsep
        simpa [e, hxe] using hxiff.symm⟩
  · have hed : e ∈ d.1 := by
      by_contra hnot
      exact hediff (propext ⟨fun h => (hes h).elim, fun h => (hnot h).elim⟩)
    have hadd : AddableEvent s e := by
      refine ⟨hes, ?_⟩
      intro b hbe hne
      have hbd : b ∈ d.1 := d.1.lower hbe hed
      by_contra hbs
      have hbsep : b ∈ separatingEvents s d.1 :=
        mem_separatingEvents_iff.mpr (by simp [hbs, hbd])
      have : b = e := by
        rw [separatingEvents_direction_eq_singleton] at hbsep
        simpa using hbsep
      exact hne this
    exact Or.inr ⟨hadd, by
      apply LowerSet.ext
      ext x
      by_cases hxe : x = e
      · subst x
        simp [e, hes, hed]
      · have hxsep : x ∉ separatingEvents s d.1 := by
          rw [separatingEvents_direction_eq_singleton]
          simpa [e] using hxe
        have hxiff := mem_iff_of_not_mem_separatingEvents s d.1 x hxsep
        simpa [e, hxe] using hxiff.symm⟩

/-- State reached by a commuting removal/addition pair. -/
def exchangeEventState (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) (hab : ¬a ≤ b) :
    LowerSet α where
  carrier := {x | (x ∈ s ∧ x ≠ a) ∨ x = b}
  lower' := by
    intro x y hyx hx
    rcases hx with hx | hxb
    · refine Or.inl ⟨s.lower hyx hx.1, ?_⟩
      intro hya
      subst y
      exact hx.2 (ha.2 x hx.1 hyx)
    · subst x
      by_cases hyb : y = b
      · exact Or.inr hyb
      · have hys : y ∈ s := hb.2 y hyx hyb
        exact Or.inl ⟨hys, fun hya => hab (hya ▸ hyx)⟩

omit [Fintype α] in
@[simp]
theorem mem_exchangeEventState_iff (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) (hab : ¬a ≤ b)
    (x : α) :
    x ∈ exchangeEventState s a b ha hb hab ↔
      (x ∈ s ∧ x ≠ a) ∨ x = b :=
  Iff.rfl

theorem remove_adj_exchange (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) (hab : ¬a ≤ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (removeEventState s a ha) (exchangeEventState s a b ha hb hab) := by
  rw [show (lowerSetTransitionGraph (α := α)).Adj
      (removeEventState s a ha) (exchangeEventState s a b ha hb hab) ↔
      lowerSetDistance (removeEventState s a ha)
        (exchangeEventState s a b ha hb hab) = 1 by rfl]
  rw [lowerSetDistance_eq_card_filter]
  have hba : b ≠ a := by
    intro h
    subst b
    exact hb.1 ha.1
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ removeEventState s a ha) ≠
          (x ∈ exchangeEventState s a b ha hb hab)) = {b} := by
    ext x
    by_cases hxb : x = b
    · subst x
      simp [hb.1, hba]
    · by_cases hxa : x = a <;> simp [hxb, hxa]
  rw [hfilter]
  simp

theorem add_adj_exchange (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) (hab : ¬a ≤ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (addEventState s b hb) (exchangeEventState s a b ha hb hab) := by
  rw [show (lowerSetTransitionGraph (α := α)).Adj
      (addEventState s b hb) (exchangeEventState s a b ha hb hab) ↔
      lowerSetDistance (addEventState s b hb)
        (exchangeEventState s a b ha hb hab) = 1 by rfl]
  rw [lowerSetDistance_eq_card_filter]
  have habne : a ≠ b := by
    intro h
    subst b
    exact hb.1 ha.1
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ addEventState s b hb) ≠
          (x ∈ exchangeEventState s a b ha hb hab)) = {a} := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha.1, habne]
    · by_cases hxb : x = b <;> simp [hxa, hxb, Ne.symm habne]
  rw [hfilter]
  simp

theorem add_remove_complete_square_of_not_le
    (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) (hab : ¬a ≤ b) :
    ∃ w : LowerSet α, w ≠ s ∧
      (lowerSetTransitionGraph (α := α)).Adj (removeEventState s a ha) w ∧
      (lowerSetTransitionGraph (α := α)).Adj (addEventState s b hb) w := by
  refine ⟨exchangeEventState s a b ha hb hab, ?_,
    remove_adj_exchange s a b ha hb hab,
    add_adj_exchange s a b ha hb hab⟩
  intro h
  have hbmem : b ∈ exchangeEventState s a b ha hb hab := by simp
  rw [h] at hbmem
  exact hb.1 hbmem

/-- Adjacent states cannot differ in two distinct event coordinates. -/
theorem adj_not_two_event_differences
    {s t : LowerSet α}
    (hadj : (lowerSetTransitionGraph (α := α)).Adj s t)
    {a b : α} (hab : a ≠ b)
    (ha : (a ∈ s) ≠ (a ∈ t)) (hb : (b ∈ s) ≠ (b ∈ t)) : False := by
  have ha' : a ∈ separatingEvents s t :=
    mem_separatingEvents_iff.mpr ha
  have hb' : b ∈ separatingEvents s t :=
    mem_separatingEvents_iff.mpr hb
  have hsub : ({a, b} : Finset α) ⊆ separatingEvents s t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha'
    · exact hb'
  have hcardle := Finset.card_le_card hsub
  have hsep : (separatingEvents s t).card = 1 := by
    rw [← lowerSetDistance_eq_card_separatingEvents]
    exact hadj
  have hpairs : ({a, b} : Finset α).card = 2 := by simp [hab]
  omega

/-- A causal relation from a removable event to an addable event prevents
the two incident directions from completing to a square. -/
theorem add_remove_no_square_of_le
    (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) (hab : a ≤ b) :
    ¬∃ w : LowerSet α, w ≠ s ∧
      (lowerSetTransitionGraph (α := α)).Adj (removeEventState s a ha) w ∧
      (lowerSetTransitionGraph (α := α)).Adj (addEventState s b hb) w := by
  rintro ⟨w, hws, hrw, haw⟩
  have habne : a ≠ b := by
    intro heq
    subst b
    exact hb.1 ha.1
  obtain ⟨e, he, heuniq⟩ := existsUnique_separatingEvent_of_adj hrw
  have hsep :
      separatingEvents (removeEventState s a ha) w = {e} := by
    apply Finset.Subset.antisymm
    · intro x hx
      simpa using heuniq x hx
    · intro x hx
      have hxe : x = e := by simpa using hx
      subst x
      exact he
  have heab : e = a ∨ e = b := by
    by_contra hnot
    push_neg at hnot
    have hna : a ∉ separatingEvents (removeEventState s a ha) w := by
      rw [hsep]
      simp [Ne.symm hnot.1]
    have hnb : b ∉ separatingEvents (removeEventState s a ha) w := by
      rw [hsep]
      simp [Ne.symm hnot.2]
    have hwa : a ∉ w := by
      have hiff := mem_iff_of_not_mem_separatingEvents
        (removeEventState s a ha) w a hna
      simpa [ha.1] using hiff
    have hwb : b ∉ w := by
      have hiff := mem_iff_of_not_mem_separatingEvents
        (removeEventState s a ha) w b hnb
      simpa [hb.1, Ne.symm habne] using hiff
    have hdifa :
        (a ∈ addEventState s b hb) ≠ (a ∈ w) := by
      simp [ha.1, habne, hwa]
    have hdifb :
        (b ∈ addEventState s b hb) ≠ (b ∈ w) := by
      simp [hwb]
    exact adj_not_two_event_differences haw habne hdifa hdifb
  rcases heab with hea | heb
  · subst e
    apply hws
    apply LowerSet.ext
    ext x
    by_cases hxa : x = a
    · subst x
      have hdiff := mem_separatingEvents_iff.mp he
      have hwa : a ∈ w := by simpa [ha.1] using hdiff
      simp [ha.1, hwa]
    · have hnot : x ∉ separatingEvents (removeEventState s a ha) w := by
        rw [hsep]
        simp [hxa]
      have hiff := mem_iff_of_not_mem_separatingEvents
        (removeEventState s a ha) w x hnot
      simpa [hxa] using hiff.symm
  · subst e
    have hna : a ∉ separatingEvents (removeEventState s a ha) w := by
      rw [hsep]
      simp [habne]
    have hwa : a ∉ w := by
      have hiff := mem_iff_of_not_mem_separatingEvents
        (removeEventState s a ha) w a hna
      simpa [ha.1] using hiff
    have hdiff := mem_separatingEvents_iff.mp he
    have hwb : b ∈ w := by
      simpa [hb.1, Ne.symm habne] using hdiff
    exact hwa (w.lower hab hwb)

/-- Mixed add/remove directions complete to a causal square exactly when the
removed event is not a causal predecessor of the added event. -/
theorem add_remove_square_iff_not_le
    (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) :
    (∃ w : LowerSet α, w ≠ s ∧
      (lowerSetTransitionGraph (α := α)).Adj (removeEventState s a ha) w ∧
      (lowerSetTransitionGraph (α := α)).Adj (addEventState s b hb) w) ↔
      ¬a ≤ b := by
  constructor
  · intro hsquare hab
    exact add_remove_no_square_of_le s a b ha hb hab hsquare
  · exact add_remove_complete_square_of_not_le s a b ha hb

/-- The graph-intrinsic sectional defect of a mixed frontier pair is exactly
the indicator of the underlying causal-order relation. -/
theorem cubicalSectionalDefect_remove_add
    (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : AddableEvent s b) :
    lowerSetCubicalSectionalDefect s
        (removeEventState s a ha) (addEventState s b hb) =
      if a ≤ b then 1 else 0 := by
  unfold lowerSetCubicalSectionalDefect cubicalSectionalDefect
  have hra := adj_removeEventState s a ha
  have hab' := adj_addEventState s b hb
  have hne : removeEventState s a ha ≠ addEventState s b hb := by
    intro heq
    have har : a ∉ removeEventState s a ha := by simp [ha.1]
    have haa : a ∈ addEventState s b hb := by
      have habne : a ≠ b := by
        intro h
        subst b
        exact hb.1 ha.1
      simp [ha.1, habne]
    rw [heq] at har
    exact har haa
  rw [if_pos ⟨hra, hab', hne⟩]
  by_cases hab : a ≤ b
  · rw [if_pos hab, if_neg (add_remove_no_square_of_le s a b ha hb hab)]
  · rw [if_neg hab, if_pos (add_remove_complete_square_of_not_le s a b ha hb hab)]

/-! ## Same-sign frontier squares -/

/-- State obtained by adding two distinct addable events. -/
def addPairEventState (s : LowerSet α) (a b : α)
    (ha : AddableEvent s a) (hb : AddableEvent s b) : LowerSet α where
  carrier := {x | x ∈ s ∨ x = a ∨ x = b}
  lower' := by
    intro x y hyx hx
    rcases hx with hxs | hxa | hxb
    · exact Or.inl (s.lower hyx hxs)
    · subst x
      by_cases hya : y = a
      · exact Or.inr (Or.inl hya)
      · exact Or.inl (ha.2 y hyx hya)
    · subst x
      by_cases hyb : y = b
      · exact Or.inr (Or.inr hyb)
      · exact Or.inl (hb.2 y hyx hyb)

omit [Fintype α] in
@[simp]
theorem mem_addPairEventState_iff (s : LowerSet α) (a b : α)
    (ha : AddableEvent s a) (hb : AddableEvent s b) (x : α) :
    x ∈ addPairEventState s a b ha hb ↔ x ∈ s ∨ x = a ∨ x = b :=
  Iff.rfl

theorem add_left_adj_addPairEventState (s : LowerSet α) (a b : α)
    (ha : AddableEvent s a) (hb : AddableEvent s b) (hne : a ≠ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (addEventState s a ha) (addPairEventState s a b ha hb) := by
  rw [show (lowerSetTransitionGraph (α := α)).Adj
      (addEventState s a ha) (addPairEventState s a b ha hb) ↔
      lowerSetDistance (addEventState s a ha)
        (addPairEventState s a b ha hb) = 1 by rfl]
  rw [lowerSetDistance_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ addEventState s a ha) ≠
          (x ∈ addPairEventState s a b ha hb)) = {b} := by
    ext x
    by_cases hxb : x = b
    · subst x
      simp [hb.1, Ne.symm hne]
    · simp [hxb, or_assoc, or_comm]
  rw [hfilter]
  simp

theorem add_right_adj_addPairEventState (s : LowerSet α) (a b : α)
    (ha : AddableEvent s a) (hb : AddableEvent s b) (hne : a ≠ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (addEventState s b hb) (addPairEventState s a b ha hb) := by
  rw [show (lowerSetTransitionGraph (α := α)).Adj
      (addEventState s b hb) (addPairEventState s a b ha hb) ↔
      lowerSetDistance (addEventState s b hb)
        (addPairEventState s a b ha hb) = 1 by rfl]
  rw [lowerSetDistance_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ addEventState s b hb) ≠
          (x ∈ addPairEventState s a b ha hb)) = {a} := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha.1, hne]
    · simp [hxa, or_assoc, or_comm]
  rw [hfilter]
  simp

theorem add_add_complete_square (s : LowerSet α) (a b : α)
    (ha : AddableEvent s a) (hb : AddableEvent s b) (hne : a ≠ b) :
    ∃ w : LowerSet α, w ≠ s ∧
      (lowerSetTransitionGraph (α := α)).Adj (addEventState s a ha) w ∧
      (lowerSetTransitionGraph (α := α)).Adj (addEventState s b hb) w := by
  refine ⟨addPairEventState s a b ha hb, ?_,
    add_left_adj_addPairEventState s a b ha hb hne,
    add_right_adj_addPairEventState s a b ha hb hne⟩
  intro h
  have hamem : a ∈ addPairEventState s a b ha hb := by simp
  rw [h] at hamem
  exact ha.1 hamem

/-- State obtained by removing two distinct removable events. -/
def removePairEventState (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : RemovableEvent s b) : LowerSet α where
  carrier := {x | x ∈ s ∧ x ≠ a ∧ x ≠ b}
  lower' := by
    intro x y hyx hx
    refine ⟨s.lower hyx hx.1, ?_, ?_⟩
    · intro hya
      subst y
      exact hx.2.1 (ha.2 x hx.1 hyx)
    · intro hyb
      subst y
      exact hx.2.2 (hb.2 x hx.1 hyx)

omit [Fintype α] [DecidableEq α] in
@[simp]
theorem mem_removePairEventState_iff (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : RemovableEvent s b) (x : α) :
    x ∈ removePairEventState s a b ha hb ↔
      x ∈ s ∧ x ≠ a ∧ x ≠ b :=
  Iff.rfl

theorem remove_left_adj_removePairEventState (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : RemovableEvent s b) (hne : a ≠ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (removeEventState s a ha) (removePairEventState s a b ha hb) := by
  rw [show (lowerSetTransitionGraph (α := α)).Adj
      (removeEventState s a ha) (removePairEventState s a b ha hb) ↔
      lowerSetDistance (removeEventState s a ha)
        (removePairEventState s a b ha hb) = 1 by rfl]
  rw [lowerSetDistance_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ removeEventState s a ha) ≠
          (x ∈ removePairEventState s a b ha hb)) = {b} := by
    ext x
    by_cases hxb : x = b
    · subst x
      simp [hb.1, Ne.symm hne]
    · simp [hxb]
  rw [hfilter]
  simp

theorem remove_right_adj_removePairEventState (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : RemovableEvent s b) (hne : a ≠ b) :
    (lowerSetTransitionGraph (α := α)).Adj
      (removeEventState s b hb) (removePairEventState s a b ha hb) := by
  rw [show (lowerSetTransitionGraph (α := α)).Adj
      (removeEventState s b hb) (removePairEventState s a b ha hb) ↔
      lowerSetDistance (removeEventState s b hb)
        (removePairEventState s a b ha hb) = 1 by rfl]
  rw [lowerSetDistance_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun x : α =>
        (x ∈ removeEventState s b hb) ≠
          (x ∈ removePairEventState s a b ha hb)) = {a} := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha.1, hne]
    · simp [hxa]
  rw [hfilter]
  simp

theorem remove_remove_complete_square (s : LowerSet α) (a b : α)
    (ha : RemovableEvent s a) (hb : RemovableEvent s b) (hne : a ≠ b) :
    ∃ w : LowerSet α, w ≠ s ∧
      (lowerSetTransitionGraph (α := α)).Adj (removeEventState s a ha) w ∧
      (lowerSetTransitionGraph (α := α)).Adj (removeEventState s b hb) w := by
  refine ⟨removePairEventState s a b ha hb, ?_,
    remove_left_adj_removePairEventState s a b ha hb hne,
    remove_right_adj_removePairEventState s a b ha hb hne⟩
  intro h
  have hanmem : a ∉ removePairEventState s a b ha hb := by simp
  rw [h] at hanmem
  exact hanmem ha.1

/-! ## Frontier order-curvature correspondence -/

/-- The outgoing labels which remove a maximal occupied event. -/
abbrev RemovableFrontier (s : LowerSet α) :=
  {a : α // RemovableEvent s a}

/-- The outgoing labels which add a minimal unoccupied event. -/
abbrev AddableFrontier (s : LowerSet α) :=
  {b : α // AddableEvent s b}

/-- A removable frontier label, bundled as the corresponding graph
direction. -/
def removeFrontierDirection (s : LowerSet α) (a : RemovableFrontier s) :
    EventDirection s := by
  letI : DecidableEq α := Classical.decEq α
  refine ⟨removeEventState s a.1 a.2, ?_⟩
  exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
    (v := s) (removeEventState s a.1 a.2)).mpr
      (adj_removeEventState s a.1 a.2)

/-- An addable frontier label, bundled as the corresponding graph direction. -/
def addFrontierDirection (s : LowerSet α) (b : AddableFrontier s) :
    EventDirection s := by
  letI : DecidableEq α := Classical.decEq α
  refine ⟨addEventState s b.1 b.2, ?_⟩
  exact ((lowerSetTransitionGraph (α := α)).mem_neighborFinset
    (v := s) (addEventState s b.1 b.2)).mpr
      (adj_addEventState s b.1 b.2)

omit [DecidableEq α] in
@[simp]
theorem directionEvent_removeFrontierDirection
    (s : LowerSet α) (a : RemovableFrontier s) :
    directionEvent s (removeFrontierDirection s a) = a.1 := by
  have haSep : a.1 ∈
      separatingEvents s (removeFrontierDirection s a).1 := by
    change a.1 ∈ separatingEvents s (removeEventState s a.1 a.2)
    apply mem_separatingEvents_iff.mpr
    simp [a.2.1]
  rw [separatingEvents_direction_eq_singleton] at haSep
  have h := Finset.mem_singleton.mp haSep
  exact h.symm

@[simp]
theorem directionEvent_addFrontierDirection
    (s : LowerSet α) (b : AddableFrontier s) :
    directionEvent s (addFrontierDirection s b) = b.1 := by
  have hbSep : b.1 ∈
      separatingEvents s (addFrontierDirection s b).1 := by
    change b.1 ∈ separatingEvents s (addEventState s b.1 b.2)
    apply mem_separatingEvents_iff.mpr
    simp [b.2.1]
  rw [separatingEvents_direction_eq_singleton] at hbSep
  have h := Finset.mem_singleton.mp hbSep
  exact h.symm

/-- Convert either kind of legal frontier event into its unique incident
graph direction. -/
def frontierDirection (s : LowerSet α) :
    RemovableFrontier s ⊕ AddableFrontier s → EventDirection s
  | Sum.inl a => removeFrontierDirection s a
  | Sum.inr b => addFrontierDirection s b

theorem frontierDirection_injective (s : LowerSet α) :
    Function.Injective (frontierDirection s) := by
  intro x y hxy
  have he := congrArg (directionEvent s) hxy
  rcases x with a | a <;> rcases y with b | b
  · congr 1
    apply Subtype.ext
    simpa [frontierDirection] using he
  · have hab : a.1 = b.1 := by
      simpa [frontierDirection] using he
    exact (b.2.1 (hab ▸ a.2.1)).elim
  · have hab : a.1 = b.1 := by
      simpa [frontierDirection] using he
    exact (a.2.1 (hab.symm ▸ b.2.1)).elim
  · congr 1
    apply Subtype.ext
    simpa [frontierDirection] using he

theorem frontierDirection_surjective (s : LowerSet α) :
    Function.Surjective (frontierDirection s) := by
  intro d
  rcases direction_eq_remove_or_add s d with ⟨ha, hd⟩ | ⟨hb, hd⟩
  · refine ⟨Sum.inl ⟨directionEvent s d, ha⟩, ?_⟩
    apply Subtype.ext
    change removeEventState s (directionEvent s d) ha = d.1
    exact hd.symm
  · refine ⟨Sum.inr ⟨directionEvent s d, hb⟩, ?_⟩
    apply Subtype.ext
    change addEventState s (directionEvent s d) hb = d.1
    exact hd.symm

/-- The intrinsic tangent directions at a causal state are canonically
equivalent to its removable frontier plus its addable frontier. -/
noncomputable def frontierDirectionEquiv (s : LowerSet α) :
    RemovableFrontier s ⊕ AddableFrontier s ≃ EventDirection s :=
  Equiv.ofBijective (frontierDirection s)
    ⟨frontierDirection_injective s, frontierDirection_surjective s⟩

/-- Mixed sectional curvature evaluated on one removable and one addable
frontier direction. -/
def mixedFrontierSectionalDefect (s : LowerSet α)
    (a : RemovableFrontier s) (b : AddableFrontier s) : ℕ :=
  lowerSetCubicalSectionalDefect s
    (removeEventState s a.1 a.2) (addEventState s b.1 b.2)

/-- Exact local order-curvature formula: mixed sectional curvature is the
indicator kernel of the causal order across the two sides of the frontier. -/
theorem mixedFrontierSectionalDefect_eq_orderIndicator
    (s : LowerSet α) (a : RemovableFrontier s) (b : AddableFrontier s) :
    mixedFrontierSectionalDefect s a b =
      if a.1 ≤ b.1 then 1 else 0 := by
  exact cubicalSectionalDefect_remove_add s a.1 b.1 a.2 b.2

/-- Thus the causal relation between opposite frontier directions can be
reconstructed from positive mixed sectional curvature. -/
theorem causalOrder_iff_mixedFrontierSectionalDefect_pos
    (s : LowerSet α) (a : RemovableFrontier s) (b : AddableFrontier s) :
    a.1 ≤ b.1 ↔ 0 < mixedFrontierSectionalDefect s a b := by
  rw [mixedFrontierSectionalDefect_eq_orderIndicator]
  by_cases hab : a.1 ≤ b.1 <;> simp [hab]

/-- Number of causal incidences crossing the active frontier, expressed as
the sum of its order-indicator kernel. -/
def frontierCausalIncidenceCount (s : LowerSet α) : ℕ :=
  ∑ a : RemovableFrontier s, ∑ b : AddableFrontier s,
    if a.1 ≤ b.1 then 1 else 0

/-- Aggregate mixed cubical curvature at a causal state. -/
def totalMixedFrontierCurvature (s : LowerSet α) : ℕ :=
  ∑ a : RemovableFrontier s, ∑ b : AddableFrontier s,
    mixedFrontierSectionalDefect s a b

/-- Total mixed frontier curvature is exactly the number of causal-order
incidences crossing the active frontier. -/
theorem totalMixedFrontierCurvature_eq_frontierCausalIncidenceCount
    (s : LowerSet α) :
    totalMixedFrontierCurvature s = frontierCausalIncidenceCount s := by
  unfold totalMixedFrontierCurvature frontierCausalIncidenceCount
  simp_rw [mixedFrontierSectionalDefect_eq_orderIndicator]

/-- Two removable frontier directions always have zero sectional defect. -/
theorem cubicalSectionalDefect_remove_remove_eq_zero
    (s : LowerSet α) (a b : RemovableFrontier s) :
    lowerSetCubicalSectionalDefect s
      (removeEventState s a.1 a.2) (removeEventState s b.1 b.2) = 0 := by
  by_cases hab : a = b
  · subst b
    exact cubicalSectionalDefect_self
      (lowerSetTransitionGraph (α := α)) s (removeEventState s a.1 a.2)
  · have hlabel : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    have hstates :
        removeEventState s a.1 a.2 ≠ removeEventState s b.1 b.2 := by
      intro h
      have hd : removeFrontierDirection s a = removeFrontierDirection s b := by
        apply Subtype.ext
        exact h
      have he := congrArg (directionEvent s) hd
      exact hlabel (by simpa using he)
    unfold lowerSetCubicalSectionalDefect cubicalSectionalDefect
    rw [if_pos ⟨adj_removeEventState s a.1 a.2,
      adj_removeEventState s b.1 b.2, hstates⟩]
    rw [if_pos (remove_remove_complete_square s a.1 b.1 a.2 b.2 hlabel)]

/-- Two addable frontier directions always have zero sectional defect. -/
theorem cubicalSectionalDefect_add_add_eq_zero
    (s : LowerSet α) (a b : AddableFrontier s) :
    lowerSetCubicalSectionalDefect s
      (addEventState s a.1 a.2) (addEventState s b.1 b.2) = 0 := by
  by_cases hab : a = b
  · subst b
    exact cubicalSectionalDefect_self
      (lowerSetTransitionGraph (α := α)) s (addEventState s a.1 a.2)
  · have hlabel : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    have hstates : addEventState s a.1 a.2 ≠ addEventState s b.1 b.2 := by
      intro h
      have hd : addFrontierDirection s a = addFrontierDirection s b := by
        apply Subtype.ext
        exact h
      have he := congrArg (directionEvent s) hd
      exact hlabel (by simpa using he)
    unfold lowerSetCubicalSectionalDefect cubicalSectionalDefect
    rw [if_pos ⟨adj_addEventState s a.1 a.2,
      adj_addEventState s b.1 b.2, hstates⟩]
    rw [if_pos (add_add_complete_square s a.1 b.1 a.2 b.2 hlabel)]

/-- The full sectional kernel expressed in the complete frontier frame. -/
def frontierSectionalKernel (s : LowerSet α)
    (x y : RemovableFrontier s ⊕ AddableFrontier s) : ℕ :=
  lowerSetCubicalSectionalDefect s
    (frontierDirection s x).1 (frontierDirection s y).1

/-- Classification of every directional two-plane: same-sign planes are
flat, while a mixed plane is the indicator of causal precedence. -/
theorem frontierSectionalKernel_eq
    (s : LowerSet α) (x y : RemovableFrontier s ⊕ AddableFrontier s) :
    frontierSectionalKernel s x y =
      match x, y with
      | Sum.inl _, Sum.inl _ => 0
      | Sum.inl a, Sum.inr b => if a.1 ≤ b.1 then 1 else 0
      | Sum.inr b, Sum.inl a => if a.1 ≤ b.1 then 1 else 0
      | Sum.inr _, Sum.inr _ => 0 := by
  rcases x with a | b <;> rcases y with c | d
  · exact cubicalSectionalDefect_remove_remove_eq_zero s a c
  · exact mixedFrontierSectionalDefect_eq_orderIndicator s a d
  · rw [show frontierSectionalKernel s (Sum.inr b) (Sum.inl c) =
        frontierSectionalKernel s (Sum.inl c) (Sum.inr b) by
      unfold frontierSectionalKernel lowerSetCubicalSectionalDefect
      exact cubicalSectionalDefect_symm
        (lowerSetTransitionGraph (α := α)) s _ _]
    exact mixedFrontierSectionalDefect_eq_orderIndicator s c b
  · exact cubicalSectionalDefect_add_add_eq_zero s b d

/-- Sum of the sectional kernel over all ordered pairs in the complete
frontier frame. -/
def totalFrontierSectionalCurvature (s : LowerSet α) : ℕ :=
  ∑ x : RemovableFrontier s ⊕ AddableFrontier s,
    ∑ y : RemovableFrontier s ⊕ AddableFrontier s,
      frontierSectionalKernel s x y

/-- The same curvature trace written directly over all graph directions. -/
def totalDirectionalSectionalCurvature (s : LowerSet α) : ℕ :=
  ∑ d : EventDirection s, ∑ e : EventDirection s,
    lowerSetCubicalSectionalDefect s d.1 e.1

/-- Reindexing by the frontier equivalence does not change the full
directional curvature trace. -/
theorem totalDirectionalSectionalCurvature_eq_frontier
    (s : LowerSet α) :
    totalDirectionalSectionalCurvature s =
      totalFrontierSectionalCurvature s := by
  unfold totalDirectionalSectionalCurvature totalFrontierSectionalCurvature
  let E := frontierDirectionEquiv s
  calc
    (∑ d : EventDirection s, ∑ e : EventDirection s,
        lowerSetCubicalSectionalDefect s d.1 e.1) =
        ∑ x : RemovableFrontier s ⊕ AddableFrontier s,
          ∑ e : EventDirection s,
            lowerSetCubicalSectionalDefect s (E x).1 e.1 := by
      exact (E.sum_comp (fun d => ∑ e : EventDirection s,
        lowerSetCubicalSectionalDefect s d.1 e.1)).symm
    _ = ∑ x : RemovableFrontier s ⊕ AddableFrontier s,
          ∑ y : RemovableFrontier s ⊕ AddableFrontier s,
            lowerSetCubicalSectionalDefect s (E x).1 (E y).1 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact (E.sum_comp (fun e =>
        lowerSetCubicalSectionalDefect s (E x).1 e.1)).symm
    _ = ∑ x : RemovableFrontier s ⊕ AddableFrontier s,
          ∑ y : RemovableFrontier s ⊕ AddableFrontier s,
            frontierSectionalKernel s x y := by
      rfl

/-- Exact scalar trace formula: the full ordered sectional curvature equals
twice the number of causal incidences crossing the active frontier. -/
theorem totalDirectionalSectionalCurvature_eq_two_mul_incidenceCount
    (s : LowerSet α) :
    totalDirectionalSectionalCurvature s =
      2 * frontierCausalIncidenceCount s := by
  rw [totalDirectionalSectionalCurvature_eq_frontier]
  unfold totalFrontierSectionalCurvature frontierCausalIncidenceCount
  simp_rw [Fintype.sum_sum_type]
  simp_rw [frontierSectionalKernel_eq]
  simp only [Finset.sum_const_zero, add_zero, zero_add]
  rw [Finset.sum_comm]
  omega

end
end CausalAlgebraicGeometry.CAGDirectionalGeometry
