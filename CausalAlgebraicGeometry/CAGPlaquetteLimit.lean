/-
  CAGPlaquetteLimit.lean — Causal squares and a continuum mixed Hessian.

  In the two-chain scaling family, the next event in each causal component is
  independently addable.  The resulting two-direction `CausalCube` is the
  elementary rectangular plaquette.  Its four vertices are identified with
  the four expected grid states, and its directions form an edge in the
  intrinsic cubical link.

  Evaluating a scalar field around this causal square gives an intrinsic
  mixed difference.  After scaling by h^2, that difference is proved to equal
  the continuum mixed derivative at the cell center for the coupled quartic
  test class of `CAGTwoDimensionalLimit`.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGTwoDimensionalLimit

namespace CausalAlgebraicGeometry.CAGPlaquetteLimit

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGCubicalComplex
open CausalAlgebraicGeometry.CAGCubicalComplex.CausalCube
open CausalAlgebraicGeometry.CAGScalingLimit
open CausalAlgebraicGeometry.CAGTwoDimensionalLimit

noncomputable section
open scoped Classical

/-! ## The elementary causal plaquette -/

/-- The next unrealized event in the first causal-chain component. -/
def nextXEvent {n m : ℕ} (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) : Fin n ⊕ Fin m :=
  Sum.inl ⟨p.1.val, hxn⟩

/-- The next unrealized event in the second causal-chain component. -/
def nextYEvent {n m : ℕ} (p : Fin (n + 1) × Fin (m + 1))
    (hym : p.2.val < m) : Fin n ⊕ Fin m :=
  Sum.inr ⟨p.2.val, hym⟩

/-- The next first-axis event is intrinsically addable at the corresponding
rectangular causal state. -/
theorem nextXEvent_addable {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1)) (hxn : p.1.val < n) :
    AddableEvent (rectangularState n m p) (nextXEvent p hxn) := by
  constructor
  · simp [nextXEvent]
  · rintro (b | b) hb hne
    · simp [nextXEvent] at hb
      change b.val < p.1.val
      have hbval : b.val ≤ p.1.val := Fin.mk_le_mk.mp hb
      have hbne : b.val ≠ p.1.val := by
        intro hv
        apply hne
        simp [nextXEvent, Fin.ext_iff, hv]
      omega
    · simp [nextXEvent] at hb

/-- The next second-axis event is intrinsically addable at the corresponding
rectangular causal state. -/
theorem nextYEvent_addable {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1)) (hym : p.2.val < m) :
    AddableEvent (rectangularState n m p) (nextYEvent p hym) := by
  constructor
  · simp [nextYEvent]
  · rintro (b | b) hb hne
    · simp [nextYEvent] at hb
    · simp [nextYEvent] at hb
      change b.val < p.2.val
      have hbval : b.val ≤ p.2.val := Fin.mk_le_mk.mp hb
      have hbne : b.val ≠ p.2.val := by
        intro hv
        apply hne
        simp [nextYEvent, Fin.ext_iff, hv]
      omega

/-- The two independently addable next events form an intrinsic causal
two-cube. -/
def rectangularPlaquette {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    CausalCube (Fin n ⊕ Fin m) where
  base := rectangularState n m p
  directions := {nextXEvent p hxn, nextYEvent p hym}
  addable := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact nextXEvent_addable p hxn
    · exact nextYEvent_addable p hym

/-- The elementary causal plaquette really has cubical dimension two. -/
@[simp]
theorem rectangularPlaquette_dimension {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    (rectangularPlaquette p hxn hym).dimension = 2 := by
  simp [rectangularPlaquette, CausalCube.dimension,
    nextXEvent, nextYEvent]

/-- Opposite corner after advancing both causal-chain coordinates. -/
def rectangularUpperRight {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    Fin (n + 1) × Fin (m + 1) :=
  (chainRight p.1 hxn, chainRight p.2 hym)

theorem rectangularPlaquette_vertex_x {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    (rectangularPlaquette p hxn hym).vertex
      ((rectangularPlaquette p hxn hym).singletonFace
        (nextXEvent p hxn) (by simp [rectangularPlaquette])) =
      rectangularState n m (rectangularRightX p hxn) := by
  apply LowerSet.ext
  ext e
  cases e with
  | inl a =>
      simp [CausalCube.mem_vertex_iff, rectangularPlaquette, nextXEvent,
        rectangularRightX, CausalCube.singletonFace, Fin.ext_iff]
      omega
  | inr b =>
      simp [CausalCube.mem_vertex_iff, rectangularPlaquette, nextXEvent,
        rectangularRightX, CausalCube.singletonFace]

theorem rectangularPlaquette_vertex_y {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    (rectangularPlaquette p hxn hym).vertex
      ((rectangularPlaquette p hxn hym).singletonFace
        (nextYEvent p hym) (by simp [rectangularPlaquette])) =
      rectangularState n m (rectangularRightY p hym) := by
  apply LowerSet.ext
  ext e
  cases e with
  | inl a =>
      simp [CausalCube.mem_vertex_iff, rectangularPlaquette, nextYEvent,
        rectangularRightY, CausalCube.singletonFace]
  | inr b =>
      simp [CausalCube.mem_vertex_iff, rectangularPlaquette, nextYEvent,
        rectangularRightY, CausalCube.singletonFace, Fin.ext_iff]
      omega

theorem rectangularPlaquette_vertex_xy {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    (rectangularPlaquette p hxn hym).vertex
      ((rectangularPlaquette p hxn hym).pairFace
        (nextXEvent p hxn) (nextYEvent p hym)
        (by simp [rectangularPlaquette])
        (by simp [rectangularPlaquette])) =
      rectangularState n m (rectangularUpperRight p hxn hym) := by
  apply LowerSet.ext
  ext e
  cases e with
  | inl a =>
      simp [CausalCube.mem_vertex_iff, rectangularPlaquette, nextXEvent,
        nextYEvent, rectangularUpperRight, CausalCube.pairFace, Fin.ext_iff]
      omega
  | inr b =>
      simp [CausalCube.mem_vertex_iff, rectangularPlaquette, nextXEvent,
        nextYEvent, rectangularUpperRight, CausalCube.pairFace, Fin.ext_iff]
      omega

/-- First-axis direction as a vertex of the cubical link. -/
def rectangularPlaquetteXDirection {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    {a : Fin n ⊕ Fin m // a ∈ (rectangularPlaquette p hxn hym).directions} :=
  ⟨nextXEvent p hxn, by simp [rectangularPlaquette]⟩

/-- Second-axis direction as a vertex of the cubical link. -/
def rectangularPlaquetteYDirection {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    {a : Fin n ⊕ Fin m // a ∈ (rectangularPlaquette p hxn hym).directions} :=
  ⟨nextYEvent p hym, by simp [rectangularPlaquette]⟩

theorem rectangularPlaquette_directions_ne {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    rectangularPlaquetteXDirection p hxn hym ≠
      rectangularPlaquetteYDirection p hxn hym := by
  intro h
  have hv := congrArg Subtype.val h
  simp [rectangularPlaquetteXDirection, rectangularPlaquetteYDirection,
    nextXEvent, nextYEvent] at hv

/-- The two coordinate moves are adjacent in the intrinsic cubical link:
the link itself detects their causal square. -/
theorem rectangularPlaquette_link_adj {n m : ℕ}
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    (cubicalLink
      (lowerSetTransitionGraph (α := Fin n ⊕ Fin m))
      (rectangularPlaquette p hxn hym).base).Adj
        ((rectangularPlaquette p hxn hym).linkDirection
          (rectangularPlaquetteXDirection p hxn hym))
        ((rectangularPlaquette p hxn hym).linkDirection
          (rectangularPlaquetteYDirection p hxn hym)) := by
  exact (rectangularPlaquette p hxn hym).linkDirection_adj
    (rectangularPlaquetteXDirection p hxn hym)
    (rectangularPlaquetteYDirection p hxn hym)
    (rectangularPlaquette_directions_ne p hxn hym)

/-! ## Intrinsic mixed difference and continuum Hessian -/

/-- Alternating scalar-field sum around an oriented elementary causal
plaquette. -/
def causalCubeMixedDifference {α : Type*} [PartialOrder α] [Fintype α]
    [DecidableEq α] (Q : CausalCube α) (φ : LowerSet α → ℝ)
    (a b : α) (ha : a ∈ Q.directions) (hb : b ∈ Q.directions) : ℝ :=
  φ (Q.vertex (Q.pairFace a b ha hb)) -
    φ (Q.vertex (Q.singletonFace a ha)) -
    φ (Q.vertex (Q.singletonFace b hb)) + φ Q.base

/-- Coordinate expression for the field difference around the intrinsic
causal plaquette. -/
def rectangularPlaquetteDifference {n m : ℕ}
    (φ : LowerSet (Fin n ⊕ Fin m) → ℝ)
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) : ℝ :=
  φ (rectangularState n m (rectangularUpperRight p hxn hym)) -
    φ (rectangularState n m (rectangularRightX p hxn)) -
    φ (rectangularState n m (rectangularRightY p hym)) +
    φ (rectangularState n m p)

/-- The coordinate expression is exactly the alternating sum over the four
vertices of the certified `CausalCube`. -/
theorem rectangularPlaquetteDifference_eq_causalCube {n m : ℕ}
    (φ : LowerSet (Fin n ⊕ Fin m) → ℝ)
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    rectangularPlaquetteDifference φ p hxn hym =
      causalCubeMixedDifference (rectangularPlaquette p hxn hym) φ
        (nextXEvent p hxn) (nextYEvent p hym)
        (by simp [rectangularPlaquette])
        (by simp [rectangularPlaquette]) := by
  unfold rectangularPlaquetteDifference causalCubeMixedDifference
  rw [rectangularPlaquette_vertex_xy,
    rectangularPlaquette_vertex_x,
    rectangularPlaquette_vertex_y]
  rfl

/-- Coordinate of the upper-right vertex of the elementary plaquette. -/
theorem rectangularCoordinate_upperRight {n m : ℕ} (h : ℝ)
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    rectangularCoordinate h (rectangularUpperRight p hxn hym) =
      ((rectangularCoordinate h p).1 + h,
        (rectangularCoordinate h p).2 + h) := by
  apply Prod.ext
  · exact chainCoordinate_right h p.1 hxn
  · exact chainCoordinate_right h p.2 hym

/-- Mesh-scaled mixed difference of a sampled continuum field around a
certified causal square. -/
def scaledRectangularPlaquetteDifference (n m : ℕ) (h : ℝ)
    (f : ℝ × ℝ → ℝ) (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) : ℝ :=
  rectangularPlaquetteDifference (rectangularSample n m h f)
    p hxn hym / h ^ 2

/-- Exact forward-difference formula obtained from the intrinsic causal
square. -/
theorem scaledRectangularPlaquetteDifference_eq_forwardMixed
    (n m : ℕ) (h : ℝ) (f : ℝ × ℝ → ℝ)
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    scaledRectangularPlaquetteDifference n m h f p hxn hym =
      (f ((rectangularCoordinate h p).1 + h,
          (rectangularCoordinate h p).2 + h) -
        f ((rectangularCoordinate h p).1 + h,
          (rectangularCoordinate h p).2) -
        f ((rectangularCoordinate h p).1,
          (rectangularCoordinate h p).2 + h) +
        f (rectangularCoordinate h p)) / h ^ 2 := by
  unfold scaledRectangularPlaquetteDifference rectangularPlaquetteDifference
  simp only [rectangularSample_rectangularState]
  rw [rectangularCoordinate_upperRight h p hxn hym,
    rectangularCoordinate_rightX h p hxn,
    rectangularCoordinate_rightY h p hym]

/-- Continuum mixed derivative of the coupled quartic surface. -/
def quarticSurfaceMixedDerivative (c : QuarticSurfaceCoefficients)
    (p : ℝ × ℝ) : ℝ :=
  4 * c.x2y2 * p.1 * p.2 + c.xy

/-- Center of an elementary continuum plaquette with lower-left corner `p`. -/
def plaquetteCenter (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + h / 2, p.2 + h / 2)

/-- The causal forward mixed difference is an exact cell-centered mixed
derivative on the coupled quartic class.  Pure x- and y-polynomials cancel;
the nontrivial `x^2 y^2` coupling is recovered exactly. -/
theorem quarticSurface_forwardMixed_exact
    (c : QuarticSurfaceCoefficients) (p : ℝ × ℝ)
    (h : ℝ) (hh : h ≠ 0) :
    (quarticSurface c (p.1 + h, p.2 + h) -
      quarticSurface c (p.1 + h, p.2) -
      quarticSurface c (p.1, p.2 + h) + quarticSurface c p) / h ^ 2 =
        quarticSurfaceMixedDerivative c (plaquetteCenter h p) := by
  unfold quarticSurface quarticSurfaceMixedDerivative plaquetteCenter
  field_simp [hh]
  ring

/-- **CAUSAL PLAQUETTE/HESSIAN THEOREM.** The mesh-scaled alternating sum
around the intrinsic two-event causal cube is exactly the continuum mixed
Hessian component at the cell center for every coupled quartic test surface. -/
theorem scaledRectangularPlaquette_quartic_exact
    (n m : ℕ) (c : QuarticSurfaceCoefficients) (h : ℝ) (hh : h ≠ 0)
    (p : Fin (n + 1) × Fin (m + 1))
    (hxn : p.1.val < n) (hym : p.2.val < m) :
    scaledRectangularPlaquetteDifference n m h (quarticSurface c)
        p hxn hym =
      quarticSurfaceMixedDerivative c
        (plaquetteCenter h (rectangularCoordinate h p)) := by
  rw [scaledRectangularPlaquetteDifference_eq_forwardMixed]
  exact quarticSurface_forwardMixed_exact
    c (rectangularCoordinate h p) h hh

end
end CausalAlgebraicGeometry.CAGPlaquetteLimit
