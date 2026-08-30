/-
  CAGTwoDimensionalLimit.lean — A controlled two-dimensional scaling family.

  The event poset is the disjoint sum of two finite causal chains.  Its
  downsets are proved to be exactly pairs of chain prefixes, and its intrinsic
  transition graph is therefore the box product of two path graphs.  This is
  a CAG-generated rectangular lattice: the grid is recovered from the causal
  order rather than imposed as an unrelated graph.

  The intrinsic graph Laplacian is identified with the five-point finite
  difference operator.  On a coupled quartic class, the comparison with the
  negative Euclidean Laplacian has an exact uniform O(h^2) error.  Elementary
  causal squares additionally recover the mixed continuum Hessian on the
  same test class.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGScalingLimit
import Mathlib.Combinatorics.SimpleGraph.Prod

namespace CausalAlgebraicGeometry.CAGTwoDimensionalLimit

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGFiniteCausalDynamics
open CausalAlgebraicGeometry.CAGCubicalComplex
open CausalAlgebraicGeometry.CAGScalingLimit

noncomputable section
open scoped Classical

/-! ## Downsets of a disjoint pair of chains -/

/-- Combine lower sets in two causally disconnected components.  Mathlib's
order on `Sum` makes elements in different summands incomparable. -/
def sumLowerSet {α β : Type*} [PartialOrder α] [PartialOrder β]
    (s : LowerSet α) (t : LowerSet β) : LowerSet (α ⊕ β) where
  carrier := Sum.elim (fun a => a ∈ s) (fun b => b ∈ t)
  lower' := by
    rintro (a | b) (a' | b') hab hb
    · exact s.lower (by simpa using hab) hb
    · simp at hab
    · simp at hab
    · exact t.lower (by simpa using hab) hb

@[simp]
theorem mem_sumLowerSet_inl {α β : Type*} [PartialOrder α] [PartialOrder β]
    {s : LowerSet α} {t : LowerSet β} {a : α} :
    Sum.inl a ∈ sumLowerSet s t ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem mem_sumLowerSet_inr {α β : Type*} [PartialOrder α] [PartialOrder β]
    {s : LowerSet α} {t : LowerSet β} {b : β} :
    Sum.inr b ∈ sumLowerSet s t ↔ b ∈ t :=
  Iff.rfl

/-- Restriction of a sum-poset downset to its left causal component. -/
def leftSlice {α β : Type*} [PartialOrder α] [PartialOrder β]
    (s : LowerSet (α ⊕ β)) : LowerSet α where
  carrier := {a | Sum.inl a ∈ s}
  lower' := by
    intro a a' haa' ha'
    exact s.lower (by simpa using haa') ha'

/-- Restriction of a sum-poset downset to its right causal component. -/
def rightSlice {α β : Type*} [PartialOrder α] [PartialOrder β]
    (s : LowerSet (α ⊕ β)) : LowerSet β where
  carrier := {b | Sum.inr b ∈ s}
  lower' := by
    intro b b' hbb' hb'
    exact s.lower (by simpa using hbb') hb'

@[simp]
theorem mem_leftSlice {α β : Type*} [PartialOrder α] [PartialOrder β]
    {s : LowerSet (α ⊕ β)} {a : α} :
    a ∈ leftSlice s ↔ Sum.inl a ∈ s :=
  Iff.rfl

@[simp]
theorem mem_rightSlice {α β : Type*} [PartialOrder α] [PartialOrder β]
    {s : LowerSet (α ⊕ β)} {b : β} :
    b ∈ rightSlice s ↔ Sum.inr b ∈ s :=
  Iff.rfl

/-- Lower sets of a disjoint sum of posets are exactly pairs of lower sets. -/
def sumLowerSetEquiv {α β : Type*} [PartialOrder α] [PartialOrder β] :
    LowerSet α × LowerSet β ≃ LowerSet (α ⊕ β) where
  toFun p := sumLowerSet p.1 p.2
  invFun s := (leftSlice s, rightSlice s)
  left_inv p := by
    apply Prod.ext
    · apply LowerSet.ext
      ext a
      rfl
    · apply LowerSet.ext
      ext b
      rfl
  right_inv s := by
    apply LowerSet.ext
    ext e
    cases e <;> rfl

/-- State with `i` realized events in the first chain and `j` in the second. -/
def rectangularState (n m : ℕ) (p : Fin (n + 1) × Fin (m + 1)) :
    LowerSet (Fin n ⊕ Fin m) :=
  sumLowerSet (chainState n p.1) (chainState m p.2)

@[simp]
theorem mem_rectangularState_inl_iff {n m : ℕ}
    {p : Fin (n + 1) × Fin (m + 1)} {a : Fin n} :
    Sum.inl a ∈ rectangularState n m p ↔ a.val < p.1.val :=
  Iff.rfl

@[simp]
theorem mem_rectangularState_inr_iff {n m : ℕ}
    {p : Fin (n + 1) × Fin (m + 1)} {b : Fin m} :
    Sum.inr b ∈ rectangularState n m p ↔ b.val < p.2.val :=
  Iff.rfl

/-- Exact coordinate equivalence for every state of the two-chain causal
family. -/
def rectangularStateEquiv (n m : ℕ) :
    Fin (n + 1) × Fin (m + 1) ≃ LowerSet (Fin n ⊕ Fin m) :=
  (Equiv.prodCongr (chainStateEquiv n) (chainStateEquiv m)).trans
    sumLowerSetEquiv

@[simp]
theorem rectangularStateEquiv_apply (n m : ℕ)
    (p : Fin (n + 1) × Fin (m + 1)) :
    rectangularStateEquiv n m p = rectangularState n m p :=
  rfl

private theorem hammingDist_sum {α β : Type*} [Fintype α] [Fintype β]
    (x₁ y₁ : α → Bool) (x₂ y₂ : β → Bool) :
    hammingDist (Sum.elim x₁ x₂) (Sum.elim y₁ y₂) =
      hammingDist x₁ y₁ + hammingDist x₂ y₂ := by
  unfold hammingDist
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- The intrinsic event-wall metric is the Manhattan metric on the recovered
rectangle. -/
theorem rectangularState_distance (n m : ℕ)
    (p q : Fin (n + 1) × Fin (m + 1)) :
    lowerSetDistance (rectangularState n m p) (rectangularState n m q) =
      Nat.dist p.1.val q.1.val + Nat.dist p.2.val q.2.val := by
  have hp : lowerSetCode (rectangularState n m p) =
      Sum.elim (lowerSetCode (chainState n p.1))
        (lowerSetCode (chainState m p.2)) := by
    funext e
    cases e <;> simp [lowerSetCode]
  have hq : lowerSetCode (rectangularState n m q) =
      Sum.elim (lowerSetCode (chainState n q.1))
        (lowerSetCode (chainState m q.2)) := by
    funext e
    cases e <;> simp [lowerSetCode]
  unfold lowerSetDistance
  rw [hp, hq, hammingDist_sum]
  rw [← lowerSetDistance, ← lowerSetDistance]
  rw [chainState_distance, chainState_distance]

private theorem natDist_eq_one_iff_pathGraph_adj (n : ℕ)
    (i j : Fin (n + 1)) :
    Nat.dist i.val j.val = 1 ↔ (SimpleGraph.pathGraph (n + 1)).Adj i j := by
  rw [SimpleGraph.pathGraph_adj]
  unfold Nat.dist
  omega

/-- Adjacency in the causal-state graph is exactly adjacency in the
rectangular box product of paths. -/
theorem rectangularState_adj_iff_boxProd_adj (n m : ℕ)
    (p q : Fin (n + 1) × Fin (m + 1)) :
    (lowerSetTransitionGraph (α := Fin n ⊕ Fin m)).Adj
        (rectangularState n m p) (rectangularState n m q) ↔
      ((SimpleGraph.pathGraph (n + 1)) □
        (SimpleGraph.pathGraph (m + 1))).Adj p q := by
  change lowerSetDistance (rectangularState n m p)
      (rectangularState n m q) = 1 ↔ _
  rw [rectangularState_distance, SimpleGraph.boxProd_adj]
  constructor
  · intro h
    by_cases hx : Nat.dist p.1.val q.1.val = 0
    · right
      constructor
      · apply (natDist_eq_one_iff_pathGraph_adj m p.2 q.2).1
        omega
      · apply Fin.ext
        exact Nat.eq_of_dist_eq_zero hx
    · left
      constructor
      · apply (natDist_eq_one_iff_pathGraph_adj n p.1 q.1).1
        omega
      · apply Fin.ext
        apply Nat.eq_of_dist_eq_zero
        omega
  · rintro (⟨hp, hq⟩ | ⟨hq, hp⟩)
    · have hx := (natDist_eq_one_iff_pathGraph_adj n p.1 q.1).2 hp
      have hy : Nat.dist p.2.val q.2.val = 0 := by
        apply Nat.dist_eq_zero
        exact congrArg Fin.val hq
      omega
    · have hy := (natDist_eq_one_iff_pathGraph_adj m p.2 q.2).2 hq
      have hx : Nat.dist p.1.val q.1.val = 0 := by
        apply Nat.dist_eq_zero
        exact congrArg Fin.val hp
      omega

/-- **CAUSAL RECTANGLE THEOREM.** The complete intrinsic state graph of two
disjoint causal chains is graph-isomorphic to a rectangular grid. -/
def rectangularStateGraphIso (n m : ℕ) :
    (SimpleGraph.pathGraph (n + 1) □ SimpleGraph.pathGraph (m + 1)) ≃g
      lowerSetTransitionGraph (α := Fin n ⊕ Fin m) where
  toEquiv := rectangularStateEquiv n m
  map_rel_iff' := by
    intro p q
    exact rectangularState_adj_iff_boxProd_adj n m p q

/-! ## Laplacian transport and the intrinsic five-point stencil -/

/-- Graph Laplacians are invariant under graph isomorphism when the field is
pulled back along the isomorphism. -/
theorem graphLaplacian_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (φ : W → ℝ) (v : V) :
    graphLaplacian H φ (e v) =
      graphLaplacian G (fun x => φ (e x)) v := by
  unfold graphLaplacian
  calc
    (∑ w ∈ H.neighborFinset (e v), (φ (e v) - φ w)) =
        ∑ w : H.neighborSet (e v), (φ (e v) - φ w.1) := by
          apply Finset.sum_subtype
          intro w
          simp
    _ = ∑ w : G.neighborSet v, (φ (e v) - φ (e w.1)) := by
          symm
          exact Fintype.sum_equiv (e.mapNeighborSet v)
            (fun w : G.neighborSet v => φ (e v) - φ (e w.1))
            (fun w : H.neighborSet (e v) => φ (e v) - φ w.1)
            (fun _ => rfl)
    _ = ∑ w ∈ G.neighborFinset v, (φ (e v) - φ (e w)) := by
          symm
          apply Finset.sum_subtype
          intro w
          simp

/-- The Laplacian of a box product splits into its two coordinate
Laplacians. -/
theorem graphLaplacian_boxProd {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (φ : V × W → ℝ) (p : V × W) :
    graphLaplacian (G □ H) φ p =
      graphLaplacian G (fun x => φ (x, p.2)) p.1 +
        graphLaplacian H (fun y => φ (p.1, y)) p.2 := by
  unfold graphLaplacian
  rw [SimpleGraph.neighborFinset_boxProd]
  simp only [Finset.sum_disjUnion, Finset.sum_product,
    Finset.sum_singleton]

/-- Move one lattice step left in the first causal-chain coordinate. -/
def rectangularLeftX {n m : ℕ} (p : Fin (n + 1) × Fin (m + 1))
    (hp0 : 0 < p.1.val) : Fin (n + 1) × Fin (m + 1) :=
  (chainLeft p.1 hp0, p.2)

/-- Move one lattice step right in the first causal-chain coordinate. -/
def rectangularRightX {n m : ℕ} (p : Fin (n + 1) × Fin (m + 1))
    (hpn : p.1.val < n) : Fin (n + 1) × Fin (m + 1) :=
  (chainRight p.1 hpn, p.2)

/-- Move one lattice step down in the second causal-chain coordinate. -/
def rectangularLeftY {n m : ℕ} (p : Fin (n + 1) × Fin (m + 1))
    (hp0 : 0 < p.2.val) : Fin (n + 1) × Fin (m + 1) :=
  (p.1, chainLeft p.2 hp0)

/-- Move one lattice step up in the second causal-chain coordinate. -/
def rectangularRightY {n m : ℕ} (p : Fin (n + 1) × Fin (m + 1))
    (hpm : p.2.val < m) : Fin (n + 1) × Fin (m + 1) :=
  (p.1, chainRight p.2 hpm)

/-- **INTRINSIC FIVE-POINT THEOREM.** At an interior state of the two-chain
causal family, the CAG state-graph Laplacian is exactly the two-dimensional
five-point stencil. -/
theorem graphLaplacian_rectangularState_interior
    {n m : ℕ} (φ : LowerSet (Fin n ⊕ Fin m) → ℝ)
    (p : Fin (n + 1) × Fin (m + 1))
    (hx0 : 0 < p.1.val) (hxn : p.1.val < n)
    (hy0 : 0 < p.2.val) (hym : p.2.val < m) :
    graphLaplacian (lowerSetTransitionGraph (α := Fin n ⊕ Fin m)) φ
        (rectangularState n m p) =
      4 * φ (rectangularState n m p) -
        φ (rectangularState n m (rectangularLeftX p hx0)) -
        φ (rectangularState n m (rectangularRightX p hxn)) -
        φ (rectangularState n m (rectangularLeftY p hy0)) -
        φ (rectangularState n m (rectangularRightY p hym)) := by
  have hiso := graphLaplacian_iso (rectangularStateGraphIso n m) φ p
  change graphLaplacian (lowerSetTransitionGraph (α := Fin n ⊕ Fin m)) φ
      (rectangularState n m p) =
    graphLaplacian
      (SimpleGraph.pathGraph (n + 1) □ SimpleGraph.pathGraph (m + 1))
      (fun q => φ (rectangularState n m q)) p at hiso
  rw [hiso]
  rw [graphLaplacian_boxProd]
  rw [graphLaplacian_pathGraph_interior _ p.1 hx0 hxn]
  rw [graphLaplacian_pathGraph_interior _ p.2 hy0 hym]
  unfold rectangularLeftX rectangularRightX rectangularLeftY rectangularRightY
  ring

/-! ## Two-dimensional continuum consistency -/

/-- Euclidean coordinate supplied by a common external mesh scale `h`. -/
def rectangularCoordinate {n m : ℕ} (h : ℝ)
    (p : Fin (n + 1) × Fin (m + 1)) : ℝ × ℝ :=
  (chainCoordinate h p.1, chainCoordinate h p.2)

theorem rectangularCoordinate_leftX {n m : ℕ} (h : ℝ)
    (p : Fin (n + 1) × Fin (m + 1)) (hp0 : 0 < p.1.val) :
    rectangularCoordinate h (rectangularLeftX p hp0) =
      ((rectangularCoordinate h p).1 - h, (rectangularCoordinate h p).2) := by
  apply Prod.ext
  · exact chainCoordinate_left h p.1 hp0
  · rfl

theorem rectangularCoordinate_rightX {n m : ℕ} (h : ℝ)
    (p : Fin (n + 1) × Fin (m + 1)) (hpn : p.1.val < n) :
    rectangularCoordinate h (rectangularRightX p hpn) =
      ((rectangularCoordinate h p).1 + h, (rectangularCoordinate h p).2) := by
  apply Prod.ext
  · exact chainCoordinate_right h p.1 hpn
  · rfl

theorem rectangularCoordinate_leftY {n m : ℕ} (h : ℝ)
    (p : Fin (n + 1) × Fin (m + 1)) (hp0 : 0 < p.2.val) :
    rectangularCoordinate h (rectangularLeftY p hp0) =
      ((rectangularCoordinate h p).1, (rectangularCoordinate h p).2 - h) := by
  apply Prod.ext
  · rfl
  · exact chainCoordinate_left h p.2 hp0

theorem rectangularCoordinate_rightY {n m : ℕ} (h : ℝ)
    (p : Fin (n + 1) × Fin (m + 1)) (hpm : p.2.val < m) :
    rectangularCoordinate h (rectangularRightY p hpm) =
      ((rectangularCoordinate h p).1, (rectangularCoordinate h p).2 + h) := by
  apply Prod.ext
  · rfl
  · exact chainCoordinate_right h p.2 hpm

/-- Sample a continuum scalar field on every two-chain causal state. -/
def rectangularSample (n m : ℕ) (h : ℝ) (f : ℝ × ℝ → ℝ) :
    LowerSet (Fin n ⊕ Fin m) → ℝ :=
  fun s => f (rectangularCoordinate h ((rectangularStateEquiv n m).symm s))

@[simp]
theorem rectangularSample_rectangularState (n m : ℕ) (h : ℝ)
    (f : ℝ × ℝ → ℝ) (p : Fin (n + 1) × Fin (m + 1)) :
    rectangularSample n m h f (rectangularState n m p) =
      f (rectangularCoordinate h p) := by
  unfold rectangularSample
  change f (rectangularCoordinate h
    ((rectangularStateEquiv n m).symm (rectangularStateEquiv n m p))) = _
  rw [Equiv.symm_apply_apply]

/-- Exact sampled-field five-point formula before division by mesh area. -/
theorem graphLaplacian_rectangularSample_interior
    (n m : ℕ) (h : ℝ) (f : ℝ × ℝ → ℝ)
    (p : Fin (n + 1) × Fin (m + 1))
    (hx0 : 0 < p.1.val) (hxn : p.1.val < n)
    (hy0 : 0 < p.2.val) (hym : p.2.val < m) :
    graphLaplacian (lowerSetTransitionGraph (α := Fin n ⊕ Fin m))
        (rectangularSample n m h f) (rectangularState n m p) =
      4 * f (rectangularCoordinate h p) -
        f ((rectangularCoordinate h p).1 - h,
          (rectangularCoordinate h p).2) -
        f ((rectangularCoordinate h p).1 + h,
          (rectangularCoordinate h p).2) -
        f ((rectangularCoordinate h p).1,
          (rectangularCoordinate h p).2 - h) -
        f ((rectangularCoordinate h p).1,
          (rectangularCoordinate h p).2 + h) := by
  rw [graphLaplacian_rectangularState_interior
    (rectangularSample n m h f) p hx0 hxn hy0 hym]
  simp only [rectangularSample_rectangularState]
  rw [rectangularCoordinate_leftX h p hx0,
    rectangularCoordinate_rightX h p hxn,
    rectangularCoordinate_leftY h p hy0,
    rectangularCoordinate_rightY h p hym]

/-- Scaled intrinsic CAG Laplacian on the rectangular family. -/
def scaledRectangularLaplacian (n m : ℕ) (h : ℝ)
    (f : ℝ × ℝ → ℝ) (p : Fin (n + 1) × Fin (m + 1)) : ℝ :=
  graphLaplacian (lowerSetTransitionGraph (α := Fin n ⊕ Fin m))
      (rectangularSample n m h f) (rectangularState n m p) / h ^ 2

/-- The scaled intrinsic CAG operator is exactly the negative five-point
finite-difference Laplacian at every interior state. -/
theorem scaledRectangularLaplacian_eq_fivePoint
    (n m : ℕ) (h : ℝ) (f : ℝ × ℝ → ℝ)
    (p : Fin (n + 1) × Fin (m + 1))
    (hx0 : 0 < p.1.val) (hxn : p.1.val < n)
    (hy0 : 0 < p.2.val) (hym : p.2.val < m) :
    scaledRectangularLaplacian n m h f p =
      (4 * f (rectangularCoordinate h p) -
        f ((rectangularCoordinate h p).1 - h,
          (rectangularCoordinate h p).2) -
        f ((rectangularCoordinate h p).1 + h,
          (rectangularCoordinate h p).2) -
        f ((rectangularCoordinate h p).1,
          (rectangularCoordinate h p).2 - h) -
        f ((rectangularCoordinate h p).1,
          (rectangularCoordinate h p).2 + h)) / h ^ 2 := by
  unfold scaledRectangularLaplacian
  rw [graphLaplacian_rectangularSample_interior
    n m h f p hx0 hxn hy0 hym]

/-- Coefficients for a coupled quartic test surface.  This class includes
independent quartic/cubic terms and the mixed terms `x^2 y^2` and `x y`. -/
structure QuarticSurfaceCoefficients where
  x4 : ℝ
  y4 : ℝ
  x2y2 : ℝ
  x3 : ℝ
  y3 : ℝ
  x2 : ℝ
  y2 : ℝ
  xy : ℝ
  x1 : ℝ
  y1 : ℝ
  constant : ℝ

/-- Coupled quartic continuum test field. -/
def quarticSurface (c : QuarticSurfaceCoefficients) (p : ℝ × ℝ) : ℝ :=
  c.x4 * p.1 ^ 4 + c.y4 * p.2 ^ 4 +
    c.x2y2 * p.1 ^ 2 * p.2 ^ 2 +
    c.x3 * p.1 ^ 3 + c.y3 * p.2 ^ 3 +
    c.x2 * p.1 ^ 2 + c.y2 * p.2 ^ 2 +
    c.xy * p.1 * p.2 + c.x1 * p.1 + c.y1 * p.2 + c.constant

/-- Exact Euclidean Laplacian of `quarticSurface`. -/
def quarticSurfaceLaplacian (c : QuarticSurfaceCoefficients)
    (p : ℝ × ℝ) : ℝ :=
  12 * c.x4 * p.1 ^ 2 + 6 * c.x3 * p.1 + 2 * c.x2 +
    2 * c.x2y2 * p.2 ^ 2 +
    (12 * c.y4 * p.2 ^ 2 + 6 * c.y3 * p.2 + 2 * c.y2 +
      2 * c.x2y2 * p.1 ^ 2)

/-- Algebraic consistency identity for the negative five-point operator on
the coupled quartic class. -/
theorem quarticSurface_fivePoint_exact
    (c : QuarticSurfaceCoefficients) (p : ℝ × ℝ) (h : ℝ) (hh : h ≠ 0) :
    (4 * quarticSurface c p -
      quarticSurface c (p.1 - h, p.2) -
      quarticSurface c (p.1 + h, p.2) -
      quarticSurface c (p.1, p.2 - h) -
      quarticSurface c (p.1, p.2 + h)) / h ^ 2 =
        -quarticSurfaceLaplacian c p - 2 * (c.x4 + c.y4) * h ^ 2 := by
  unfold quarticSurface quarticSurfaceLaplacian
  field_simp [hh]
  ring

/-- **TWO-DIMENSIONAL CAG/CONTINUUM ERROR THEOREM.** The scaled intrinsic
CAG operator differs from the negative Euclidean Laplacian by the exact,
uniform truncation term `-2(x4+y4)h^2`. -/
theorem scaledRectangularLaplacian_quartic_exact
    (n m : ℕ) (c : QuarticSurfaceCoefficients) (h : ℝ) (hh : h ≠ 0)
    (p : Fin (n + 1) × Fin (m + 1))
    (hx0 : 0 < p.1.val) (hxn : p.1.val < n)
    (hy0 : 0 < p.2.val) (hym : p.2.val < m) :
    scaledRectangularLaplacian n m h (quarticSurface c) p =
      -quarticSurfaceLaplacian c (rectangularCoordinate h p) -
        2 * (c.x4 + c.y4) * h ^ 2 := by
  rw [scaledRectangularLaplacian_eq_fivePoint
    n m h _ p hx0 hxn hy0 hym]
  exact quarticSurface_fivePoint_exact c (rectangularCoordinate h p) h hh

/-- Uniform absolute error for the two-dimensional CAG scaling family. -/
theorem scaledRectangularLaplacian_quartic_error
    (n m : ℕ) (c : QuarticSurfaceCoefficients) (h : ℝ) (hh : h ≠ 0)
    (p : Fin (n + 1) × Fin (m + 1))
    (hx0 : 0 < p.1.val) (hxn : p.1.val < n)
    (hy0 : 0 < p.2.val) (hym : p.2.val < m) :
    |scaledRectangularLaplacian n m h (quarticSurface c) p +
        quarticSurfaceLaplacian c (rectangularCoordinate h p)| =
      2 * |c.x4 + c.y4| * h ^ 2 := by
  rw [scaledRectangularLaplacian_quartic_exact
    n m c h hh p hx0 hxn hy0 hym]
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  rw [show -quarticSurfaceLaplacian c (rectangularCoordinate h p) -
      2 * (c.x4 + c.y4) * h ^ 2 +
        quarticSurfaceLaplacian c (rectangularCoordinate h p) =
      (-2) * (c.x4 + c.y4) * h ^ 2 by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hh2]
  norm_num

/-- The terminal state of the square `n`-by-`n` causal family lies exactly at
the independently specified continuum corner `(L,L)`. -/
theorem rectangularCoordinate_terminal (L : ℝ) (n : ℕ) (hn : n ≠ 0) :
    rectangularCoordinate (chainMesh L n)
      ((⟨n, Nat.lt_succ_self n⟩, ⟨n, Nat.lt_succ_self n⟩) :
        Fin (n + 1) × Fin (n + 1)) = (L, L) := by
  apply Prod.ext <;> exact chainCoordinate_terminal L n hn

/-- Along fixed physical squares with mesh `L/n`, the certified uniform
two-dimensional consistency error converges to zero. -/
theorem quarticSquareFamily_error_tendsto_zero
    (c : QuarticSurfaceCoefficients) (L : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => 2 * |c.x4 + c.y4| * (chainMesh L n) ^ 2)
      Filter.atTop (nhds 0) := by
  exact (quarticConsistencyError_tendsto_zero (c.x4 + c.y4)).comp
    (chainMesh_tendsto_zero L)

end
end CausalAlgebraicGeometry.CAGTwoDimensionalLimit
