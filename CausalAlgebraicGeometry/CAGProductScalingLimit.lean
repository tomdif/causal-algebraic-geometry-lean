/-
  CAGProductScalingLimit.lean — Arbitrary-dimensional product scaling for CAG.

  A family of `d` mutually independent causal chains is built recursively as
  a disjoint sum.  Its downset-state graph is proved graph-isomorphic to the
  `d`-fold box product of a finite path.  Thus the dimension, grid coordinates,
  Manhattan geometry, and `2d` nearest-neighbor directions all arise from the
  causal order.

  At every fully interior state, the intrinsic CAG graph Laplacian is proved
  equal to the recursively defined `(2d+1)`-point stencil.  A separable
  arbitrary-dimensional quartic class then gives an exact uniform O(h^2)
  comparison with the negative Euclidean Laplacian.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGPlaquetteLimit

namespace CausalAlgebraicGeometry.CAGProductScalingLimit

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGFiniteCausalDynamics
open CausalAlgebraicGeometry.CAGScalingLimit
open CausalAlgebraicGeometry.CAGTwoDimensionalLimit

noncomputable section
open scoped Classical

/-! ## Generic disjoint-sum state geometry -/

private theorem hammingDist_sum {α β : Type*} [Fintype α] [Fintype β]
    (x₁ y₁ : α → Bool) (x₂ y₂ : β → Bool) :
    hammingDist (Sum.elim x₁ x₂) (Sum.elim y₁ y₂) =
      hammingDist x₁ y₁ + hammingDist x₂ y₂ := by
  unfold hammingDist
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Event-wall distance splits additively over causally disconnected
components. -/
theorem lowerSetDistance_sumLowerSet
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    [Fintype α] [Fintype β]
    (s s' : LowerSet α) (t t' : LowerSet β) :
    lowerSetDistance (sumLowerSet s t) (sumLowerSet s' t') =
      lowerSetDistance s s' + lowerSetDistance t t' := by
  have hs : lowerSetCode (sumLowerSet s t) =
      Sum.elim (lowerSetCode s) (lowerSetCode t) := by
    funext e
    cases e <;> simp [lowerSetCode]
  have ht : lowerSetCode (sumLowerSet s' t') =
      Sum.elim (lowerSetCode s') (lowerSetCode t') := by
    funext e
    cases e <;> simp [lowerSetCode]
  unfold lowerSetDistance
  rw [hs, ht, hammingDist_sum]

/-- A one-event state transition in a disjoint causal sum occurs in exactly
one component. -/
theorem sumLowerSet_adj_iff_boxProd_adj
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    [Fintype α] [Fintype β]
    (s s' : LowerSet α) (t t' : LowerSet β) :
    (lowerSetTransitionGraph (α := α ⊕ β)).Adj
        (sumLowerSet s t) (sumLowerSet s' t') ↔
      (lowerSetTransitionGraph (α := α) □
        lowerSetTransitionGraph (α := β)).Adj (s, t) (s', t') := by
  change lowerSetDistance (sumLowerSet s t) (sumLowerSet s' t') = 1 ↔ _
  rw [lowerSetDistance_sumLowerSet, SimpleGraph.boxProd_adj]
  constructor
  · intro h
    by_cases hs0 : lowerSetDistance s s' = 0
    · right
      constructor
      · change lowerSetDistance t t' = 1
        omega
      · exact (lowerSetDistance_eq_zero_iff s s').mp hs0
    · left
      have ht0 : lowerSetDistance t t' = 0 := by omega
      constructor
      · change lowerSetDistance s s' = 1
        omega
      · exact (lowerSetDistance_eq_zero_iff t t').mp ht0
  · rintro (⟨hs, rfl⟩ | ⟨ht, rfl⟩)
    · change lowerSetDistance s s' = 1 at hs
      simpa using hs
    · change lowerSetDistance t t' = 1 at ht
      simpa using ht

/-- The downset graph of a disjoint sum is the box product of the component
downset graphs. -/
def sumLowerSetGraphIso
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    [Fintype α] [Fintype β] :
    (lowerSetTransitionGraph (α := α) □
      lowerSetTransitionGraph (α := β)) ≃g
        lowerSetTransitionGraph (α := α ⊕ β) where
  toEquiv := sumLowerSetEquiv
  map_rel_iff' := by
    intro p q
    exact sumLowerSet_adj_iff_boxProd_adj p.1 q.1 p.2 q.2

/-- Box products preserve graph isomorphisms in both factors. -/
def graphIsoBoxCongr
    {V W V' W' : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    {G' : SimpleGraph V'} {H' : SimpleGraph W'}
    (e : G ≃g G') (f : H ≃g H') :
    (G □ H) ≃g (G' □ H') where
  toEquiv := Equiv.prodCongr e.toEquiv f.toEquiv
  map_rel_iff' := by
    intro p q
    change (G'.Adj (e p.1) (e q.1) ∧ f p.2 = f q.2 ∨
      H'.Adj (f p.2) (f q.2) ∧ e p.1 = e q.1) ↔ _
    rw [e.map_adj_iff, f.map_adj_iff]
    simp

/-! ## Arbitrarily many independent causal chains -/

/-- Event poset consisting of `d` independent chains, each with `n` events. -/
def IndependentChains : ℕ → ℕ → Type
  | 0, _ => Empty
  | d + 1, n => Fin n ⊕ IndependentChains d n

instance instFintypeIndependentChains (d n : ℕ) :
    Fintype (IndependentChains d n) := by
  induction d with
  | zero =>
      change Fintype Empty
      infer_instance
  | succ d ih =>
      change Fintype (Fin n ⊕ IndependentChains d n)
      infer_instance

instance instPartialOrderIndependentChains (d n : ℕ) :
    PartialOrder (IndependentChains d n) := by
  induction d with
  | zero =>
      change PartialOrder Empty
      infer_instance
  | succ d ih =>
      change PartialOrder (Fin n ⊕ IndependentChains d n)
      infer_instance

instance instDecidableEqIndependentChains (d n : ℕ) :
    DecidableEq (IndependentChains d n) := by
  induction d with
  | zero =>
      change DecidableEq Empty
      infer_instance
  | succ d ih =>
      change DecidableEq (Fin n ⊕ IndependentChains d n)
      infer_instance

/-- Recursive coordinate type for a `d`-dimensional grid with `n+1` states
on every axis. -/
def ProductIndex : ℕ → ℕ → Type
  | 0, _ => PUnit
  | d + 1, n => Fin (n + 1) × ProductIndex d n

instance instFintypeProductIndex (d n : ℕ) : Fintype (ProductIndex d n) := by
  induction d with
  | zero =>
      change Fintype PUnit
      infer_instance
  | succ d ih =>
      change Fintype (Fin (n + 1) × ProductIndex d n)
      infer_instance

instance instDecidableEqProductIndex (d n : ℕ) :
    DecidableEq (ProductIndex d n) := by
  induction d with
  | zero =>
      change DecidableEq PUnit
      infer_instance
  | succ d ih =>
      change DecidableEq (Fin (n + 1) × ProductIndex d n)
      infer_instance

/-- Recursive `d`-fold box product of the path graph on `n+1` states. -/
def productGridGraph : (d n : ℕ) → SimpleGraph (ProductIndex d n)
  | 0, _ => ⊥
  | d + 1, n => SimpleGraph.pathGraph (n + 1) □ productGridGraph d n

/-- The empty causal event type has exactly one downset. -/
def emptyLowerSetEquiv : PUnit ≃ LowerSet Empty where
  toFun _ := ⊥
  invFun _ := ⟨⟩
  left_inv x := by cases x; rfl
  right_inv s := by
    apply LowerSet.ext
    ext e
    exact e.elim

/-- The zero-dimensional singleton graph is the downset graph of the empty
event poset. -/
def emptyStateGraphIso :
    (⊥ : SimpleGraph PUnit) ≃g lowerSetTransitionGraph (α := Empty) where
  toEquiv := emptyLowerSetEquiv
  map_rel_iff' := by
    intro u v
    have huv : u = v := Subsingleton.elim _ _
    subst v
    simp

/-- **ARBITRARY-DIMENSIONAL PRODUCT-GRID THEOREM.** The complete CAG state
graph of `d` independent `n`-event chains is the `d`-fold box product of the
path graph on `n+1` vertices. -/
def productStateGraphIso : (d n : ℕ) →
    productGridGraph d n ≃g
      lowerSetTransitionGraph (α := IndependentChains d n)
  | 0, _ => emptyStateGraphIso
  | d + 1, n =>
      (graphIsoBoxCongr (chainStateGraphIso n) (productStateGraphIso d n)).trans
        sumLowerSetGraphIso

/-- Coordinate equivalence underlying `productStateGraphIso`. -/
def productStateEquiv (d n : ℕ) :
    ProductIndex d n ≃ LowerSet (IndependentChains d n) :=
  (productStateGraphIso d n).toEquiv

/-- Causal state with the specified realized-event count on every axis. -/
def productState (d n : ℕ) (k : ProductIndex d n) :
    LowerSet (IndependentChains d n) :=
  productStateEquiv d n k

@[simp]
theorem productStateGraphIso_apply (d n : ℕ) (k : ProductIndex d n) :
    productStateGraphIso d n k = productState d n k :=
  rfl

/-- Recursive Manhattan distance on product coordinates. -/
def productManhattanDistance : {d n : ℕ} →
    ProductIndex d n → ProductIndex d n → ℕ
  | 0, _, _, _ => 0
  | _ + 1, _, k, l =>
      Nat.dist k.1.val l.1.val + productManhattanDistance k.2 l.2

/-- The intrinsic event-wall distance on `d` independent chains is exactly
the `d`-dimensional Manhattan distance. -/
theorem productState_distance (d n : ℕ) (k l : ProductIndex d n) :
    lowerSetDistance (productState d n k) (productState d n l) =
      productManhattanDistance k l := by
  induction d with
  | zero =>
      cases k
      cases l
      simp [productState, productManhattanDistance]
  | succ d ih =>
      change lowerSetDistance
          (sumLowerSet (chainState n k.1) (productState d n k.2))
          (sumLowerSet (chainState n l.1) (productState d n l.2)) =
        Nat.dist k.1.val l.1.val + productManhattanDistance k.2 l.2
      rw [lowerSetDistance_sumLowerSet, chainState_distance, ih]

/-! ## Interior coordinates and the `(2d+1)`-point stencil -/

/-- A coordinate strictly inside a finite path. -/
abbrev InteriorCoordinate (n : ℕ) :=
  {k : Fin (n + 1) // 0 < k.val ∧ k.val < n}

/-- Recursive coordinates for fully interior points of the product grid. -/
def ProductInteriorIndex : ℕ → ℕ → Type
  | 0, _ => PUnit
  | d + 1, n => InteriorCoordinate n × ProductInteriorIndex d n

/-- Forget that every coordinate is interior. -/
def interiorToProductIndex : {d n : ℕ} →
    ProductInteriorIndex d n → ProductIndex d n
  | 0, _, _ => ⟨⟩
  | _ + 1, _, q => (q.1.1, interiorToProductIndex q.2)

/-- Recursive form of the usual `(2d+1)`-point negative-Laplacian stencil. -/
def productStencil : {d n : ℕ} →
    (ProductIndex d n → ℝ) → ProductInteriorIndex d n → ℝ
  | 0, _, _, _ => 0
  | _ + 1, _, φ, q =>
      2 * φ (q.1.1, interiorToProductIndex q.2) -
        φ (chainLeft q.1.1 q.1.2.1, interiorToProductIndex q.2) -
        φ (chainRight q.1.1 q.1.2.2, interiorToProductIndex q.2) +
        productStencil (fun tail => φ (q.1.1, tail)) q.2

/-- The recursive product stencil annihilates every constant field. -/
@[simp]
theorem productStencil_const (d n : ℕ) (c : ℝ)
    (q : ProductInteriorIndex d n) :
    productStencil (fun _ : ProductIndex d n => c) q = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change 2 * c - c - c +
        productStencil (fun _ : ProductIndex d n => c) q.2 = 0
      rw [ih]
      ring

/-- Adding a constant to a field does not change its product stencil. -/
theorem productStencil_add_const (d n : ℕ) (c : ℝ)
    (φ : ProductIndex d n → ℝ) (q : ProductInteriorIndex d n) :
    productStencil (fun k => c + φ k) q = productStencil φ q := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change
        2 * (c + φ (q.1.1, interiorToProductIndex q.2)) -
          (c + φ (chainLeft q.1.1 q.1.2.1,
            interiorToProductIndex q.2)) -
          (c + φ (chainRight q.1.1 q.1.2.2,
            interiorToProductIndex q.2)) +
          productStencil (fun tail => c + φ (q.1.1, tail)) q.2 =
        2 * φ (q.1.1, interiorToProductIndex q.2) -
          φ (chainLeft q.1.1 q.1.2.1,
            interiorToProductIndex q.2) -
          φ (chainRight q.1.1 q.1.2.2,
            interiorToProductIndex q.2) +
          productStencil (fun tail => φ (q.1.1, tail)) q.2
      rw [ih]
      ring

/-- The graph Laplacian of the `d`-fold path product is exactly the recursive
`(2d+1)`-point stencil at every fully interior coordinate. -/
theorem graphLaplacian_productGrid_interior
    (d n : ℕ) (φ : ProductIndex d n → ℝ)
    (q : ProductInteriorIndex d n) :
    graphLaplacian (productGridGraph d n) φ
        (interiorToProductIndex q) = productStencil φ q := by
  induction d with
  | zero =>
      cases q
      change graphLaplacian (⊥ : SimpleGraph PUnit) φ ⟨⟩ = 0
      unfold graphLaplacian
      simp
  | succ d ih =>
      change graphLaplacian
          (SimpleGraph.pathGraph (n + 1) □ productGridGraph d n) φ
          (q.1.1, interiorToProductIndex q.2) =
        2 * φ (q.1.1, interiorToProductIndex q.2) -
          φ (chainLeft q.1.1 q.1.2.1, interiorToProductIndex q.2) -
          φ (chainRight q.1.1 q.1.2.2, interiorToProductIndex q.2) +
          productStencil (fun tail => φ (q.1.1, tail)) q.2
      rw [graphLaplacian_boxProd]
      rw [graphLaplacian_pathGraph_interior _ q.1.1 q.1.2.1 q.1.2.2]
      rw [ih]

/-- **INTRINSIC ARBITRARY-DIMENSIONAL STENCIL THEOREM.** On `d` independent
causal chains, the CAG state-graph Laplacian is exactly the `(2d+1)`-point
product stencil. -/
theorem graphLaplacian_productState_interior
    (d n : ℕ) (φ : LowerSet (IndependentChains d n) → ℝ)
    (q : ProductInteriorIndex d n) :
    graphLaplacian
        (lowerSetTransitionGraph (α := IndependentChains d n)) φ
        (productState d n (interiorToProductIndex q)) =
      productStencil (fun k => φ (productState d n k)) q := by
  have hiso := graphLaplacian_iso (productStateGraphIso d n) φ
    (interiorToProductIndex q)
  change graphLaplacian
      (lowerSetTransitionGraph (α := IndependentChains d n)) φ
      (productState d n (interiorToProductIndex q)) =
    graphLaplacian (productGridGraph d n)
      (fun k => φ (productState d n k)) (interiorToProductIndex q) at hiso
  rw [hiso, graphLaplacian_productGrid_interior]

/-! ## Arbitrary-dimensional continuum consistency -/

/-- Recursive coordinate model of Euclidean `d`-space. -/
def EuclideanPoint : ℕ → Type
  | 0 => PUnit
  | d + 1 => ℝ × EuclideanPoint d

/-- Assign common external mesh spacing `h` to every causal-chain axis. -/
def productCoordinate : {d n : ℕ} →
    ℝ → ProductIndex d n → EuclideanPoint d
  | 0, _, _, _ => ⟨⟩
  | _ + 1, _, h, k =>
      (chainCoordinate h k.1, productCoordinate h k.2)

/-- Sum the components of a recursive Euclidean vector. -/
def euclideanCoordinateSum : {d : ℕ} → EuclideanPoint d → ℝ
  | 0, _ => 0
  | _ + 1, x => x.1 + euclideanCoordinateSum x.2

/-- Sum of independent quartic polynomials, one on each Euclidean axis. -/
def separableQuartic : {d : ℕ} →
    EuclideanPoint d → EuclideanPoint d → EuclideanPoint d →
      EuclideanPoint d → EuclideanPoint d → EuclideanPoint d → ℝ
  | 0, _, _, _, _, _, _ => 0
  | _ + 1, A, B, C, D, E, x =>
      quarticField A.1 B.1 C.1 D.1 E.1 x.1 +
        separableQuartic A.2 B.2 C.2 D.2 E.2 x.2

/-- Euclidean Laplacian of `separableQuartic`. -/
def separableQuarticLaplacian : {d : ℕ} →
    EuclideanPoint d → EuclideanPoint d → EuclideanPoint d →
      EuclideanPoint d → ℝ
  | 0, _, _, _, _ => 0
  | _ + 1, A, B, C, x =>
      quarticSecondDerivative A.1 B.1 C.1 x.1 +
        separableQuarticLaplacian A.2 B.2 C.2 x.2

/-- Exact arbitrary-dimensional consistency formula for the product stencil
on separable quartic fields.  Each axis contributes its one-dimensional
quadratic truncation term. -/
theorem productStencil_separableQuartic_exact
    (d n : ℕ) (A B C D E : EuclideanPoint d)
    (h : ℝ) (hh : h ≠ 0) (q : ProductInteriorIndex d n) :
    productStencil
        (fun k => separableQuartic A B C D E (productCoordinate h k)) q /
          h ^ 2 =
      -separableQuarticLaplacian A B C
          (productCoordinate h (interiorToProductIndex q)) -
        2 * euclideanCoordinateSum A * h ^ 2 := by
  induction d with
  | zero =>
      simp [productStencil, separableQuarticLaplacian,
        euclideanCoordinateSum]
  | succ d ih =>
      change
        (2 * (quarticField A.1 B.1 C.1 D.1 E.1
                (chainCoordinate h q.1.1) +
              separableQuartic A.2 B.2 C.2 D.2 E.2
                (productCoordinate h (interiorToProductIndex q.2))) -
          (quarticField A.1 B.1 C.1 D.1 E.1
                (chainCoordinate h (chainLeft q.1.1 q.1.2.1)) +
              separableQuartic A.2 B.2 C.2 D.2 E.2
                (productCoordinate h (interiorToProductIndex q.2))) -
          (quarticField A.1 B.1 C.1 D.1 E.1
                (chainCoordinate h (chainRight q.1.1 q.1.2.2)) +
              separableQuartic A.2 B.2 C.2 D.2 E.2
                (productCoordinate h (interiorToProductIndex q.2))) +
          productStencil
            (fun tail =>
              quarticField A.1 B.1 C.1 D.1 E.1
                  (chainCoordinate h q.1.1) +
                separableQuartic A.2 B.2 C.2 D.2 E.2
                  (productCoordinate h tail)) q.2) / h ^ 2 =
        -(quarticSecondDerivative A.1 B.1 C.1
              (chainCoordinate h q.1.1) +
            separableQuarticLaplacian A.2 B.2 C.2
              (productCoordinate h (interiorToProductIndex q.2))) -
          2 * (A.1 + euclideanCoordinateSum A.2) * h ^ 2
      rw [chainCoordinate_left h q.1.1 q.1.2.1,
        chainCoordinate_right h q.1.1 q.1.2.2]
      rw [productStencil_add_const]
      have hhead := quartic_centeredDifference_exact
        A.1 B.1 C.1 D.1 E.1 (chainCoordinate h q.1.1) h hh
      have htail := ih A.2 B.2 C.2 D.2 E.2 q.2
      rw [add_div]
      rw [show
        2 * (quarticField A.1 B.1 C.1 D.1 E.1
              (chainCoordinate h q.1.1) +
            separableQuartic A.2 B.2 C.2 D.2 E.2
              (productCoordinate h (interiorToProductIndex q.2))) -
          (quarticField A.1 B.1 C.1 D.1 E.1
              (chainCoordinate h q.1.1 - h) +
            separableQuartic A.2 B.2 C.2 D.2 E.2
              (productCoordinate h (interiorToProductIndex q.2))) -
          (quarticField A.1 B.1 C.1 D.1 E.1
              (chainCoordinate h q.1.1 + h) +
            separableQuartic A.2 B.2 C.2 D.2 E.2
              (productCoordinate h (interiorToProductIndex q.2))) =
        2 * quarticField A.1 B.1 C.1 D.1 E.1
              (chainCoordinate h q.1.1) -
          quarticField A.1 B.1 C.1 D.1 E.1
              (chainCoordinate h q.1.1 - h) -
          quarticField A.1 B.1 C.1 D.1 E.1
              (chainCoordinate h q.1.1 + h) by ring]
      rw [hhead, htail]
      ring

/-- Sample a continuum field on every state of the product causal family. -/
def productSample (d n : ℕ) (h : ℝ) (f : EuclideanPoint d → ℝ) :
    LowerSet (IndependentChains d n) → ℝ :=
  fun s => f (productCoordinate h ((productStateEquiv d n).symm s))

@[simp]
theorem productSample_productState (d n : ℕ) (h : ℝ)
    (f : EuclideanPoint d → ℝ) (k : ProductIndex d n) :
    productSample d n h f (productState d n k) = f (productCoordinate h k) := by
  unfold productSample productState
  rw [Equiv.symm_apply_apply]

/-- Mesh-scaled intrinsic CAG Laplacian for `d` independent causal chains. -/
def scaledProductLaplacian (d n : ℕ) (h : ℝ)
    (f : EuclideanPoint d → ℝ) (k : ProductIndex d n) : ℝ :=
  graphLaplacian
      (lowerSetTransitionGraph (α := IndependentChains d n))
      (productSample d n h f) (productState d n k) / h ^ 2

/-- **ARBITRARY-DIMENSIONAL CAG/CONTINUUM THEOREM.** For every dimension,
chain length, and fully interior state, the scaled intrinsic CAG Laplacian on
a separable quartic differs from the negative Euclidean Laplacian by exactly
`-2 h²` times the sum of the quartic leading coefficients. -/
theorem scaledProductLaplacian_separableQuartic_exact
    (d n : ℕ) (A B C D E : EuclideanPoint d)
    (h : ℝ) (hh : h ≠ 0) (q : ProductInteriorIndex d n) :
    scaledProductLaplacian d n h (separableQuartic A B C D E)
        (interiorToProductIndex q) =
      -separableQuarticLaplacian A B C
          (productCoordinate h (interiorToProductIndex q)) -
        2 * euclideanCoordinateSum A * h ^ 2 := by
  unfold scaledProductLaplacian
  rw [graphLaplacian_productState_interior]
  simp only [productSample_productState]
  exact productStencil_separableQuartic_exact d n A B C D E h hh q

/-- Uniform absolute error in every dimension and at every interior state. -/
theorem scaledProductLaplacian_separableQuartic_error
    (d n : ℕ) (A B C D E : EuclideanPoint d)
    (h : ℝ) (hh : h ≠ 0) (q : ProductInteriorIndex d n) :
    |scaledProductLaplacian d n h (separableQuartic A B C D E)
          (interiorToProductIndex q) +
        separableQuarticLaplacian A B C
          (productCoordinate h (interiorToProductIndex q))| =
      2 * |euclideanCoordinateSum A| * h ^ 2 := by
  rw [scaledProductLaplacian_separableQuartic_exact
    d n A B C D E h hh q]
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  rw [show
    -separableQuarticLaplacian A B C
          (productCoordinate h (interiorToProductIndex q)) -
        2 * euclideanCoordinateSum A * h ^ 2 +
      separableQuarticLaplacian A B C
          (productCoordinate h (interiorToProductIndex q)) =
        (-2) * euclideanCoordinateSum A * h ^ 2 by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hh2]
  norm_num

/-- Coordinate vector with the same scalar in every Euclidean component. -/
def constantEuclideanPoint : (d : ℕ) → ℝ → EuclideanPoint d
  | 0, _ => ⟨⟩
  | d + 1, x => (x, constantEuclideanPoint d x)

/-- Terminal grid coordinate on every causal-chain axis. -/
def terminalProductIndex : (d n : ℕ) → ProductIndex d n
  | 0, _ => ⟨⟩
  | d + 1, n =>
      (⟨n, Nat.lt_succ_self n⟩, terminalProductIndex d n)

/-- For a nonzero chain length, the terminal product state lies exactly at
the externally specified corner `(L,...,L)`. -/
theorem productCoordinate_terminal (d n : ℕ) (L : ℝ) (hn : n ≠ 0) :
    productCoordinate (chainMesh L n) (terminalProductIndex d n) =
      constantEuclideanPoint d L := by
  induction d with
  | zero => rfl
  | succ d ih =>
      apply Prod.ext
      · exact chainCoordinate_terminal L n hn
      · exact ih

/-- Along fixed physical `d`-cubes with mesh `L/n`, the certified uniform
arbitrary-dimensional consistency error converges to zero. -/
theorem productFamily_error_tendsto_zero
    (d : ℕ) (A : EuclideanPoint d) (L : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        2 * |euclideanCoordinateSum A| * (chainMesh L n) ^ 2)
      Filter.atTop (nhds 0) := by
  exact (quarticConsistencyError_tendsto_zero
    (euclideanCoordinateSum A)).comp (chainMesh_tendsto_zero L)

end
end CausalAlgebraicGeometry.CAGProductScalingLimit
