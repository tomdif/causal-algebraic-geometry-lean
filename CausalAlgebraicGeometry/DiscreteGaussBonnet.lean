/-
  DiscreteGaussBonnet.lean — The BD action is a sum of local curvatures.

  THEOREM (Discrete Gauss-Bonnet):
    2 · S_BD(S) = Σ_{x ∈ S} (2 - deg(x, S))

  where deg(x, S) = number of Hasse neighbors of x within S.

  Proof: Handshaking lemma gives Σ deg = 2·|links|.
  So Σ(2 - deg) = 2|S| - 2|links| = 2·S_BD.

  The term κ(x) = 2 - deg(x) is the discrete curvature at x:
  - Corner (deg 2): κ = 0 (flat)
  - Edge (deg 3): κ = -1 (mild negative curvature)
  - Interior (deg 4): κ = -2 (full negative curvature)
  - Isolated (deg 0): κ = +2 (maximal positive curvature)

  The positive energy theorem becomes: among convex subsets, the full
  grid minimizes total curvature (most negative = "flattest").

  Zero sorry.
-/
import CausalAlgebraicGeometry.BDAction
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.DiscreteGaussBonnet

open CausalAlgebraicGeometry.BDAction
open CausalAlgebraicGeometry.GridClassification

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

/-! ## Degree in the Hasse graph -/

/-- The degree of element x in the Hasse graph restricted to S:
    number of elements y ∈ S such that (x,y) or (y,x) is a link. -/
def hasseDeg (m n : ℕ) (S : Finset (Fin m × Fin n)) (x : Fin m × Fin n) : ℕ :=
  (S.filter fun y =>
    (x.1 = y.1 ∧ x.2.val + 1 = y.2.val) ∨  -- x → y horizontal
    (x.1 = y.1 ∧ y.2.val + 1 = x.2.val) ∨  -- y → x horizontal
    (x.1.val + 1 = y.1.val ∧ x.2 = y.2) ∨  -- x → y vertical
    (y.1.val + 1 = x.1.val ∧ x.2 = y.2)    -- y → x vertical
  ).card

/-- The discrete curvature at x: κ(x) = 2 - deg(x). -/
def discreteCurvature (m n : ℕ) (S : Finset (Fin m × Fin n)) (x : Fin m × Fin n) : Int :=
  2 - (hasseDeg m n S x : Int)

/-- The total curvature: Σ_{x ∈ S} κ(x). -/
def totalCurvature (m n : ℕ) (S : Finset (Fin m × Fin n)) : Int :=
  S.sum fun x => discreteCurvature m n S x

/-! ## The handshaking lemma -/

-- Step 1: Sum of hasseDeg = card of adjacency-filtered product
private lemma sum_hasseDeg_eq (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    S.sum (hasseDeg m n S) =
    ((S ×ˢ S).filter fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
      (p.1.1 = p.2.1 ∧ p.1.2.val + 1 = p.2.2.val) ∨
      (p.1.1 = p.2.1 ∧ p.2.2.val + 1 = p.1.2.val) ∨
      (p.1.1.val + 1 = p.2.1.val ∧ p.1.2 = p.2.2) ∨
      (p.2.1.val + 1 = p.1.1.val ∧ p.1.2 = p.2.2)).card := by
  unfold hasseDeg
  simp_rw [Finset.card_filter, ← Finset.sum_product']

-- The 4 directional pair sets (right/left horizontal, down/up vertical)
private def dirHR (m n : ℕ) (S : Finset (Fin m × Fin n)) :=
  (S ×ˢ S).filter fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
    p.1.1 = p.2.1 ∧ p.1.2.val + 1 = p.2.2.val

private def dirHL (m n : ℕ) (S : Finset (Fin m × Fin n)) :=
  (S ×ˢ S).filter fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
    p.1.1 = p.2.1 ∧ p.2.2.val + 1 = p.1.2.val

private def dirVD (m n : ℕ) (S : Finset (Fin m × Fin n)) :=
  (S ×ˢ S).filter fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
    p.1.1.val + 1 = p.2.1.val ∧ p.1.2 = p.2.2

private def dirVU (m n : ℕ) (S : Finset (Fin m × Fin n)) :=
  (S ×ˢ S).filter fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
    p.2.1.val + 1 = p.1.1.val ∧ p.1.2 = p.2.2

-- dirHR and dirVD are definitionally equal to hLinks and vLinks
private lemma dirHR_eq_hLinks (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    dirHR m n S = hLinks m n S := by unfold dirHR hLinks; rfl

private lemma dirVD_eq_vLinks (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    dirVD m n S = vLinks m n S := by unfold dirVD vLinks; rfl

-- dirHL bijects with hLinks via swap (reverse links have same count)
private lemma card_dirHL_eq_hLinks (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    (dirHL m n S).card = (hLinks m n S).card := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    unfold dirHL at hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    unfold hLinks
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hp.1.2, hp.1.1⟩, hp.2.1.symm, hp.2.2⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro p hp
    unfold hLinks at hp
    simp only [Finset.mem_filter] at hp
    have hmem := Finset.mem_product.mp hp.1
    refine ⟨(p.2, p.1), ?_, by simp⟩
    unfold dirHL
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hmem.2, hmem.1⟩, hp.2.1.symm, hp.2.2⟩

-- dirVU bijects with vLinks via swap
private lemma card_dirVU_eq_vLinks (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    (dirVU m n S).card = (vLinks m n S).card := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    unfold dirVU at hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    unfold vLinks
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hp.1.2, hp.1.1⟩, hp.2.1, hp.2.2.symm⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro p hp
    unfold vLinks at hp
    simp only [Finset.mem_filter] at hp
    have hmem := Finset.mem_product.mp hp.1
    refine ⟨(p.2, p.1), ?_, by simp⟩
    unfold dirVU
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hmem.2, hmem.1⟩, hp.2.1, hp.2.2.symm⟩

-- The adjacency filter = disjoint union of 4 directional sets
private lemma adj_eq_union (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    ((S ×ˢ S).filter fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
      (p.1.1 = p.2.1 ∧ p.1.2.val + 1 = p.2.2.val) ∨
      (p.1.1 = p.2.1 ∧ p.2.2.val + 1 = p.1.2.val) ∨
      (p.1.1.val + 1 = p.2.1.val ∧ p.1.2 = p.2.2) ∨
      (p.2.1.val + 1 = p.1.1.val ∧ p.1.2 = p.2.2)) =
    dirHR m n S ∪ dirHL m n S ∪ dirVD m n S ∪ dirVU m n S := by
  simp only [dirHR, dirHL, dirVD, dirVU]
  ext p; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product]; tauto

-- Pairwise disjointness of the 4 directional sets
-- HR vs HL: x.2+1=y.2 and y.2+1=x.2 is impossible
private lemma disjoint_HR_HL (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Disjoint (dirHR m n S) (dirHL m n S) := by
  simp only [dirHR, dirHL, Finset.disjoint_filter]
  intro p _ h1 h2; exact absurd h1.2 (by omega)

-- HR vs VD: x.1=y.1 and x.1+1=y.1 is impossible
private lemma disjoint_HR_VD (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Disjoint (dirHR m n S) (dirVD m n S) := by
  simp only [dirHR, dirVD, Finset.disjoint_filter]
  intro p _ h1 h2; exact absurd (congr_arg Fin.val h1.1 ▸ h2.1) (by omega)

private lemma disjoint_HR_VU (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Disjoint (dirHR m n S) (dirVU m n S) := by
  simp only [dirHR, dirVU, Finset.disjoint_filter]
  intro p _ h1 h2; exact absurd (congr_arg Fin.val h1.1 ▸ h2.1) (by omega)

private lemma disjoint_HL_VD (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Disjoint (dirHL m n S) (dirVD m n S) := by
  simp only [dirHL, dirVD, Finset.disjoint_filter]
  intro p _ h1 h2; exact absurd (congr_arg Fin.val h1.1 ▸ h2.1) (by omega)

private lemma disjoint_HL_VU (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Disjoint (dirHL m n S) (dirVU m n S) := by
  simp only [dirHL, dirVU, Finset.disjoint_filter]
  intro p _ h1 h2; exact absurd (congr_arg Fin.val h1.1 ▸ h2.1) (by omega)

-- VD vs VU: x.1+1=y.1 and y.1+1=x.1 is impossible
private lemma disjoint_VD_VU (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Disjoint (dirVD m n S) (dirVU m n S) := by
  simp only [dirVD, dirVU, Finset.disjoint_filter]
  intro p _ h1 h2; exact absurd h1.1 (by omega)

/-- The sum of degrees = 2 · numLinks (handshaking lemma for the Hasse graph).
    Each directed link (x,y) contributes 1 to deg(x) and 1 to deg(y). -/
theorem handshaking (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    S.sum (hasseDeg m n S) = 2 * numLinks m n S := by
  rw [sum_hasseDeg_eq, adj_eq_union, numLinks]
  have d1 := disjoint_HR_HL m n S
  have d2 := disjoint_HR_VD m n S
  have d3 := disjoint_HR_VU m n S
  have d4 := disjoint_HL_VD m n S
  have d5 := disjoint_HL_VU m n S
  have d6 := disjoint_VD_VU m n S
  rw [Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d3, d5⟩, d6⟩),
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d2, d4⟩),
      Finset.card_union_of_disjoint d1,
      dirHR_eq_hLinks, dirVD_eq_vLinks, card_dirHL_eq_hLinks, card_dirVU_eq_vLinks]
  ring

-- Kernel verification of handshaking for [3]²
theorem handshaking_3 :
    (fullGrid 3 3).sum (hasseDeg 3 3 (fullGrid 3 3)) = 2 * numLinks 3 3 (fullGrid 3 3) := by
  native_decide

/-! ## The discrete Gauss-Bonnet theorem -/

/-- **Discrete Gauss-Bonnet**: totalCurvature(S) = 2 · S_BD(S).
    Equivalently: Σ(2 - deg) = 2(|S| - |links|). -/
theorem gauss_bonnet (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    totalCurvature m n S = 2 * bdAction m n S := by
  unfold totalCurvature discreteCurvature bdAction
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have h := handshaking m n S
  unfold numLinks at h ⊢
  have key : ∑ x ∈ S, (hasseDeg m n S x : ℤ) = ↑(S.sum (hasseDeg m n S)) := by
    rw [Nat.cast_sum]
  rw [key, h]
  push_cast
  ring

-- Kernel verification for [2]² and [3]²
theorem gauss_bonnet_2 :
    totalCurvature 2 2 (fullGrid 2 2) = 2 * bdAction 2 2 (fullGrid 2 2) := by native_decide

theorem gauss_bonnet_3 :
    totalCurvature 3 3 (fullGrid 3 3) = 2 * bdAction 3 3 (fullGrid 3 3) := by native_decide

/-! ## Curvature of the full grid -/

-- Verify the curvature map on [3]²:
-- Corners (deg 2): κ = 0
-- Edges (deg 3): κ = -1
-- Interior (deg 4): κ = -2

theorem corner_curvature_3 : discreteCurvature 3 3 (fullGrid 3 3) (0, 0) = 0 := by native_decide
theorem edge_curvature_3 : discreteCurvature 3 3 (fullGrid 3 3) (0, 1) = -1 := by native_decide
theorem interior_curvature_3 : discreteCurvature 3 3 (fullGrid 3 3) (1, 1) = -2 := by native_decide

/-- Total curvature of flat [3]² = -6 = 2 × (-3) = 2 × S_BD. -/
theorem total_curvature_3 : totalCurvature 3 3 (fullGrid 3 3) = -6 := by native_decide

/-! ## Connection to positive energy

  The positive energy theorem (bd_action_ge) says:
    S_BD(S) ≥ -(m-1)(n-1) + 1

  Via Gauss-Bonnet, this becomes:
    Σ_{x ∈ S} κ(x) ≥ 2·(-(m-1)(n-1) + 1)

  Interpretation: among all convex subsets, the full grid has the
  MOST NEGATIVE total curvature. Removing elements from the full
  grid increases the total curvature (adds positive curvature defects).

  This is exactly the discrete analogue of:
    ∫_M R √g dA ≥ ∫_{flat} R √g dA = 2πχ (Gauss-Bonnet)

  where flat space achieves the minimum integrated curvature.
-/

end CausalAlgebraicGeometry.DiscreteGaussBonnet
