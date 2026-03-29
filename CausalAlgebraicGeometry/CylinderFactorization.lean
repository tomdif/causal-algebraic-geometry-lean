/-
  CylinderFactorization.lean — BD action factorizes on product subsets

  For a "cylinder" S × [t] in [m]×[n] × [t], the BD action decomposes as:
    S_BD(S × [t]) = t · S_BD_spatial(S) - |S| · (t - 1)

  This is the product structure that connects the spatial partition function
  to black hole thermodynamics: the temporal extent t plays the role of
  inverse temperature β.

  Zero sorry.
-/
import CausalAlgebraicGeometry.BDAction
import Mathlib.Data.Fintype.Prod

namespace CausalAlgebraicGeometry.CylinderFactorization

open CausalAlgebraicGeometry.GridClassification
open CausalAlgebraicGeometry.BDAction

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Spatial BD action (1D: row only) -/

/-- Spatial links in a 1D subset S ⊆ Fin n: consecutive pairs. -/
def spatialLinks (n : ℕ) (S : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  S.product S |>.filter fun p => p.1.val + 1 = p.2.val

/-- Spatial BD action: |S| - |spatial links|. -/
def bdSpatial (n : ℕ) (S : Finset (Fin n)) : Int :=
  (S.card : Int) - (spatialLinks n S).card

/-! ## Cylinder construction -/

/-- The cylinder S × [t]: product of a spatial set S ⊆ Fin n with Fin t. -/
def cylinder (n t : ℕ) (S : Finset (Fin n)) : Finset (Fin n × Fin t) :=
  S.product Finset.univ

theorem cylinder_card (n t : ℕ) (S : Finset (Fin n)) :
    (cylinder n t S).card = S.card * t := by
  simp [cylinder, Finset.card_product, Fintype.card_fin]

/-! ## Link counts on the cylinder -/

-- Helper: membership in hLinks on the cylinder, fully simplified
private lemma mem_hLinks_cylinder (n t : ℕ) (S : Finset (Fin n))
    (a1 a2 : Fin n) (s1 s2 : Fin t) :
    ((a1, s1), (a2, s2)) ∈ hLinks n t (cylinder n t S) ↔
    a1 ∈ S ∧ a2 ∈ S ∧ a1 = a2 ∧ s1.val + 1 = s2.val := by
  unfold hLinks cylinder
  constructor
  · intro h
    have h1 := Finset.mem_filter.mp h
    have h2 := Finset.mem_product.mp h1.1
    have h3 := Finset.mem_product.mp h2.1
    have h4 := Finset.mem_product.mp h2.2
    exact ⟨h3.1, h4.1, h1.2.1, h1.2.2⟩
  · rintro ⟨ha1, ha2, heq, hcons⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha1, Finset.mem_univ _⟩,
      Finset.mem_product.mpr ⟨ha2, Finset.mem_univ _⟩⟩, heq, hcons⟩

-- Helper: membership in vLinks on the cylinder, fully simplified
private lemma mem_vLinks_cylinder (n t : ℕ) (S : Finset (Fin n))
    (a1 a2 : Fin n) (s1 s2 : Fin t) :
    ((a1, s1), (a2, s2)) ∈ vLinks n t (cylinder n t S) ↔
    a1 ∈ S ∧ a2 ∈ S ∧ a1.val + 1 = a2.val ∧ s1 = s2 := by
  unfold vLinks cylinder
  constructor
  · intro h
    have h1 := Finset.mem_filter.mp h
    have h2 := Finset.mem_product.mp h1.1
    have h3 := Finset.mem_product.mp h2.1
    have h4 := Finset.mem_product.mp h2.2
    exact ⟨h3.1, h4.1, h1.2.1, h1.2.2⟩
  · rintro ⟨ha1, ha2, hcons, heq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha1, Finset.mem_univ _⟩,
      Finset.mem_product.mpr ⟨ha2, Finset.mem_univ _⟩⟩, hcons, heq⟩

/-- Horizontal links in the cylinder: same space (row), consecutive time (column).
    hLinks checks p.1.1 = p.2.1 ∧ p.1.2.val + 1 = p.2.2.val, so in the cylinder
    Fin n × Fin t these are temporal links. Count = |S| × (t - 1). -/
theorem cylinder_hLinks_card (n t : ℕ) (S : Finset (Fin n)) :
    (hLinks n t (cylinder n t S)).card = S.card * (t - 1) := by
  cases t with
  | zero =>
    simp [hLinks, cylinder, Finset.filter_empty, Finset.product_empty]
  | succ t =>
    show (hLinks n (t + 1) (cylinder n (t + 1) S)).card = S.card * t
    let f : Fin n × Fin t → (Fin n × Fin (t + 1)) × (Fin n × Fin (t + 1)) :=
      fun ⟨x, j⟩ => ((x, ⟨j.val, by omega⟩), (x, ⟨j.val + 1, by omega⟩))
    have hf_inj : Function.Injective f := by
      intro ⟨x₁, j₁⟩ ⟨x₂, j₂⟩ h
      simp only [f, Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨⟨hx, hj⟩, _⟩ := h
      exact Prod.ext hx (Fin.ext hj)
    have hf_mem : ∀ (x : Fin n) (j : Fin t), x ∈ S →
        f (x, j) ∈ hLinks n (t + 1) (cylinder n (t + 1) S) := by
      intro x j hxS
      rw [mem_hLinks_cylinder]
      exact ⟨hxS, hxS, rfl, rfl⟩
    have hf_surj : ∀ x ∈ hLinks n (t + 1) (cylinder n (t + 1) S),
        ∃ a ∈ S.product (Finset.univ : Finset (Fin t)), f a = x := by
      intro ⟨⟨a1, s1⟩, ⟨a2, s2⟩⟩ hx
      rw [mem_hLinks_cylinder] at hx
      obtain ⟨ha1, _, heq, hcons⟩ := hx
      refine ⟨(a1, ⟨s1.val, by omega⟩), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨ha1, Finset.mem_univ _⟩
      · simp only [f]; ext <;> simp [Fin.ext_iff] <;> omega
    rw [show S.card * t = (S.product (Finset.univ : Finset (Fin t))).card from by
      simp [Finset.card_product, Fintype.card_fin]]
    rw [← Finset.card_image_of_injective _ hf_inj]
    congr 1
    ext ⟨⟨a1, s1⟩, ⟨a2, s2⟩⟩
    constructor
    · intro hx
      rw [Finset.mem_image]
      rw [mem_hLinks_cylinder] at hx
      obtain ⟨ha1, _, heq, hcons⟩ := hx
      exact ⟨(a1, ⟨s1.val, by omega⟩), Finset.mem_product.mpr ⟨ha1, Finset.mem_univ _⟩,
        by simp only [f]; ext <;> simp [Fin.ext_iff] <;> omega⟩
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨⟨a, j⟩, hmem, hf_eq⟩ := hx
      rw [mem_hLinks_cylinder]
      have haS := (Finset.mem_product.mp hmem).1
      simp only [f, Prod.mk.injEq, Fin.mk.injEq] at hf_eq
      obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := hf_eq
      exact ⟨haS, haS, rfl, rfl⟩

/-- Vertical links in the cylinder: consecutive space (row), same time (column).
    vLinks checks p.1.1.val + 1 = p.2.1.val ∧ p.1.2 = p.2.2, so in the cylinder
    Fin n × Fin t these are spatial links. Count = |spatialLinks(S)| × t. -/
theorem cylinder_vLinks_card (n t : ℕ) (S : Finset (Fin n)) :
    (vLinks n t (cylinder n t S)).card = (spatialLinks n S).card * t := by
  let f : (Fin n × Fin n) × Fin t → (Fin n × Fin t) × (Fin n × Fin t) :=
    fun ⟨⟨x, x'⟩, s⟩ => ((x, s), (x', s))
  have hf_inj : Function.Injective f := by
    intro ⟨⟨x1, x1'⟩, s1⟩ ⟨⟨x2, x2'⟩, s2⟩ h
    have h1 : x1 = x2 := by have := congr_arg (fun p => p.1.1) h; exact this
    have h2 : s1 = s2 := by have := congr_arg (fun p => p.1.2) h; exact this
    have h3 : x1' = x2' := by have := congr_arg (fun p => p.2.1) h; exact this
    subst h1; subst h2; subst h3; rfl
  have mem_spatialLinks_iff : ∀ (x x' : Fin n),
      (x, x') ∈ spatialLinks n S ↔ x ∈ S ∧ x' ∈ S ∧ x.val + 1 = x'.val := by
    intro x x'
    unfold spatialLinks
    constructor
    · intro h
      have h1 := Finset.mem_filter.mp h
      have h2 := Finset.mem_product.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    · rintro ⟨hx, hx', hcons⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx'⟩, hcons⟩
  have hf_mem : ∀ p ∈ (spatialLinks n S).product (Finset.univ : Finset (Fin t)),
      f p ∈ vLinks n t (cylinder n t S) := by
    intro ⟨⟨x, x'⟩, s⟩ hmem
    have hmem1 := (Finset.mem_product.mp hmem).1
    rw [mem_spatialLinks_iff] at hmem1
    rw [mem_vLinks_cylinder]
    exact ⟨hmem1.1, hmem1.2.1, hmem1.2.2, rfl⟩
  have hf_surj : ∀ x ∈ vLinks n t (cylinder n t S),
      ∃ p ∈ (spatialLinks n S).product (Finset.univ : Finset (Fin t)), f p = x := by
    intro ⟨⟨a1, s1⟩, ⟨a2, s2⟩⟩ hx
    rw [mem_vLinks_cylinder] at hx
    obtain ⟨ha1, ha2, hcons, heq⟩ := hx
    refine ⟨((a1, a2), s1), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨(mem_spatialLinks_iff a1 a2).mpr ⟨ha1, ha2, hcons⟩,
        Finset.mem_univ _⟩
    · show f ((a1, a2), s1) = ((a1, s1), (a2, s2))
      simp only [f]
      subst heq; rfl
  rw [show (spatialLinks n S).card * t =
      ((spatialLinks n S).product (Finset.univ : Finset (Fin t))).card from by
    simp [Finset.card_product, Fintype.card_fin]]
  rw [← Finset.card_image_of_injective _ hf_inj]
  congr 1
  ext ⟨⟨a1, s1⟩, ⟨a2, s2⟩⟩
  constructor
  · intro hx
    rw [Finset.mem_image]
    rw [mem_vLinks_cylinder] at hx
    obtain ⟨ha1, ha2, hcons, heq⟩ := hx
    refine ⟨((a1, a2), s1),
      Finset.mem_product.mpr ⟨(mem_spatialLinks_iff a1 a2).mpr ⟨ha1, ha2, hcons⟩,
        Finset.mem_univ _⟩, ?_⟩
    show f ((a1, a2), s1) = ((a1, s1), (a2, s2))
    simp only [f]; subst heq; rfl
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨⟨⟨x, x'⟩, s⟩, hmem, hf_eq⟩ := hx
    rw [mem_vLinks_cylinder]
    have hsl := (Finset.mem_product.mp hmem).1
    rw [mem_spatialLinks_iff] at hsl
    change ((x, s), (x', s)) = ((a1, s1), (a2, s2)) at hf_eq
    have h1 := congr_arg Prod.fst hf_eq
    have h2 := congr_arg Prod.snd hf_eq
    simp only [Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨hsl.1, hsl.2.1, hsl.2.2, rfl⟩

/-! ## The factorization theorem -/

/-- **Cylinder factorization**: S_BD(S × [t]) = t · S_BD_spatial(S) - |S| · (t - 1). -/
theorem cylinder_bd_factorization (n t : ℕ) (ht : 0 < t) (S : Finset (Fin n)) :
    bdAction n t (cylinder n t S) =
    (t : Int) * bdSpatial n S - (S.card : Int) * ((t : Int) - 1) := by
  unfold bdAction numLinks bdSpatial
  rw [cylinder_card, cylinder_hLinks_card, cylinder_vLinks_card]
  have ht1 : 1 ≤ t := ht
  zify [ht1]
  ring

/-! ## Physical interpretation

  The cylinder factorization gives:
    S_BD(C × [t]) = t · S_BD_spatial(C) - |C| · (t - 1)

  In the partition function Z(β) = Σ_C exp(-β · S_BD(C × [t])):
    Z(β) = Σ_C exp(-β·t · S_BD_spatial(C) + β(t-1)|C|)

  This is a spatial partition function with:
  - Effective inverse temperature: β_eff = β · t
  - Chemical potential: μ = β · (t - 1)

  For the Euclidean black hole path integral (β = inverse Hawking temperature):
  - t plays the role of β (temporal extent = inverse temperature)
  - The spatial partition function counts states at fixed temperature
  - log Z ~ m^{d-2} gives the Bekenstein-Hawking entropy (area scaling)

  The positive energy theorem (bd_action_ge) applied to each spatial slice
  shows that the spatial ground state is the full spatial grid, confirming
  that flat space dominates the partition function.
-/

end CausalAlgebraicGeometry.CylinderFactorization
