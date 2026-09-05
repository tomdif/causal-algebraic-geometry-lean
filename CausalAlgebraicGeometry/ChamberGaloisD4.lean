/-
  ChamberGaloisD4.lean — The first full chamber-symmetry theorem.

  A transitive permutation action on a two-element type is already the full
  symmetric action.  The dimension-four residual chamber polynomial is an
  irreducible quadratic, so this elementary observation closes the first
  genuine case of the chamber Galois conjecture.
-/
import CausalAlgebraicGeometry.ChamberFrobenius
import CausalAlgebraicGeometry.ChamberGaloisConjecture

namespace CausalAlgebraicGeometry.ChamberGaloisD4

open Polynomial
open CausalAlgebraicGeometry.ChamberGaloisBridge
open CausalAlgebraicGeometry.ChamberFrobenius

/-- Two permutations of a two-element type are determined by the image of
one point. -/
private theorem perm_eq_of_card_two_apply_eq
    {α : Type*} [Fintype α] (hcard : Fintype.card α = 2)
    {σ τ : Equiv.Perm α} {x : α} (h : σ x = τ x) : σ = τ := by
  classical
  have hne : ∃ y : α, y ≠ x := by
    by_contra hall
    push_neg at hall
    haveI : Subsingleton α := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have : Fintype.card α ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
    omega
  obtain ⟨y, hyx⟩ := hne
  have huniv : ({x, y} : Finset α) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [hyx, Ne.symm hyx] using hcard.symm
  have every (z : α) : z = x ∨ z = y := by
    have hz : z ∈ ({x, y} : Finset α) := by rw [huniv]; simp
    simpa [Finset.mem_insert, Finset.mem_singleton] using hz
  apply Equiv.ext
  intro z
  rcases every z with hz | hz
  · subst z
    exact h
  · subst z
    have hσ : σ y ≠ σ x := fun heq => hyx (σ.injective heq)
    have hτ : τ y ≠ τ x := fun heq => hyx (τ.injective heq)
    rcases every (σ x) with hσx | hσx <;>
      rcases every (σ y) with hσy | hσy <;>
      rcases every (τ x) with hτx | hτx <;>
      rcases every (τ y) with hτy | hτy <;>
      simp_all

/-- Every transitive action on a two-element finite type realizes every
permutation. -/
theorem surjective_toPermHom_of_card_two
    {G α : Type*} [Group G] [Fintype α] [MulAction G α]
    (hcard : Fintype.card α = 2)
    (htrans : ∀ x y : α, ∃ g : G, g • x = y) :
    Function.Surjective (MulAction.toPermHom G α) := by
  classical
  intro τ
  have hnonempty : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let x : α := Classical.choice hnonempty
  obtain ⟨g, hg⟩ := htrans x (τ x)
  refine ⟨g, ?_⟩
  apply perm_eq_of_card_two_apply_eq hcard
  exact hg

/-- The rational residual chamber polynomial in dimension four is
irreducible. -/
theorem qResidualChamberPolynomial_four_irreducible :
    Irreducible (qResidualChamberPolynomial 4) := by
  have hunit : IsUnit (C (150 : ℚ)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  apply (irreducible_isUnit_mul hunit).mp
  rw [qResidualChamberPolynomial_four]
  exact ChamberQ4.Q4_irreducible

/-- **First full chamber-symmetry theorem.**  The canonical Galois action for
`d = 4` is the full symmetric group on the two residual roots. -/
theorem hasFullChamberGaloisGroup_four : HasFullChamberGaloisGroup 4 := by
  have hirr := qResidualChamberPolynomial_four_irreducible
  have hsep : (qResidualChamberPolynomial 4).Separable :=
    PerfectField.separable_of_irreducible hirr
  apply surjective_toPermHom_of_card_two
  · simpa using chamberRoot_card 4 hsep
  · exact chamberGaloisAction_pretransitive 4 hirr

noncomputable local instance chamberRootFourDecidableEq :
    DecidableEq (ChamberRoot 4) := Classical.decEq _

/-- The certified mod-11 pattern `[2]` is realized by an actual two-cycle in
the characteristic-zero chamber Galois action.  This is the first concrete
instance of the Frobenius-cycle conclusion. -/
theorem exists_chamberGalois_cycleType_four :
    ∃ σ : (qResidualChamberPolynomial 4).Gal,
      (chamberGaloisActionHom 4 σ).cycleType = {2} := by
  classical
  have hsep : (qResidualChamberPolynomial 4).Separable :=
    PerfectField.separable_of_irreducible
      qResidualChamberPolynomial_four_irreducible
  have hcard : Fintype.card (ChamberRoot 4) = 2 :=
    chamberRoot_card 4 hsep
  have hnonempty : Nonempty (ChamberRoot 4) :=
    Fintype.card_pos_iff.mp (by omega)
  let x : ChamberRoot 4 := Classical.choice hnonempty
  have hexists : ∃ y : ChamberRoot 4, y ≠ x := by
    by_contra hall
    push_neg at hall
    have hle : Fintype.card (ChamberRoot 4) ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
    omega
  obtain ⟨y, hyx⟩ := hexists
  obtain ⟨σ, hσ⟩ := hasFullChamberGaloisGroup_four (Equiv.swap x y)
  refine ⟨σ, ?_⟩
  rw [hσ, (Equiv.Perm.isSwap_iff_cycleType.mp
    (Equiv.Perm.swap_isSwap_iff.mpr (Ne.symm hyx)))]

theorem exists_chamberGalois_two_cycle_four :
    ∃ σ : (qResidualChamberPolynomial 4).Gal,
      2 ∈ (chamberGaloisActionHom 4 σ).cycleType := by
  obtain ⟨σ, hσ⟩ := exists_chamberGalois_cycleType_four
  exact ⟨σ, by rw [hσ]; simp⟩

/-- The bridge conclusion for every certificate with the first pattern.  In
degree two, full symmetry supplies the required Frobenius cycle directly. -/
theorem frobeniusCycleBridge_four_eleven
    (_cert : FrobeniusFactorCertificate 4 11 [2]) :
    ∃ σ : (qResidualChamberPolynomial 4).Gal,
      (chamberGaloisActionHom 4 σ).cycleType =
        ([2].filter fun degree => degree ≠ 1) := by
  simpa using exists_chamberGalois_cycleType_four

/-- The general Frobenius bridge remains open, but its first certified
instance is closed: the mod-11 pattern `[2]` is realized by an actual element
of the characteristic-zero chamber Galois group. -/
theorem q4Mod11Certificate_realizes_cycle_pattern :
    ∃ σ : (qResidualChamberPolynomial 4).Gal,
      (chamberGaloisActionHom 4 σ).cycleType =
        ([2].filter fun degree => degree ≠ 1) :=
  frobeniusCycleBridge_four_eleven q4Mod11Certificate

end CausalAlgebraicGeometry.ChamberGaloisD4
