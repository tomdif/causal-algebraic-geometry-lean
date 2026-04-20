/-
  SupportObstruction.lean — Sharp characterization of when the canonical slab
  boundaries are antitone globally (not just on support).

  CONTEXT: SlabCharacterization proves lowerBdy and upperBdy are antitone on
  support (i.e., restricted to base points where the fiber is nonempty). The
  conventional values at off-support points (lowerBdy = m, upperBdy = 0) need
  not extend antitone-ness globally. This file pins down the exact obstruction.

  MAIN RESULTS (zero sorry):

  Define supp(S) := { f : Fin d → Fin m | (fiber_S f).Nonempty }.

    1. upperBdy is antitone globally ⟺ supp(S) is a downset of [m]^d.
    2. lowerBdy is antitone globally ⟺ supp(S) is an upset of [m]^d.
    3. Both antitone globally ⟺ supp(S) ∈ { ∅, ([m]^d : Finset) } — i.e.,
       either S = ∅ or every fiber of S is nonempty (full support).

  CONSEQUENCE FOR THE SLAB "BIJECTION": the forward map S ↦ (lowerBdy_S, upperBdy_S)
  lands in the antitone pairs (φ, ψ with φ ≤ ψ) iff S has full support or is
  empty. For partial-support convex S, the canonical pair is antitone only on
  supp(S), and the canonical empty-fiber values (m and 0) obstruct globality.

  This is the exact combinatorial "obstruction class" — in sheaf-theoretic
  language, the failure is parametrised by the support-type stratification of
  [m]^d. We don't formalise the sheaf version here; the plain combinatorial
  statement contains the same information.

  Zero sorry.
-/
import CausalAlgebraicGeometry.SlabCharacterization

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 400000

namespace CausalAlgebraicGeometry.SupportObstruction

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlicingBound
open CausalAlgebraicGeometry.SlabCharacterization

noncomputable section
open scoped Classical

/-! ## The support of a convex set along the last coordinate -/

/-- The support of S: the set of base points where the fiber is nonempty. -/
def support (d m : ℕ) (S : Finset (Fin (d + 1) → Fin m)) :
    Finset (Fin d → Fin m) :=
  Finset.univ.filter fun f => (fiber d m S f).Nonempty

theorem mem_support_iff {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m))
    (f : Fin d → Fin m) :
    f ∈ support d m S ↔ (fiber d m S f).Nonempty := by
  simp [support]

/-! ## Small technical lemmas about the canonical boundary values -/

/-- If the fiber is empty, lowerBdy returns the canonical value m. -/
theorem lowerBdy_of_empty {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m))
    (f : Fin d → Fin m) (hne : ¬ (fiber d m S f).Nonempty) :
    lowerBdy d m S f = m := by
  simp [lowerBdy, hne]

/-- If the fiber is empty, upperBdy returns the canonical value 0. -/
theorem upperBdy_of_empty {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m))
    (f : Fin d → Fin m) (hne : ¬ (fiber d m S f).Nonempty) :
    upperBdy d m S f = 0 := by
  simp [upperBdy, hne]

/-- If the fiber is nonempty, lowerBdy is strictly less than m. -/
theorem lowerBdy_lt_m_of_nonempty {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m))
    (f : Fin d → Fin m) (hne : (fiber d m S f).Nonempty) :
    lowerBdy d m S f < m := by
  simp only [lowerBdy, hne, dite_true]
  exact ((fiber d m S f).min' hne).isLt

/-- If the fiber is nonempty, upperBdy is strictly positive. -/
theorem upperBdy_pos_of_nonempty {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m))
    (f : Fin d → Fin m) (hne : (fiber d m S f).Nonempty) :
    0 < upperBdy d m S f := by
  simp only [upperBdy, hne, dite_true]
  omega

/-! ## Characterization: upperBdy antitone globally ⟺ support is a downset -/

/-- The upper boundary is antitone globally on [m]^d iff supp(S) is a downset. -/
theorem upperBdy_antitone_global_iff_supp_downset {d m : ℕ}
    {S : Finset (Fin (d + 1) → Fin m)} (hS : IsConvexDim (d + 1) m S) :
    (∀ f g : Fin d → Fin m, f ≤ g → upperBdy d m S g ≤ upperBdy d m S f) ↔
    IsDownsetDim d m (support d m S) := by
  constructor
  · -- ⟹: globally antitone upperBdy ⟹ support downset.
    intro hanti g hg f hfg
    rw [mem_support_iff] at hg ⊢
    -- g ∈ supp, f ≤ g, want f ∈ supp.
    have hub_g_pos : 0 < upperBdy d m S g := upperBdy_pos_of_nonempty S g hg
    have hle : upperBdy d m S g ≤ upperBdy d m S f := hanti f g hfg
    have hub_f_pos : 0 < upperBdy d m S f := lt_of_lt_of_le hub_g_pos hle
    by_contra hne
    rw [upperBdy_of_empty S f hne] at hub_f_pos
    exact Nat.lt_irrefl 0 hub_f_pos
  · -- ⟸: support downset ⟹ globally antitone upperBdy.
    intro hds f g hfg
    by_cases hg : (fiber d m S g).Nonempty
    · by_cases hf : (fiber d m S f).Nonempty
      · exact upperBdy_antitone hS f g hfg hf hg
      · -- f has empty fiber, but g has nonempty fiber and f ≤ g.
        -- Apply downset: g ∈ supp ∧ f ≤ g ⟹ f ∈ supp. Contradiction with hf.
        have : f ∈ support d m S :=
          hds g ((mem_support_iff S g).mpr hg) f hfg
        rw [mem_support_iff] at this
        exact absurd this hf
    · -- g's fiber is empty, so upperBdy(g) = 0, trivially ≤ upperBdy(f).
      rw [upperBdy_of_empty S g hg]; exact Nat.zero_le _

/-! ## Characterization: lowerBdy antitone globally ⟺ support is an upset -/

/-- The lower boundary is antitone globally on [m]^d iff supp(S) is an upset. -/
theorem lowerBdy_antitone_global_iff_supp_upset {d m : ℕ}
    {S : Finset (Fin (d + 1) → Fin m)} (hS : IsConvexDim (d + 1) m S) :
    (∀ f g : Fin d → Fin m, f ≤ g → lowerBdy d m S g ≤ lowerBdy d m S f) ↔
    IsUpsetDim d m (support d m S) := by
  constructor
  · -- ⟹: globally antitone lowerBdy ⟹ support upset.
    intro hanti f hf g hfg
    rw [mem_support_iff] at hf ⊢
    -- f ∈ supp, f ≤ g, want g ∈ supp.
    have hlb_f_lt : lowerBdy d m S f < m := lowerBdy_lt_m_of_nonempty S f hf
    have hle : lowerBdy d m S g ≤ lowerBdy d m S f := hanti f g hfg
    have hlb_g_lt : lowerBdy d m S g < m := lt_of_le_of_lt hle hlb_f_lt
    by_contra hne
    rw [lowerBdy_of_empty S g hne] at hlb_g_lt
    exact Nat.lt_irrefl m hlb_g_lt
  · -- ⟸: support upset ⟹ globally antitone lowerBdy.
    intro hus f g hfg
    by_cases hf : (fiber d m S f).Nonempty
    · by_cases hg : (fiber d m S g).Nonempty
      · exact lowerBdy_antitone hS f g hfg hf hg
      · -- f has nonempty fiber, g has empty. Upset says f ∈ supp ∧ f ≤ g ⟹ g ∈ supp.
        have : g ∈ support d m S :=
          hus f ((mem_support_iff S f).mpr hf) g hfg
        rw [mem_support_iff] at this
        exact absurd this hg
    · -- f's fiber is empty, so lowerBdy(f) = m, and lowerBdy(g) ≤ m always.
      rw [lowerBdy_of_empty S f hf]
      by_cases hg : (fiber d m S g).Nonempty
      · exact Nat.le_of_lt (lowerBdy_lt_m_of_nonempty S g hg)
      · rw [lowerBdy_of_empty S g hg]

/-! ## The combined characterization: both antitone ⟺ support is trivial -/

/-- A subset of [m]^d that is both a downset and an upset is either empty or
    everything, since [m]^d is connected under the product order. -/
theorem downset_and_upset_is_trivial {d m : ℕ}
    (T : Finset (Fin d → Fin m))
    (hds : IsDownsetDim d m T) (hus : IsUpsetDim d m T) :
    T = ∅ ∨ T = Finset.univ := by
  classical
  by_cases hne : T.Nonempty
  · right
    -- T is nonempty: pick x ∈ T. For any y, use meet x ∧ y to reach y.
    obtain ⟨x, hx⟩ := hne
    apply Finset.eq_univ_iff_forall.mpr
    intro y
    -- Let z i = min (x i) (y i). Then z ≤ x and z ≤ y.
    let z : Fin d → Fin m := fun i => min (x i) (y i)
    have hzx : z ≤ x := fun i => by simp [z]
    have hzy : z ≤ y := fun i => by simp [z]
    -- T is downset: x ∈ T, z ≤ x ⟹ z ∈ T.
    have hzT : z ∈ T := hds x hx z hzx
    -- T is upset: z ∈ T, z ≤ y ⟹ y ∈ T.
    exact hus z hzT y hzy
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hne

/-- Support is empty iff S is empty (every point has fiber = the containing slice). -/
theorem support_empty_iff_S_empty {d m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (d + 1) → Fin m)) :
    support d m S = ∅ ↔ S = ∅ := by
  constructor
  · intro hsupp
    rw [← Finset.not_nonempty_iff_eq_empty]
    intro hSne
    obtain ⟨p, hp⟩ := hSne
    -- p ∈ S ⟹ its base point is in supp.
    let f : Fin d → Fin m := fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    let k : Fin m := p ⟨d, Nat.lt_succ_iff.mpr (le_refl d)⟩
    have hk_mem : k ∈ fiber d m S f := by
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
      have hrecon : extendByZ d m f k = p := extendByZ_reconstruct d m p
      rw [hrecon]; exact hp
    have hf_supp : f ∈ support d m S :=
      (mem_support_iff S f).mpr ⟨k, hk_mem⟩
    rw [hsupp] at hf_supp
    exact absurd hf_supp (by simp)
  · intro hS
    subst hS
    ext f
    simp [support, fiber]

/-- **MAIN CHARACTERIZATION**: both canonical boundaries are antitone globally
    iff S is empty or has full support (every fiber nonempty).

    This is the exact obstruction to the forward slab map landing in the
    antitone-pair set globally. -/
theorem boundaries_antitone_global_iff_supp_trivial {d m : ℕ} (hm : 0 < m)
    {S : Finset (Fin (d + 1) → Fin m)} (hS : IsConvexDim (d + 1) m S) :
    ((∀ f g : Fin d → Fin m, f ≤ g → lowerBdy d m S g ≤ lowerBdy d m S f) ∧
     (∀ f g : Fin d → Fin m, f ≤ g → upperBdy d m S g ≤ upperBdy d m S f)) ↔
    (S = ∅ ∨ ∀ f : Fin d → Fin m, (fiber d m S f).Nonempty) := by
  rw [lowerBdy_antitone_global_iff_supp_upset hS,
      upperBdy_antitone_global_iff_supp_downset hS]
  constructor
  · intro ⟨hus, hds⟩
    rcases downset_and_upset_is_trivial (support d m S) hds hus with h | h
    · left; exact (support_empty_iff_S_empty hm S).mp h
    · right; intro f
      have : f ∈ support d m S := by rw [h]; exact Finset.mem_univ _
      exact (mem_support_iff S f).mp this
  · intro h
    rcases h with hS0 | hfull
    · subst hS0
      refine ⟨?_, ?_⟩
      · intro p hp q hq
        simp [support, fiber] at hp
      · intro p hp q hq
        simp [support, fiber] at hp
    · have hsupp : support d m S = Finset.univ := by
        ext f
        simp only [mem_support_iff, Finset.mem_univ, iff_true]
        exact hfull f
      refine ⟨?_, ?_⟩
      · rw [hsupp]; intro p _ q _; exact Finset.mem_univ _
      · rw [hsupp]; intro p _ q _; exact Finset.mem_univ _

/-! ## Summary

RESULT (zero sorry):

  For convex S ⊆ [m]^{d+1}:
    • upperBdy_S antitone globally  ⟺  supp(S) is a downset of [m]^d.
    • lowerBdy_S antitone globally  ⟺  supp(S) is an upset of [m]^d.
    • BOTH antitone globally        ⟺  S = ∅ or supp(S) = full (all fibers nonempty).

CONSEQUENCE: the forward map S ↦ (lowerBdy_S, upperBdy_S) lands in "antitone
pair globally" precisely for S empty or full-support. Partial-support convex S
give pairs antitone on supp(S) but not globally.

This sharpens the previous on-support statements (lowerBdy_antitone,
upperBdy_antitone) to a complete characterization of when on-support extends
to global antitone — isolating the exact combinatorial obstruction to the
slab "bijection" claim.

WHAT THIS MEANS FOR THE UPPER BOUND c_d ≤ 2 L_d:
  The sandwich (SlabBijection.lean) uses the INJECTION convex ↪ downset × upset
  via (↓S, ↑S), which is sharper than the antitone-pair count and works for
  any convex S. The obstruction characterized here explains why a naive
  antitone-pair count overcounts (20 pairs vs 13 convex at d=1, m=2): empty
  fibers force canonical values that break globality.

  Whether the upper bound of the sandwich is tight (c_d = 2 L_d) is still open
  for d ≥ 3. The full-support lower bound (FullSupportLowerBound.lean) is the
  natural pathway.
-/

end -- noncomputable section

end CausalAlgebraicGeometry.SupportObstruction
