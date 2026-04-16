/-
  CSpecUniqueness.lean — CSpec is the UNIQUE topology for the structure sheaf

  THE RESULT:
  CSpec is uniquely determined: it is the ONLY family of subsets on which
  restriction preserves ring structure. No proper extension or restriction
  of the convex sets can serve as the topology for the structure sheaf.

  This follows from ConvexityIFF.lean:
  - no_enlargement: adding any non-convex set breaks ring hom
  - no_shrinkage: removing any convex set loses a valid open
  - cspec_uniquely_determined: the biconditional (ring hom ↔ convex)

  This file strengthens those results to an explicit uniqueness statement:
  any family F that satisfies "S ∈ F ↔ restriction to S is a ring hom"
  must equal the family of causally convex sets.

  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.ConvexityIFF

namespace CausalAlgebraicGeometry.CSpecUniqueness

open CausalAlgebra CSpecSheaf Uniqueness SheafGammaBridge WidthOneProof CausalPrimality ConvexityIFF

/-! ## Uniqueness as a set equality -/

/-- **CSpec is the UNIQUE topology compatible with the structure sheaf.**

    Any predicate F on finsets that is equivalent to "restriction is a ring hom"
    must agree with IsConvexFS on every finset. -/
theorem cspec_is_unique_topology {k : Type*} [Field k] (C : CAlg k)
    (F : Finset C.Λ → Prop)
    (hF : ∀ S : Finset C.Λ, F S ↔ IsRingHomOpen C S) :
    ∀ S : Finset C.Λ, F S ↔ IsConvexFS C S := by
  intro S
  rw [hF S]
  exact (convexity_iff_preserves_multiplication C S).symm

/-- **Equivalently**: any two predicates that both characterize ring hom opens
    must agree with each other. -/
theorem ring_hom_topology_unique {k : Type*} [Field k] (C : CAlg k)
    (F G : Finset C.Λ → Prop)
    (hF : ∀ S, F S ↔ IsRingHomOpen C S)
    (hG : ∀ S, G S ↔ IsRingHomOpen C S) :
    ∀ S, F S ↔ G S := by
  intro S
  rw [hF S, hG S]

/-- **No alternative topology exists**: any S that is NOT causally convex
    breaks the structure sheaf (witness matrices exist). -/
theorem no_alternative_topology {k : Type*} [Field k] (C : CAlg k) :
    ∀ S : Finset C.Λ, ¬IsConvexFS C S →
      ∃ (M N : CornerElt C Finset.univ),
        ∃ α ∈ S, ∃ β ∈ S,
          (cornerMul C M N).mat α β ≠
          ∑ γ : C.Λ,
            (if γ ∈ S then M.mat α γ else 0) *
            (if γ ∈ S then N.mat γ β else 0) := by
  intro S hS
  exact no_enlargement C S hS

/-- **Every convex set IS needed**: removing any convex set from the topology
    would exclude a valid ring hom open. -/
theorem every_convex_set_needed {k : Type*} [Field k] (C : CAlg k) :
    ∀ S : Finset C.Λ, IsConvexFS C S → IsRingHomOpen C S := by
  intro S hS
  exact no_shrinkage C S hS

/-- **THE UNIQUENESS THEOREM (combined)**: CSpec = {causally convex subsets}
    is the unique family satisfying:
    (1) Every member supports ring hom restriction
    (2) Every non-member breaks ring hom restriction -/
theorem cspec_uniqueness_combined {k : Type*} [Field k] (C : CAlg k) :
    -- Direction 1: convex → ring hom
    (∀ S : Finset C.Λ, IsConvexFS C S → IsRingHomOpen C S)
    -- Direction 2: ¬convex → ¬ring hom (via explicit witness)
    ∧ (∀ S : Finset C.Λ, ¬IsConvexFS C S → ¬IsRingHomOpen C S) := by
  constructor
  · intro S hS; exact no_shrinkage C S hS
  · intro S hS hR
    exact hS ((convexity_iff_preserves_multiplication C S).symm.mp hR)

end CausalAlgebraicGeometry.CSpecUniqueness
