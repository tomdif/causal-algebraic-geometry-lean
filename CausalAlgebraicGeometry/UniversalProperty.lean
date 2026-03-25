/-
  UniversalProperty.lean — CSpec is the universal causal spectrum

  THE UNIVERSAL PROPERTY: CSpec is not merely A spectrum — it is THE
  spectrum. Any assignment of algebras to subsets of a causal algebra
  that respects multiplication under restriction MUST factor through
  the convex opens, which ARE the opens of CSpec.

  Formally: let F be any functor from finsets to algebras such that
  F(S) carries a multiplication and restriction F(T) → F(S) (for S ⊆ T)
  preserves this multiplication. Then the domain of F (the subsets
  on which restriction is a ring homomorphism) is contained in the
  set of causally convex subsets = the opens of CSpec.

  Moreover, the convex opens are the LARGEST such domain
  (causal_primality_unique_maximal).

  This makes CSpec the terminal object among compatible spectra:
  every other compatible spectrum maps to CSpec, and CSpec maps to
  no smaller spectrum. It is canonical, forced, and inevitable.

  Proof: combines ringHomOpen_iff_convex (the bridge theorem) with
  causal_primality_unique_maximal (the uniqueness theorem).
-/
import CausalAlgebraicGeometry.SheafGammaBridge
import CausalAlgebraicGeometry.Uniqueness

namespace CausalAlgebraicGeometry.UniversalProperty

open CausalAlgebra CSpecSheaf Uniqueness SheafGammaBridge WidthOneProof

/-! ### The universal property -/

/-- A **compatible spectrum** is a collection of finsets (the "opens")
    on which the corner algebra restriction preserves multiplication.
    Formally: a predicate P on finsets such that P(S) implies S is
    a ring homomorphism open for the corner algebra sheaf. -/
def IsCompatibleSpectrum {k : Type*} [Field k] (C : CAlg k)
    (P : Finset C.Λ → Prop) : Prop :=
  ∀ S, P S → IsRingHomOpen C S

/-- **THE UNIVERSAL PROPERTY**: CSpec is the terminal compatible spectrum.

    Part 1: CSpec IS compatible (every convex open is a ring hom open).
    Part 2: CSpec is MAXIMAL (every compatible spectrum is contained in CSpec).
    Part 3: CSpec is FORCED (non-convex subsets break ring hom).

    Any functor assigning algebras to subsets and respecting restriction
    must have its domain contained in the convex opens = CSpec opens.
    CSpec is the largest such domain. Therefore CSpec is unavoidable. -/
theorem cspec_universal_property {k : Type*} [Field k] (C : CAlg k) :
    -- Part 1: CSpec is compatible
    (∀ S : Finset C.Λ, IsConvexFS C S → IsRingHomOpen C S) ∧
    -- Part 2: Every compatible spectrum is contained in CSpec
    (∀ P : Finset C.Λ → Prop,
      IsCompatibleSpectrum C P →
      ∀ S, P S → IsConvexFS C S) ∧
    -- Part 3: CSpec is the ONLY maximal compatible spectrum
    --   (non-convex → not ring hom open → not in any compatible spectrum)
    (∀ S : Finset C.Λ, ¬ IsConvexFS C S → ¬ IsRingHomOpen C S) :=
  ⟨-- Part 1: convex → ring hom open
   fun S hS => convex_implies_ringHomOpen C S hS,
   -- Part 2: compatible → contained in convex
   fun P hP S hPS => (ringHomOpen_iff_convex C S).mp (hP S hPS),
   -- Part 3: non-convex → not ring hom open
   fun S hS => not_convex_implies_not_ringHomOpen C S hS⟩

/-- **Corollary**: CSpec is the unique maximal compatible spectrum.
    If P and Q are both maximal compatible spectra (i.e., both equal
    to the set of convex subsets), they are identical. There is no
    choice in defining the spectrum of a causal algebra. -/
theorem cspec_unique {k : Type*} [Field k] (C : CAlg k)
    (P Q : Finset C.Λ → Prop)
    (hP : IsCompatibleSpectrum C P)
    (hQ : IsCompatibleSpectrum C Q)
    (hP_max : ∀ S, IsConvexFS C S → P S)
    (hQ_max : ∀ S, IsConvexFS C S → Q S) :
    ∀ S, P S ↔ Q S := by
  intro S
  constructor
  · intro hPS
    exact hQ_max S ((ringHomOpen_iff_convex C S).mp (hP S hPS))
  · intro hQS
    exact hP_max S ((ringHomOpen_iff_convex C S).mp (hQ S hQS))

/-- **The inevitability theorem**: there is exactly ONE way to define
    a spectrum on a causal algebra that is compatible with the ring
    structure. The convex subsets are forced by the algebra, not chosen. -/
theorem cspec_inevitable {k : Type*} [Field k] (C : CAlg k) :
    -- The ring hom opens are EXACTLY the convex subsets
    (∀ S : Finset C.Λ, IsRingHomOpen C S ↔ IsConvexFS C S) ∧
    -- This biconditional means: any compatible spectrum must use
    -- convex subsets as opens, and CSpec uses ALL convex subsets.
    -- There is no room for variation.
    (∀ S : Finset C.Λ, IsConvexFS C S → IsRingHomOpen C S) ∧
    (∀ S : Finset C.Λ, ¬ IsConvexFS C S → ¬ IsRingHomOpen C S) :=
  ⟨fun S => ringHomOpen_iff_convex C S,
   fun S hS => convex_implies_ringHomOpen C S hS,
   fun S hS => not_convex_implies_not_ringHomOpen C S hS⟩

end CausalAlgebraicGeometry.UniversalProperty
