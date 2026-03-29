/-
  ConvexityIFF.lean — The clean biconditional

  Causal convexity is EQUIVALENT to restriction preserving multiplication.
  This combines:
  - Forward (CSpecSheaf.lean): product_supported_on_convex
  - Backward (Uniqueness.lean): non_convex_breaks_restriction

  And states the uniqueness corollary: CSpec is the ONLY topology
  (family of open subsets) on which restriction is a ring homomorphism.
-/
import CausalAlgebraicGeometry.SheafGammaBridge

namespace CausalAlgebraicGeometry.ConvexityIFF

open CausalAlgebra CSpecSheaf Uniqueness SheafGammaBridge WidthOneProof CausalPrimality

/-! ### The biconditional: convexity iff restriction preserves multiplication -/

/-- **THE BICONDITIONAL** (Finset version):

    A finset S is causally convex if and only if restriction to S
    preserves the ring structure of corner algebras.

    Forward: convexity kills cross-terms (product_supported_on_convex).
    Backward: non-convexity admits explicit counterexample matrices
    (non_convex_breaks_restriction). -/
theorem convexity_iff_preserves_multiplication {k : Type*} [Field k]
    (C : CAlg k) (S : Finset C.Λ) :
    IsConvexFS C S ↔ IsRingHomOpen C S :=
  (ringHomOpen_iff_convex C S).symm

/-- Equivalent reformulation using IsConvex from CSpecSheaf.
    IsConvex and IsConvexFS are definitionally equal. -/
theorem isConvex_eq_isConvexFS {k : Type*} [Field k]
    (C : CAlg k) (S : Finset C.Λ) :
    IsConvex C S ↔ IsConvexFS C S := by
  constructor
  · intro h α hα β hβ γ hαγ hγβ; exact h α hα β hβ γ hαγ hγβ
  · intro h α hα β hβ γ hαγ hγβ; exact h α hα β hβ γ hαγ hγβ

/-- The biconditional using IsConvex (from CSpecSheaf). -/
theorem isConvex_iff_ringHomOpen {k : Type*} [Field k]
    (C : CAlg k) (S : Finset C.Λ) :
    IsConvex C S ↔ IsRingHomOpen C S := by
  rw [isConvex_eq_isConvexFS]
  exact convexity_iff_preserves_multiplication C S

/-! ### Bridge to IsCausallyConvex (Set-based version) -/

/-- IsCausallyConvex on the coercion of a Finset to a Set is equivalent
    to IsConvexFS on the Finset. -/
theorem isCausallyConvex_coe_iff_isConvexFS {k : Type*} [Field k]
    (C : CAlg k) (S : Finset C.Λ) :
    IsCausallyConvex C (↑S : Set C.Λ) ↔ IsConvexFS C S := by
  constructor
  · intro h α hα β hβ γ hαγ hγβ
    -- IsCausallyConvex: ∀ α β γ, α ∈ S → β ∈ S → C.le α γ → C.le γ β → γ ∈ S
    exact Finset.mem_coe.mp
      (h α β γ (Finset.mem_coe.mpr hα) (Finset.mem_coe.mpr hβ) hαγ hγβ)
  · intro h α β γ hα hβ hαγ hγβ
    exact Finset.mem_coe.mpr
      (h α (Finset.mem_coe.mp hα) β (Finset.mem_coe.mp hβ) γ hαγ hγβ)

/-- **THE BICONDITIONAL** (Set version):

    IsCausallyConvex on ↑S iff restriction to S is a ring homomorphism. -/
theorem isCausallyConvex_iff_ringHomOpen {k : Type*} [Field k]
    (C : CAlg k) (S : Finset C.Λ) :
    IsCausallyConvex C (↑S : Set C.Λ) ↔ IsRingHomOpen C S := by
  rw [isCausallyConvex_coe_iff_isConvexFS]
  exact convexity_iff_preserves_multiplication C S

/-! ### Uniqueness corollary: CSpec is uniquely determined -/

/-- **CSpec is the UNIQUE topology for the structure sheaf**.

    If a family of finsets F is exactly the collection of subsets on
    which restriction is a ring homomorphism, then F is precisely the
    causally convex subsets. There is no other choice.

    This means CSpec (the causal spectrum) is not one of many possible
    constructions -- it is the ONLY possible structure sheaf topology. -/
theorem cspec_uniquely_determined {k : Type*} [Field k] (C : CAlg k) :
    -- A finset S admits a ring-homomorphic restriction iff it is causally convex.
    -- Therefore: the opens of CSpec = {causally convex subsets} is the unique
    -- family of subsets supporting a structure sheaf.
    (∀ S : Finset C.Λ, IsRingHomOpen C S ↔ IsConvexFS C S) := by
  intro S
  exact ringHomOpen_iff_convex C S

/-- **No enlargement**: if we try to add any non-convex set to the topology,
    the structure sheaf breaks -- there exist sections whose product
    is not preserved by restriction. -/
theorem no_enlargement {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hS : ¬ IsConvexFS C S) :
    ∃ (M N : CornerElt C Finset.univ),
      ∃ α ∈ S, ∃ β ∈ S,
        (cornerMul C M N).mat α β ≠
        ∑ γ : C.Λ,
          (if γ ∈ S then M.mat α γ else 0) *
          (if γ ∈ S then N.mat γ β else 0) :=
  non_convex_breaks_restriction C S hS

/-- **No shrinkage**: every convex set IS a ring hom open --
    removing it from the topology would lose valid opens. -/
theorem no_shrinkage {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hS : IsConvexFS C S) :
    IsRingHomOpen C S :=
  convex_implies_ringHomOpen C S hS

end CausalAlgebraicGeometry.ConvexityIFF
