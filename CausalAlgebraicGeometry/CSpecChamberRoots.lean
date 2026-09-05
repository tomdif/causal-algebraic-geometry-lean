/-
  CSpecChamberRoots.lean — Chamber roots indexed over the causal spectrum.

  The same convex complement that supports the local corner ring determines a
  local chamber dimension.  This file assigns the corresponding rational
  residual polynomial and splitting-field root type to every causal prime,
  forming a genuine sheaf of root choices on CSpec.

  Local constancy is not automatic: complement cardinality may jump.  This
  file proves the conditional and fixed-dimension-stratum forms;
  `CSpecChamberRootsCounterexample.lean` disproves the unrestricted form.
-/
import CausalAlgebraicGeometry.CSpecRingSheaf
import CausalAlgebraicGeometry.ChamberGaloisConjecture

namespace CausalAlgebraicGeometry.CSpecChamberRoots

open CategoryTheory Opposite TopologicalSpace
open CausalAlgebra CausalPrimality CSpecActualSheaf
open CausalAlgebraicGeometry.ChamberGaloisBridge
open CausalAlgebraicGeometry.ChamberGaloisConjecture

universe u

variable {k : Type u} [Field k] (C : CAlg k)

/-- The local chamber dimension is two plus the size of the convex region
complementary to the causal prime. -/
noncomputable def localChamberDimension (P : CSpecTop C) : ℕ :=
  (primeComplementFinset C P).card + 2

theorem localChamberDimension_sub_two (P : CSpecTop C) :
    localChamberDimension C P - 2 = (primeComplementFinset C P).card := by
  simp [localChamberDimension]

/-- The local residual polynomial attached to a causal prime. -/
noncomputable def localResidualPolynomial (P : CSpecTop C) : Polynomial ℚ :=
  qResidualChamberPolynomial (localChamberDimension C P)

/-- Its degree is exactly the cardinality of the region supporting the local
corner ring. -/
theorem localResidualPolynomial_natDegree (P : CSpecTop C) :
    (localResidualPolynomial C P).natDegree =
      (primeComplementFinset C P).card := by
  rw [localResidualPolynomial, qResidualChamberPolynomial_natDegree,
    localChamberDimension_sub_two]

/-- Splitting-field roots of the local chamber polynomial. -/
abbrev localChamberRootFiber (P : CSpecTop C) : Type :=
  ChamberRoot (localChamberDimension C P)

/-- A sheaf whose sections choose a local chamber root at every causal prime
in an open set. -/
noncomputable def causalChamberRootSheaf :
    (CSpecTop C).Sheaf (Type _) :=
  TopCat.sheafToTypes (CSpecTop C) (localChamberRootFiber C)

theorem causalChamberRootSheaf_isSheaf :
    (causalChamberRootSheaf C).presheaf.IsSheaf :=
  (causalChamberRootSheaf C).2

@[simp]
theorem causalChamberRootSheaf_obj (U : Opens (CSpecTop C)) :
    (causalChamberRootSheaf C).presheaf.obj (op U) =
      (∀ P : U, localChamberRootFiber C P) :=
  rfl

/-- The actual local splitting-field Galois action. -/
noncomputable def localChamberGaloisActionHom (P : CSpecTop C) :
    (localResidualPolynomial C P).Gal →*
      Equiv.Perm (localChamberRootFiber C P) :=
  chamberGaloisActionHom (localChamberDimension C P)

theorem localChamberGaloisAction_faithful (P : CSpecTop C) :
    Function.Injective (localChamberGaloisActionHom C P) :=
  chamberGaloisAction_faithful (localChamberDimension C P)

/-- Equal local chamber dimensions give canonically equivalent root fibres. -/
theorem localChamberRootFiber_equiv_of_dimension_eq
    (P Q : CSpecTop C)
    (h : localChamberDimension C P = localChamberDimension C Q) :
    Nonempty (localChamberRootFiber C P ≃ localChamberRootFiber C Q) := by
  change Nonempty
    (ChamberRoot (localChamberDimension C P) ≃
      ChamberRoot (localChamberDimension C Q))
  rw [h]
  exact ⟨Equiv.refl _⟩

/-- Full local chamber symmetry wherever the corner support has at least two
events. -/
def HasFullLocalChamberSymmetry : Prop :=
  ∀ P : CSpecTop C,
    2 ≤ (primeComplementFinset C P).card →
      HasFullChamberGaloisGroup (localChamberDimension C P)

/-- The global chamber Galois conjecture implies full symmetry in every
eligible CSpec fibre. -/
theorem chamberGaloisConjecture_implies_fullLocal
    (h : ChamberGaloisConjecture) :
    HasFullLocalChamberSymmetry C := by
  intro P hcard
  apply h (localChamberDimension C P)
  simp [localChamberDimension]
  omega

/-- The unrestricted local-system property.  It is not true for every CSpec;
`CSpecChamberRootsCounterexample.lean` gives a two-point counterexample. -/
def ChamberRootLocalSystemStatement : Prop :=
  ∀ P : CSpecTop C,
    ∃ U : Opens (CSpecTop C), P ∈ U ∧
      ∀ Q : U, Nonempty (localChamberRootFiber C P ≃ localChamberRootFiber C Q)

/-- The precise topological input needed for unstratified local constancy. -/
def LocalChamberDimensionLocallyConstant : Prop :=
  ∀ P : CSpecTop C,
    ∃ U : Opens (CSpecTop C), P ∈ U ∧
      ∀ Q : U, localChamberDimension C P = localChamberDimension C Q

/-- Local constancy of the dimension function promotes the root sheaf to the
stated local system. -/
theorem chamberRootLocalSystem_of_dimensionLocallyConstant
    (h : LocalChamberDimensionLocallyConstant C) :
    ChamberRootLocalSystemStatement C := by
  intro P
  obtain ⟨U, hPU, hdim⟩ := h P
  exact ⟨U, hPU, fun Q =>
    localChamberRootFiber_equiv_of_dimension_eq C P Q (hdim Q)⟩

/-- The root family is unconditionally constant on each local-dimension
stratum.  This is the correct general theorem when dimension jumps across
specializations of CSpec. -/
theorem chamberRootFiber_constant_on_dimension_stratum
    (n : ℕ) (P Q : CSpecTop C)
    (hP : localChamberDimension C P = n)
    (hQ : localChamberDimension C Q = n) :
    Nonempty (localChamberRootFiber C P ≃ localChamberRootFiber C Q) :=
  localChamberRootFiber_equiv_of_dimension_eq C P Q (hP.trans hQ.symm)

end CausalAlgebraicGeometry.CSpecChamberRoots
