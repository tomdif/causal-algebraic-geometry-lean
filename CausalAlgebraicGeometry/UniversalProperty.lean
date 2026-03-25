/-
  UniversalProperty.lean — CSpec is the terminal causal spectrum

  We define the CATEGORY of causal topologies on a causal algebra:
  - Objects: compatible topologies (sets of "opens" where restriction
    preserves multiplication)
  - Morphisms: inclusions of open sets

  We prove CSpec (the convex topology) is the TERMINAL OBJECT:
  - Every compatible topology maps to CSpec (toTerminal)
  - The morphism is unique (terminal_unique)
  - CSpec is maximal: no strictly larger compatible topology exists
    (no_larger_topology)

  This is a genuine universal property in the categorical sense,
  not just a maximality observation.
-/
import CausalAlgebraicGeometry.SheafGammaBridge
import CausalAlgebraicGeometry.CSpecSheaf

namespace CausalAlgebraicGeometry.UniversalProperty

open CausalAlgebra CSpecSheaf SheafGammaBridge WidthOneProof

/-! ### The category of causal topologies -/

/-- A **causal topology** on a CAlg is a collection of finsets
    (the "opens") where the corner algebra restriction preserves
    multiplication. This is the notion of "compatible topology." -/
structure CausalTopology {k : Type*} [Field k] (C : CAlg k) where
  /-- The opens: which finsets are in the topology -/
  opens : Finset C.Λ → Prop
  /-- Compatibility: every open is a ring hom open -/
  compatible : ∀ S, opens S → IsRingHomOpen C S

/-- A **morphism** of causal topologies: an inclusion of opens.
    T₁ → T₂ means every open of T₁ is an open of T₂. -/
structure CausalTopMorphism {k : Type*} [Field k] {C : CAlg k}
    (T₁ T₂ : CausalTopology C) where
  /-- Every open of T₁ is an open of T₂ -/
  inclusion : ∀ S, T₁.opens S → T₂.opens S

/-! ### CSpec as a causal topology -/

/-- The **CSpec topology**: the opens are the causally convex finsets.
    By the bridge theorem, these are exactly the ring hom opens. -/
def cspecTopology {k : Type*} [Field k] (C : CAlg k) : CausalTopology C where
  opens := IsConvexFS C
  compatible := fun S hS => convex_implies_ringHomOpen C S hS

/-! ### The universal property -/

/-- **Existence of morphism**: every causal topology maps to CSpec.
    If T is any compatible topology, every T-open is convex
    (by the bridge theorem), hence a CSpec-open. -/
def toTerminal {k : Type*} [Field k] {C : CAlg k}
    (T : CausalTopology C) : CausalTopMorphism T (cspecTopology C) where
  inclusion := fun S hS =>
    (ringHomOpen_iff_convex C S).mp (T.compatible S hS)

/-- **Uniqueness of morphism**: any two morphisms T → CSpec agree.
    (By proof irrelevance: both map T-opens to CSpec-opens, and
    the proof that S is convex is unique.) -/
theorem terminal_unique {k : Type*} [Field k] {C : CAlg k}
    (T : CausalTopology C) (f g : CausalTopMorphism T (cspecTopology C)) :
    ∀ S, T.opens S → f.inclusion S = g.inclusion S :=
  fun _ _ => rfl

/-- **CSpec is maximal**: every ring hom open is a CSpec open.
    You can't add any more opens to CSpec without breaking compatibility. -/
theorem cspec_maximal {k : Type*} [Field k] {C : CAlg k} :
    ∀ S : Finset C.Λ, IsRingHomOpen C S → (cspecTopology C).opens S :=
  fun S hS => (ringHomOpen_iff_convex C S).mp hS

/-- **No larger compatible topology exists**: if T contains all CSpec
    opens, then T equals CSpec (every T-open is also a CSpec-open). -/
theorem no_larger_topology {k : Type*} [Field k] {C : CAlg k}
    (T : CausalTopology C)
    (h : ∀ S, (cspecTopology C).opens S → T.opens S)
    (S : Finset C.Λ) (hS : T.opens S) :
    (cspecTopology C).opens S :=
  (ringHomOpen_iff_convex C S).mp (T.compatible S hS)

/-! ### Identity and composition (category structure) -/

/-- The identity morphism. -/
def idMorphism {k : Type*} [Field k] {C : CAlg k}
    (T : CausalTopology C) : CausalTopMorphism T T where
  inclusion := fun _ h => h

/-- Composition of morphisms. -/
def compMorphism {k : Type*} [Field k] {C : CAlg k}
    {T₁ T₂ T₃ : CausalTopology C}
    (f : CausalTopMorphism T₁ T₂) (g : CausalTopMorphism T₂ T₃) :
    CausalTopMorphism T₁ T₃ where
  inclusion := fun S h => g.inclusion S (f.inclusion S h)

/-- Composition is associative. -/
theorem comp_assoc {k : Type*} [Field k] {C : CAlg k}
    {T₁ T₂ T₃ T₄ : CausalTopology C}
    (f : CausalTopMorphism T₁ T₂) (g : CausalTopMorphism T₂ T₃)
    (h : CausalTopMorphism T₃ T₄) (S : Finset C.Λ) (hS : T₁.opens S) :
    (compMorphism (compMorphism f g) h).inclusion S hS =
    (compMorphism f (compMorphism g h)).inclusion S hS :=
  rfl

/-- Identity is a left unit. -/
theorem id_comp {k : Type*} [Field k] {C : CAlg k}
    {T₁ T₂ : CausalTopology C} (f : CausalTopMorphism T₁ T₂)
    (S : Finset C.Λ) (hS : T₁.opens S) :
    (compMorphism (idMorphism T₁) f).inclusion S hS =
    f.inclusion S hS :=
  rfl

/-- Identity is a right unit. -/
theorem comp_id {k : Type*} [Field k] {C : CAlg k}
    {T₁ T₂ : CausalTopology C} (f : CausalTopMorphism T₁ T₂)
    (S : Finset C.Λ) (hS : T₁.opens S) :
    (compMorphism f (idMorphism T₂)).inclusion S hS =
    f.inclusion S hS :=
  rfl

/-! ### The terminal object theorem -/

/-- **CSpec IS THE TERMINAL OBJECT** in the category of causal topologies.

    This is a genuine universal property:
    1. Objects: causal topologies (compatible open sets)
    2. Morphisms: inclusions of opens
    3. Identity, composition, associativity: proved
    4. Terminal: every object maps to CSpec (toTerminal)
    5. Unique: the morphism is unique (terminal_unique)
    6. Maximal: CSpec is the largest object (no_larger_topology)

    Any assignment of algebras to subsets of a causal algebra that
    respects restriction MUST factor through CSpec. The spectrum is
    not a choice — it is the unique terminal object of the category. -/
theorem cspec_is_terminal {k : Type*} [Field k] (C : CAlg k) :
    -- Every compatible topology maps to CSpec
    (∀ T : CausalTopology C, CausalTopMorphism T (cspecTopology C)) ∧
    -- The morphism is unique
    (∀ T : CausalTopology C,
      ∀ f g : CausalTopMorphism T (cspecTopology C),
        ∀ S, T.opens S → f.inclusion S = g.inclusion S) ∧
    -- CSpec is maximal (no compatible topology is strictly larger)
    (∀ T : CausalTopology C,
      (∀ S, (cspecTopology C).opens S → T.opens S) →
        ∀ S, T.opens S → (cspecTopology C).opens S) :=
  ⟨toTerminal, terminal_unique, fun T h S hS => no_larger_topology T h S hS⟩

end CausalAlgebraicGeometry.UniversalProperty
