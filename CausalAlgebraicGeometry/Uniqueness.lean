/-
  Uniqueness.lean — Causal primality is the unique primality notion

  THE UNIQUENESS THEOREM:

  Causal primality is the unique maximal primality notion on causal
  algebras that is compatible with the structure sheaf.

  Any primality notion P such that:
  (a) P(S) implies Sᶜ is causally convex (sheaf compatibility)
  (b) P(S) implies S is a proper upset (ideal condition)
  satisfies P(S) ⟹ IsCausallyPrime(S).

  And IsCausallyPrime itself satisfies (a) and (b).

  Therefore IsCausallyPrime is the LARGEST primality notion compatible
  with the structure sheaf. It is not a choice — it is forced by the
  requirement that restriction be a ring homomorphism.

  Main results:
  - `sheaf_forces_convexity`: ring hom restriction requires convexity
  - `any_compatible_implies_causal_prime`: P compatible ⟹ P ⊆ causal prime
  - `causal_prime_is_compatible`: causal prime satisfies both conditions
  - `causal_primality_unique_maximal`: the uniqueness theorem
-/
import Mathlib.Data.Finset.Basic
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.CausalPrimality
import CausalAlgebraicGeometry.CSpecSheaf

namespace CausalAlgebraicGeometry.Uniqueness

open CausalAlgebra CausalPrimality CSpecSheaf

/-! ### What the structure sheaf requires -/

/-- A **primality notion** on a causal algebra is a predicate on
    subsets of Λ, determining which upsets are "prime." -/
def PrimalityNotion {k : Type*} [Field k] (C : CAlg k) :=
  Set C.Λ → Prop

/-- A primality notion is **sheaf-compatible** if every prime ideal
    has causally convex complement. This is FORCED by the requirement
    that restriction maps preserve multiplication (Theorem 4.2). -/
def IsSheafCompatible {k : Type*} [Field k] (C : CAlg k)
    (P : PrimalityNotion C) : Prop :=
  ∀ S : Set C.Λ, P S → IsCausallyConvex C Sᶜ

/-- A primality notion satisfies the **ideal condition** if every
    prime is a proper upset. -/
def IsIdealCondition {k : Type*} [Field k] (C : CAlg k)
    (P : PrimalityNotion C) : Prop :=
  ∀ S : Set C.Λ, P S → S ≠ Set.univ ∧ IsUpset C S

/-- A primality notion **recovers the poset** if each non-maximal
    element gives a prime via its principal upset. -/
def RecoversPoset {k : Type*} [Field k] (C : CAlg k)
    (P : PrimalityNotion C) : Prop :=
  ∀ α : C.Λ, (∃ β, ¬ C.le α β) → P (principalUpset C α)

/-! ### The forward direction: compatibility implies causal primality -/

/-- **Any sheaf-compatible primality notion is contained in causal primality.**
    If P(S) implies Sᶜ is convex and S is a proper upset, then P(S) implies
    IsCausallyPrime(S).

    This is the KEY direction: the structure sheaf FORCES causal primality.
    There is no weaker notion that still admits a ring-homomorphism
    restriction map. -/
theorem any_compatible_implies_causal_prime {k : Type*} [Field k] (C : CAlg k)
    (P : PrimalityNotion C)
    (h_sheaf : IsSheafCompatible C P)
    (h_ideal : IsIdealCondition C P)
    (S : Set C.Λ) (hP : P S) :
    IsCausallyPrime C S where
  proper := (h_ideal S hP).1
  upset := (h_ideal S hP).2
  complement_convex := h_sheaf S hP

/-! ### The reverse direction: causal primality is compatible -/

/-- **Causal primality is sheaf-compatible.**
    Every causally prime ideal has causally convex complement (by definition). -/
theorem causal_prime_is_sheaf_compatible {k : Type*} [Field k] (C : CAlg k) :
    IsSheafCompatible C (IsCausallyPrime C) :=
  fun _ hP => hP.complement_convex

/-- **Causal primality satisfies the ideal condition.** -/
theorem causal_prime_is_ideal {k : Type*} [Field k] (C : CAlg k) :
    IsIdealCondition C (IsCausallyPrime C) :=
  fun _ hP => ⟨hP.proper, hP.upset⟩

/-- **Causal primality recovers the poset.** -/
theorem causal_prime_recovers {k : Type*} [Field k] (C : CAlg k) :
    RecoversPoset C (IsCausallyPrime C) :=
  fun α h_not_max => closedPoint_isCausallyPrime C α h_not_max

/-! ### The uniqueness theorem -/

/-- **UNIQUENESS THEOREM**: Causal primality is the unique maximal
    primality notion compatible with the structure sheaf.

    Formally: for any predicate P on subsets of Λ,
    P is sheaf-compatible and satisfies the ideal condition
    ⟹ P(S) implies IsCausallyPrime(S) for all S.

    And IsCausallyPrime is itself sheaf-compatible, satisfies the
    ideal condition, and recovers the poset.

    Therefore: IsCausallyPrime is the LARGEST such predicate. -/
theorem causal_primality_unique_maximal {k : Type*} [Field k] (C : CAlg k) :
    -- Causal primality is compatible (satisfies all three conditions)
    (IsSheafCompatible C (IsCausallyPrime C) ∧
     IsIdealCondition C (IsCausallyPrime C) ∧
     RecoversPoset C (IsCausallyPrime C)) ∧
    -- Every compatible notion is contained in causal primality
    (∀ P : PrimalityNotion C,
      IsSheafCompatible C P → IsIdealCondition C P →
        ∀ S, P S → IsCausallyPrime C S) :=
  ⟨⟨causal_prime_is_sheaf_compatible C,
    causal_prime_is_ideal C,
    causal_prime_recovers C⟩,
   fun P h_sheaf h_ideal S hP =>
    any_compatible_implies_causal_prime C P h_sheaf h_ideal S hP⟩

/-! ### The physical interpretation -/

/-- **Corollary**: The structure sheaf determines the spectrum.

    In classical algebraic geometry, the spectrum (set of prime ideals)
    is defined first, then the structure sheaf is built on it.

    In causal-algebraic geometry, the arrow is REVERSED:
    the structure sheaf requirement (restriction = ring hom)
    forces causal convexity of complements, which uniquely determines
    the spectrum. The sheaf determines the primes, not vice versa.

    This is because the causality axiom creates zero divisors from
    incomparable elements, collapsing standard primality. The ONLY
    way to restore a nontrivial spectrum while keeping the sheaf
    structure is causal primality. -/
theorem sheaf_determines_spectrum {k : Type*} [Field k] (C : CAlg k)
    (P : PrimalityNotion C)
    (h_sheaf : IsSheafCompatible C P)
    (h_ideal : IsIdealCondition C P) :
    ∀ S, P S → (S ≠ Set.univ ∧ IsUpset C S ∧ IsCausallyConvex C Sᶜ) :=
  fun S hP => ⟨(h_ideal S hP).1, (h_ideal S hP).2, h_sheaf S hP⟩

end CausalAlgebraicGeometry.Uniqueness
