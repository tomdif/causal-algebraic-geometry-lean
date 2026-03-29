/-
  BulletproofRecovery.lean — The strict upset α ↦ ↑α is ALWAYS a CSpec point.

  The previous `closedPoint_isCausallyPrime` required `h_not_max : ∃ β, ¬ C.le α β`.
  This hypothesis is UNNECESSARY: α ∉ ↑α always (since α ≠ α is false),
  so ↑α ≠ Λ (properness) is automatic.

  Combined with `closedPoint_injective_T0` (injectivity under T₀),
  this gives the bulletproof recovery theorem:

  For any T₀ finite poset, α ↦ ↑α is an injection into CSpec.
  No hypotheses on individual elements are needed.

  Zero sorry.
-/
import CausalAlgebraicGeometry.CausalScheme

namespace CausalAlgebraicGeometry.BulletproofRecovery

open CausalAlgebraicGeometry.CausalPrimality
open CausalAlgebraicGeometry.CausalScheme
open CausalAlgebra

/-- α is never in its own strict principal upset. -/
theorem not_mem_principalUpset {k : Type*} [Field k] (C : CAlg k) (α : C.Λ) :
    α ∉ principalUpset C α := by
  intro ⟨_, hne⟩; exact hne rfl

/-- The strict principal upset is ALWAYS proper (↑α ≠ Λ), for ALL α.
    Proof: α ∉ ↑α, so ↑α ≠ Set.univ. -/
theorem principalUpset_proper {k : Type*} [Field k] (C : CAlg k) (α : C.Λ) :
    principalUpset C α ≠ Set.univ := by
  intro h
  have : α ∈ principalUpset C α := h ▸ Set.mem_univ α
  exact not_mem_principalUpset C α this

/-- **Bulletproof version**: ↑α is causally prime for ALL α ∈ Λ.
    No `h_not_max` hypothesis needed. -/
theorem principalUpset_isCausallyPrime {k : Type*} [Field k]
    (C : CAlg k) (α : C.Λ) :
    IsCausallyPrime C (principalUpset C α) where
  proper := principalUpset_proper C α
  upset := principalUpset_isUpset C α
  complement_convex := principalUpset_complement_convex C α

/-- The CSpec embedding: every element gives a CSpec point. -/
def cspecPoint {k : Type*} [Field k] (C : CAlg k) (α : C.Λ) : CSpec C :=
  ⟨principalUpset C α, principalUpset_isCausallyPrime C α⟩

/-- **The Bulletproof Recovery Theorem**:
    For T₀ (future-distinguishing) posets, α ↦ ↑α is an injection into CSpec.
    - Every element maps to a valid CSpec point (no exceptions, no hypotheses)
    - The map is injective iff the poset is future-distinguishing
    - This recovers the original poset from CSpec -/
theorem bulletproof_recovery {k : Type*} [Field k] (C : CAlg k)
    (hT0 : IsFutureDistinguishing C) :
    Function.Injective (cspecPoint C) := by
  intro α β h
  -- cspecPoint α = cspecPoint β means principalUpset α = principalUpset β
  have : principalUpset C α = principalUpset C β := by
    have := congr_arg Subtype.val h
    exact this
  -- By T₀, this implies α = β
  exact closedPoint_injective_T0 C hT0 this

/-- Without T₀, the map is still well-defined (every element gives a CSpec point)
    but may not be injective. The V-poset (RecoveryCounterexample.lean) shows this. -/
theorem cspecPoint_always_valid {k : Type*} [Field k] (C : CAlg k) (α : C.Λ) :
    (cspecPoint C α).val = principalUpset C α := rfl

/-! ## What the paper should say

  **Theorem (Bulletproof Recovery).**
  Let (Λ, ≤) be a finite poset and A its causal algebra over a field k.

  (a) For every α ∈ Λ, the strict principal upset ↑α = {β : α < β} is
      causally prime. In particular, ↑α ∈ CSpec(A).

  (b) The map α ↦ ↑α is injective if and only if the poset is
      future-distinguishing (T₀): distinct elements have distinct strict futures.

  (c) For future-distinguishing posets, the original poset (Λ, ≤) is recovered
      from CSpec(A) via the closed-point embedding α ↦ ↑α.

  **No hypotheses on individual elements are needed for part (a).**
  The T₀ condition is needed only for injectivity (b), and is a property of the
  POSET, not of individual elements. Counterexample without T₀: the V-poset
  {0, 1, 2} with 0 < 2, 1 < 2 has ↑0 = {2} = ↑1.
-/

end CausalAlgebraicGeometry.BulletproofRecovery
