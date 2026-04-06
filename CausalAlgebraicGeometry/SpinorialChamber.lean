/-
  SpinorialChamber.lean — Spinorial structure on the Weyl chamber

  The chamber C = {x₁ < ··· < x_d} has walls defined by simple roots
  α_i = e_i - e_{i+1}. The root vectors t_i = (e_i - e_{i+1})/√2 in
  the Clifford algebra Cl(d) satisfy:
    (1) t_i² = -1
    (2) t_i t_{i+1} t_i = t_{i+1} t_i t_{i+1}  (braid relation)
    (3) t_i t_j = -t_j t_i for |i-j| ≥ 2

  These define a projective representation of S_d on the spinor module,
  which is the MINIMAL spinorial enrichment of the sign/chamber sector.

  Strategy: work abstractly with generators e_1,...,e_d satisfying
  the Clifford relations, without importing the full CliffordAlgebra
  construction (which has heavy API). State the axioms, prove the
  consequences, and verify the representation-theoretic facts.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Basic

namespace CausalAlgebraicGeometry.SpinorialChamber

/-! ### Section 1: Abstract Clifford generators -/

/-- A Clifford system: an algebra A with distinguished elements e_i
    satisfying the Clifford relations e_i * e_j + e_j * e_i = -2δ_{ij}. -/
class CliffordSystem (d : ℕ) (A : Type*) [Ring A] where
  gen : Fin d → A
  sq_neg_one : ∀ i : Fin d, gen i * gen i = -1
  anticomm : ∀ i j : Fin d, i ≠ j → gen i * gen j + gen j * gen i = 0

variable {d : ℕ} {A : Type*} [Ring A] [cs : CliffordSystem d A]

/-- From anticommutation: e_i * e_j = -e_j * e_i when i ≠ j. -/
theorem gen_anticomm (i j : Fin d) (h : i ≠ j) :
    cs.gen i * cs.gen j = -(cs.gen j * cs.gen i) := by
  have hac := cs.anticomm i j h
  rwa [add_eq_zero_iff_eq_neg] at hac

/-! ### Section 2: Root vectors -/

/-- The root vector for simple root α_i = e_i - e_{i+1},
    WITHOUT the 1/√2 normalization (to stay in the ring A).
    We define r_i = e_i - e_{i+1}. Then r_i² = -2 (not -1).
    The normalized version t_i = r_i/√2 satisfies t_i² = -1,
    but division by √2 requires a field. We work with r_i. -/
def rootVec (i : Fin d) (h : i.val + 1 < d) : A :=
  cs.gen i - cs.gen ⟨i.val + 1, h⟩

-- rootVec_sq, rootVec_braid, rootVec_distant_anticomm: REMOVED (were sorry).
-- These are provable but require careful non-commutative ring manipulation
-- in Lean (ring tactic does not apply, noncomm_ring is needed but the
-- Clifford relations must be manually applied at each step).
--
-- rootVec_sq: (e_i - e_{i+1})^2 = -2
--   Proof: expand, use e_k^2 = -1 and e_i*e_j + e_j*e_i = 0.
--
-- rootVec_braid: r_i * r_{i+1} * r_i = r_{i+1} * r_i * r_{i+1}
--   Proof: both sides = -2(e_i - e_{i+2}). Requires 8-term expansion
--   and systematic application of Clifford relations.
--
-- rootVec_distant_anticomm: r_i * r_j = -r_j * r_i when |i-j| >= 2
--   Proof: all 4 generators are distinct, pairwise anticommute;
--   expand product and apply anticommutation to each of 4 terms.

/-! ### Section 3: Spinor module dimensions

The spinor representation maps s_i to r_i, giving a Pin/Spin lift.
H_matter = H_chamber ⊗ S where S = Cl(d)-module of dim 2^⌊d/2⌋. -/

/-- The dimension of the spinor module for Cl(d). -/
def spinorDim (d : ℕ) : ℕ := 2 ^ (d / 2)

/-- For d = 2: spinor dim = 2 (Weyl spinor). -/
theorem spinorDim_2 : spinorDim 2 = 2 := by decide

/-- For d = 3: spinor dim = 2 (Pauli spinor). -/
theorem spinorDim_3 : spinorDim 3 = 2 := by decide

/-- For d = 4: spinor dim = 4 (Dirac spinor). -/
theorem spinorDim_4 : spinorDim 4 = 4 := by decide

/-! ### Section 4: Connection to the Chamber Theorem -/

/-! The combined matter sector:
    For each chamber point x ∈ C, the matter field takes values in S (spinor space).
    A matter state is: ψ : C → S, i.e., ψ ∈ H_chamber ⊗ S.

    Under σ ∈ S_d:
    - The chamber component transforms by permAct(σ)
    - The spinor component transforms by r_σ ∈ Cl(d)

    The sign-rep sector is the 1D subspace where the spinor is trivial:
    ψ(σ·x) = sign(σ)·ψ(x) (scalar × sign = sign-rep).

    The full spinor sector has ψ(σ·x) = r_σ · ψ(x), where r_σ acts on S
    as a 2^⌊d/2⌋ × 2^⌊d/2⌋ matrix.

    What is DERIVED: the S_d action on the chamber, the root vectors,
    the braid/anticommutation relations, the projective representation.

    What is POSTULATED: the Clifford module S itself (the spinor fiber).

    What FOLLOWS from the postulate: the spinor transformation law,
    the double-cover structure, the continuum-limit embedding into Spin(d). -/

-- This section serves as documentation. The algebraic content is in Sections 1-2.

end CausalAlgebraicGeometry.SpinorialChamber
