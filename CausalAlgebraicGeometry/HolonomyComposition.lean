/-
  CausalAlgebraicGeometry/HolonomyComposition.lean — Holonomy composition laws

  The interval-projection connection T_{p,q} on a causal algebra
  satisfies algebraic composition laws that make it a genuine connection.

  Main results:
  1. Idempotency: T_{p,q}^2 = T_{p,q}
  2. Junction law: T_{p,q} * T_{q,r} = e_q
  3. Nesting laws: smaller intervals absorb from larger ones
  4. Orthogonality + completeness of idempotents
  5. Associativity of matMul
-/
import CausalAlgebraicGeometry.GaugeConnection

namespace CausalAlgebraicGeometry.HolonomyComposition

open CausalAlgebra GaugeConnection

/-! ### Matrix multiplication associativity -/

/-- Matrix multiplication is associative. -/
theorem matMul_assoc {k : Type*} [Field k] (C : CAlg k)
    (M N P : C.Λ → C.Λ → k) :
    matMul C (matMul C M N) P = matMul C M (matMul C N P) := by
  ext x y
  simp only [matMul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext u; congr 1; ext v; ring

/-! ### Diagonal structure of transition matrices -/

/-- A transition matrix is diagonal: off-diagonal entries are zero. -/
theorem transitionMatrix_diagonal {k : Type*} [Field k] (C : CAlg k)
    (p q : C.Λ) (h : C.le p q) (x y : C.Λ) (hne : x ≠ y) :
    transitionMatrix C p q h x y = 0 := by
  simp only [transitionMatrix]; split_ifs with hc
  · exact absurd hc.1 hne
  · rfl

/-- The diagonal entry of T_{p,q} at x. -/
theorem transitionMatrix_diag {k : Type*} [Field k] (C : CAlg k)
    (p q : C.Λ) (h : C.le p q) (x : C.Λ) :
    transitionMatrix C p q h x x = if inInterval C p q x then 1 else 0 := by
  simp only [transitionMatrix, true_and]

/-- Diagonal entry product for transition matrices. -/
theorem matMul_transition_diag {k : Type*} [Field k] (C : CAlg k)
    (p1 q1 p2 q2 : C.Λ) (h1 : C.le p1 q1) (h2 : C.le p2 q2) (x : C.Λ) :
    matMul C (transitionMatrix C p1 q1 h1)
             (transitionMatrix C p2 q2 h2) x x =
      transitionMatrix C p1 q1 h1 x x * transitionMatrix C p2 q2 h2 x x := by
  simp only [matMul]
  rw [Finset.sum_eq_single x]
  · intro d _ hd; rw [transitionMatrix_diagonal C p1 q1 h1 x d (Ne.symm hd), zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- Off-diagonal product entries are zero. -/
theorem matMul_transition_off_diag {k : Type*} [Field k] (C : CAlg k)
    (p1 q1 p2 q2 : C.Λ) (h1 : C.le p1 q1) (h2 : C.le p2 q2)
    (x y : C.Λ) (hne : x ≠ y) :
    matMul C (transitionMatrix C p1 q1 h1)
             (transitionMatrix C p2 q2 h2) x y = 0 := by
  simp only [matMul]; apply Finset.sum_eq_zero; intro d _
  by_cases hxd : x = d
  · subst hxd; rw [transitionMatrix_diagonal C p2 q2 h2 x y hne, mul_zero]
  · rw [transitionMatrix_diagonal C p1 q1 h1 x d hxd, zero_mul]

/-! ### Master equality lemma -/

/-- Product of transition matrices equals a transition matrix when
    the diagonal entries match. -/
theorem matMul_transition_eq {k : Type*} [Field k] (C : CAlg k)
    (p1 q1 p2 q2 p3 q3 : C.Λ)
    (h1 : C.le p1 q1) (h2 : C.le p2 q2) (h3 : C.le p3 q3)
    (hdiag : ∀ x : C.Λ,
      transitionMatrix C p1 q1 h1 x x * transitionMatrix C p2 q2 h2 x x =
      transitionMatrix C p3 q3 h3 x x) :
    matMul C (transitionMatrix C p1 q1 h1) (transitionMatrix C p2 q2 h2) =
      transitionMatrix C p3 q3 h3 := by
  ext x y; by_cases hxy : x = y
  · subst hxy; rw [matMul_transition_diag, hdiag]
  · rw [matMul_transition_off_diag C p1 q1 p2 q2 h1 h2 x y hxy,
        transitionMatrix_diagonal C p3 q3 h3 x y hxy]

/-! ### Interval lemmas -/

theorem inInterval_self {k : Type*} [Field k] (C : CAlg k) (s x : C.Λ) :
    inInterval C s s x ↔ x = s := by
  constructor
  · intro ⟨h1, h2⟩; exact C.le_antisymm x s h2 h1
  · intro h; subst h; exact ⟨C.le_refl x, C.le_refl x⟩

/-- Indicator product: (if P then 1 else 0) * (if Q then 1 else 0). -/
private theorem ind_mul_ind {k : Type*} [Field k] (P Q : Prop)
    [Decidable P] [Decidable Q] :
    (if P then (1 : k) else 0) * (if Q then 1 else 0) =
      if (P ∧ Q) then 1 else 0 := by
  split_ifs <;> simp_all

/-! ### Idempotency -/

/-- **Idempotency**: T_{p,q}^2 = T_{p,q}. -/
theorem transitionMatrix_idempotent {k : Type*} [Field k] (C : CAlg k)
    (p q : C.Λ) (h : C.le p q) :
    matMul C (transitionMatrix C p q h) (transitionMatrix C p q h) =
      transitionMatrix C p q h := by
  apply matMul_transition_eq C p q p q p q h h h
  intro x; simp only [transitionMatrix_diag, ind_mul_ind, and_self]

/-! ### Junction law -/

/-- **Junction law**: T_{p,q} * T_{q,r} = e_q for p <= q <= r. -/
theorem transitionMatrix_junction {k : Type*} [Field k] (C : CAlg k)
    (p q r : C.Λ) (hpq : C.le p q) (hqr : C.le q r) :
    matMul C (transitionMatrix C p q hpq) (transitionMatrix C q r hqr) =
      transitionMatrix C q q (C.le_refl q) := by
  apply matMul_transition_eq C p q q r q q hpq hqr (C.le_refl q)
  intro x
  simp only [transitionMatrix_diag, ind_mul_ind]
  congr 1; apply propext
  constructor
  · intro ⟨⟨_, hxq⟩, ⟨hqx, _⟩⟩
    have := C.le_antisymm x q hxq hqx
    subst this; exact ⟨C.le_refl x, C.le_refl x⟩
  · intro ⟨hqx, hxq⟩
    have := C.le_antisymm x q hxq hqx
    subst this; exact ⟨⟨hpq, C.le_refl x⟩, ⟨C.le_refl x, hqr⟩⟩

/-! ### Nesting laws -/

/-- **Nesting**: T_{p,r} * T_{p,q} = T_{p,q} for p <= q <= r. -/
theorem transitionMatrix_nesting_left {k : Type*} [Field k] (C : CAlg k)
    (p q r : C.Λ) (hpq : C.le p q) (hqr : C.le q r) :
    matMul C (transitionMatrix C p r (C.le_trans p q r hpq hqr))
             (transitionMatrix C p q hpq) =
      transitionMatrix C p q hpq := by
  apply matMul_transition_eq C p r p q p q (C.le_trans p q r hpq hqr) hpq hpq
  intro x; simp only [transitionMatrix_diag, ind_mul_ind]
  congr 1; apply propext
  constructor
  · intro ⟨_, h2⟩; exact h2
  · intro h; exact ⟨⟨h.1, C.le_trans x q r h.2 hqr⟩, h⟩

/-- **Nesting**: T_{p,q} * T_{p,r} = T_{p,q} for p <= q <= r. -/
theorem transitionMatrix_nesting_right {k : Type*} [Field k] (C : CAlg k)
    (p q r : C.Λ) (hpq : C.le p q) (hqr : C.le q r) :
    matMul C (transitionMatrix C p q hpq)
             (transitionMatrix C p r (C.le_trans p q r hpq hqr)) =
      transitionMatrix C p q hpq := by
  apply matMul_transition_eq C p q p r p q hpq (C.le_trans p q r hpq hqr) hpq
  intro x; simp only [transitionMatrix_diag, ind_mul_ind]
  congr 1; apply propext
  constructor
  · intro ⟨h1, _⟩; exact h1
  · intro h; exact ⟨h, ⟨h.1, C.le_trans x q r h.2 hqr⟩⟩

/-- **Nesting**: T_{p,r} * T_{q,r} = T_{q,r} for p <= q <= r. -/
theorem transitionMatrix_nesting_right_interval {k : Type*} [Field k] (C : CAlg k)
    (p q r : C.Λ) (hpq : C.le p q) (hqr : C.le q r) :
    matMul C (transitionMatrix C p r (C.le_trans p q r hpq hqr))
             (transitionMatrix C q r hqr) =
      transitionMatrix C q r hqr := by
  apply matMul_transition_eq C p r q r q r (C.le_trans p q r hpq hqr) hqr hqr
  intro x; simp only [transitionMatrix_diag, ind_mul_ind]
  congr 1; apply propext
  constructor
  · intro ⟨_, h2⟩; exact h2
  · intro h; exact ⟨⟨C.le_trans p q x hpq h.1, h.2⟩, h⟩

/-- **Nesting**: T_{q,r} * T_{p,r} = T_{q,r} for p <= q <= r. -/
theorem transitionMatrix_nesting_left_interval {k : Type*} [Field k] (C : CAlg k)
    (p q r : C.Λ) (hpq : C.le p q) (hqr : C.le q r) :
    matMul C (transitionMatrix C q r hqr)
             (transitionMatrix C p r (C.le_trans p q r hpq hqr)) =
      transitionMatrix C q r hqr := by
  apply matMul_transition_eq C q r p r q r hqr (C.le_trans p q r hpq hqr) hqr
  intro x; simp only [transitionMatrix_diag, ind_mul_ind]
  congr 1; apply propext
  constructor
  · intro ⟨h1, _⟩; exact h1
  · intro h; exact ⟨h, ⟨C.le_trans p q x hpq h.1, h.2⟩⟩

/-! ### Orthogonality of idempotents -/

/-- e_p * e_q = 0 for p != q. -/
theorem idempotent_orthogonal {k : Type*} [Field k] (C : CAlg k)
    (p q : C.Λ) (hne : p ≠ q) :
    matMul C (transitionMatrix C p p (C.le_refl p))
             (transitionMatrix C q q (C.le_refl q)) =
      fun _ _ => 0 := by
  ext x y; by_cases hxy : x = y
  · subst hxy
    rw [matMul_transition_diag]
    simp only [transitionMatrix_diag, ind_mul_ind, inInterval]
    have : ¬((C.le p x ∧ C.le x p) ∧ (C.le q x ∧ C.le x q)) := by
      intro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have hxp := C.le_antisymm x p (h2) (h1)
      have hxq := C.le_antisymm x q (h4) (h3)
      exact hne (hxp.symm ▸ hxq)
    simp [this]
  · exact matMul_transition_off_diag C p p q q (C.le_refl p) (C.le_refl q) x y hxy

/-! ### Completeness -/

/-- Sum of all idempotents equals the identity matrix. -/
theorem idempotent_sum_is_identity {k : Type*} [Field k] (C : CAlg k) :
    (fun x y : C.Λ => ∑ w : C.Λ,
      transitionMatrix C w w (C.le_refl w) x y) = matId C := by
  ext x y
  simp only [transitionMatrix, inInterval, matId]
  by_cases hxy : x = y
  · subst hxy; simp only [true_and]
    rw [Finset.sum_eq_single x]
    · simp [C.le_refl]
    · intro w _ hw
      have : ¬(C.le w x ∧ C.le x w) := by
        intro ⟨h1, h2⟩; exact hw (C.le_antisymm w x h1 h2)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ x) h
  · simp only [hxy, false_and, ite_false]; exact Finset.sum_const_zero

/-! ### Trace composition -/

/-- tr(T_{p,q} * T_{q,r}) = 1. -/
theorem trace_junction {k : Type*} [Field k] (C : CAlg k)
    (p q r : C.Λ) (hpq : C.le p q) (hqr : C.le q r) :
    matTrace C (matMul C (transitionMatrix C p q hpq)
                          (transitionMatrix C q r hqr)) = 1 := by
  rw [transitionMatrix_junction C p q r hpq hqr]
  exact chain_holonomy_trivial C q

/-! ### Multi-step composition -/

/-- The junction product is idempotent. -/
theorem junction_idempotent {k : Type*} [Field k] (C : CAlg k)
    (p q r : C.Λ) (hpq : C.le p q) (hqr : C.le q r) :
    matMul C (matMul C (transitionMatrix C p q hpq)
                        (transitionMatrix C q r hqr))
             (matMul C (transitionMatrix C p q hpq)
                        (transitionMatrix C q r hqr)) =
      matMul C (transitionMatrix C p q hpq)
               (transitionMatrix C q r hqr) := by
  rw [transitionMatrix_junction C p q r hpq hqr]
  exact transitionMatrix_idempotent C q q (C.le_refl q)

/-- (T_{p,q} * T_{q,r}) * T_{r,s} = e_q * T_{r,s}. -/
theorem four_step_composition {k : Type*} [Field k] (C : CAlg k)
    (p q r s : C.Λ) (hpq : C.le p q) (hqr : C.le q r) (hrs : C.le r s) :
    matMul C (matMul C (transitionMatrix C p q hpq)
                        (transitionMatrix C q r hqr))
             (transitionMatrix C r s hrs) =
      matMul C (transitionMatrix C q q (C.le_refl q))
               (transitionMatrix C r s hrs) := by
  rw [transitionMatrix_junction C p q r hpq hqr]

/-- Four-step trace vanishes when q != r. -/
theorem trace_four_step_zero {k : Type*} [Field k] (C : CAlg k)
    (p q r s : C.Λ) (hpq : C.le p q) (hqr : C.le q r) (hrs : C.le r s)
    (hne : q ≠ r) :
    matTrace C (matMul C (matMul C (transitionMatrix C p q hpq)
                                    (transitionMatrix C q r hqr))
                          (transitionMatrix C r s hrs)) = 0 := by
  rw [four_step_composition C p q r s hpq hqr hrs]
  simp only [matTrace, matMul]
  apply Finset.sum_eq_zero; intro x _
  rw [Finset.sum_eq_single x]
  · simp only [transitionMatrix_diag, ind_mul_ind, inInterval]
    have : ¬((C.le q x ∧ C.le x q) ∧ (C.le r x ∧ C.le x s)) := by
      intro ⟨⟨h1, h2⟩, ⟨h3, _⟩⟩
      exact hne ((C.le_antisymm x q h2 h1).symm ▸ C.le_antisymm x r
        ((C.le_antisymm x q h2 h1) ▸ hqr) h3)
    simp [this]
  · intro z _ hz
    rw [transitionMatrix_diagonal C q q (C.le_refl q) x z (Ne.symm hz), zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-! ### Summary

    For p <= q <= r in a causal algebra C:

    * T_{p,q} * T_{q,r} = e_q  (junction law)
    * T_{p,r} * T_{p,q} = T_{p,q}  (nesting)
    * T_{p,r} * T_{q,r} = T_{q,r}  (nesting)
    * e_p * e_q = 0 for p != q  (orthogonality)
    * Sum_w e_w = I  (completeness)
    * T_{p,q}^2 = T_{p,q}  (idempotency)
    * matMul is associative

    The junction law is the discrete parallel transport composition:
    transport from [p,q] followed by transport from [q,r]
    localizes to the junction point q. -/

end CausalAlgebraicGeometry.HolonomyComposition
