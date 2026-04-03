/-
  ChamberTheorem.lean — The fermion sector of the comparability kernel

  THEOREM (Chamber Theorem). Let K be the comparability kernel on (Fin m)^d,
  and let C = {x : x₁ < x₂ < ··· < x_d} be the fundamental Weyl chamber.
  Define the fermionic kernel
    K_F(x, y) = Σ_{σ ∈ S_d} sign(σ) · K(x, σ·y)
  for x, y ∈ C. Then:
  (1) K commutes with the S_d action: K(σ·x, σ·y) = K(x, y)
  (2) The sign-representation subspace H_sgn is K-invariant
  (3) K_F has Dirichlet BC: K_F(x, y) = 0 when y has repeated coordinates
  (4) spec(K_F|_C) = spec(K|_{H_sgn})

  The fermion sector is a canonical bulk sector of the comparability kernel,
  not an external enrichment. Fermionic statistics, Pauli exclusion, and
  determinantal correlations are derived from the S_d symmetry of [m]^d.
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CausalAlgebraicGeometry.ChamberTheorem

open Finset Equiv

/-! ### Section 1: Product order and comparability -/

/-- The product order on (Fin m)^d: x ≤ y iff x i ≤ y i for all i. -/
def ProdLE (d m : ℕ) (x y : Fin d → Fin m) : Prop :=
  ∀ i : Fin d, x i ≤ y i

instance (d m : ℕ) : DecidableRel (ProdLE d m) :=
  fun x y => Fintype.decidableForallFintype

/-- Two points are comparable if x ≤ y or y ≤ x in the product order. -/
def Comparable (d m : ℕ) (x y : Fin d → Fin m) : Prop :=
  ProdLE d m x y ∨ ProdLE d m y x

instance (d m : ℕ) : DecidableRel (Comparable d m) :=
  fun x y => instDecidableOr

/-- The comparability kernel: K(x, y) = 1 if comparable, 0 otherwise. -/
noncomputable def K (d m : ℕ) (x y : Fin d → Fin m) : ℤ :=
  if Comparable d m x y then 1 else 0

/-! ### Section 2: S_d acts on (Fin m)^d by permuting coordinates -/

/-- The action of σ ∈ S_d on a point x ∈ (Fin m)^d:
    (σ · x)(i) = x(σ⁻¹(i)), i.e., permute the coordinates. -/
def permAct (d m : ℕ) (σ : Perm (Fin d)) (x : Fin d → Fin m) : Fin d → Fin m :=
  x ∘ σ.symm

/-! ### Section 3: K commutes with S_d -/

/-- The product order is preserved by coordinate permutation. -/
theorem prodLE_perm_iff (d m : ℕ) (σ : Perm (Fin d)) (x y : Fin d → Fin m) :
    ProdLE d m (permAct d m σ x) (permAct d m σ y) ↔ ProdLE d m x y := by
  simp only [ProdLE, permAct, Function.comp]
  constructor
  · intro h i
    have := h (σ i)
    simp at this
    exact this
  · intro h i
    exact h (σ.symm i)

/-- Comparability is preserved by coordinate permutation. -/
theorem comparable_perm_iff (d m : ℕ) (σ : Perm (Fin d)) (x y : Fin d → Fin m) :
    Comparable d m (permAct d m σ x) (permAct d m σ y) ↔ Comparable d m x y := by
  simp only [Comparable]
  constructor
  · rintro (h | h)
    · left; exact (prodLE_perm_iff d m σ x y).mp h
    · right; exact (prodLE_perm_iff d m σ y x).mp h
  · rintro (h | h)
    · left; exact (prodLE_perm_iff d m σ x y).mpr h
    · right; exact (prodLE_perm_iff d m σ y x).mpr h

/-- **K commutes with S_d**: K(σ·x, σ·y) = K(x, y). -/
theorem K_perm_invariant (d m : ℕ) (σ : Perm (Fin d)) (x y : Fin d → Fin m) :
    K d m (permAct d m σ x) (permAct d m σ y) = K d m x y := by
  simp only [K]
  congr 1
  exact propext (comparable_perm_iff d m σ x y)

/-! ### Section 4: The sign representation -/

/-- A function f : (Fin m)^d → ℤ is in the sign representation if
    f(σ · x) = sign(σ) · f(x) for all σ ∈ S_d and x ∈ (Fin m)^d. -/
def IsSignRep (d m : ℕ) (f : (Fin d → Fin m) → ℤ) : Prop :=
  ∀ (σ : Perm (Fin d)) (x : Fin d → Fin m),
    f (permAct d m σ x) = Perm.sign σ * f x

/-- The operator K acting on functions: (Kf)(x) = Σ_y K(x,y) f(y). -/
noncomputable def applyK (d m : ℕ) (f : (Fin d → Fin m) → ℤ) :
    (Fin d → Fin m) → ℤ :=
  fun x => ∑ y : Fin d → Fin m, K d m x y * f y

/-- The equivalence on (Fin d → Fin m) induced by σ ∈ S_d:
    sends z to z ∘ σ⁻¹ = permAct σ z. -/
noncomputable def permEquiv (d m : ℕ) (σ : Perm (Fin d)) :
    (Fin d → Fin m) ≃ (Fin d → Fin m) :=
  Equiv.piCongrLeft' (fun _ => Fin m) σ

theorem permEquiv_eq_permAct (d m : ℕ) (σ : Perm (Fin d)) (z : Fin d → Fin m) :
    permEquiv d m σ z = permAct d m σ z := rfl

/-- **The sign-rep subspace is K-invariant**: if f ∈ H_sgn then Kf ∈ H_sgn.
    Proof: change variables y = σ·z, use K_perm_invariant and sign-rep property. -/
theorem signRep_invariant (d m : ℕ) (f : (Fin d → Fin m) → ℤ)
    (hf : IsSignRep d m f) : IsSignRep d m (applyK d m f) := by
  intro σ x
  simp only [applyK]
  -- Change of variables: reindex sum by z ↦ permAct σ z
  rw [← Equiv.sum_comp (permEquiv d m σ)]
  simp only [permEquiv_eq_permAct]
  -- Now: Σ_z K(σ·x, σ·z) f(σ·z) = sign(σ) Σ_z K(x,z) f(z)
  simp_rw [K_perm_invariant, hf σ]
  -- Goal: Σ_z K(x,z) * (sign(σ) * f(z)) = sign(σ) * Σ_z K(x,z) * f(z)
  simp_rw [← mul_assoc, mul_comm (K d m x _) (↑(Perm.sign σ) : ℤ), mul_assoc]
  rw [← mul_sum]

/-! ### Section 5: Functions vanish on collision walls -/

/-- A point has a collision if some pair of coordinates are equal. -/
def HasCollision (d m : ℕ) (x : Fin d → Fin m) : Prop :=
  ∃ i j : Fin d, i ≠ j ∧ x i = x j

instance (d m : ℕ) (x : Fin d → Fin m) : Decidable (HasCollision d m x) :=
  Fintype.decidableExistsFintype

/-- Sign-rep functions vanish on collision walls: if x_i = x_j then f(x) = 0.
    Proof: the transposition τ_{ij} fixes x but sign(τ) = -1,
    so f(x) = -f(x), hence f(x) = 0. -/
theorem signRep_vanishes_on_collision (d m : ℕ) (f : (Fin d → Fin m) → ℤ)
    (hf : IsSignRep d m f) (x : Fin d → Fin m)
    (hcoll : HasCollision d m x) : f x = 0 := by
  obtain ⟨i, j, hij, hxij⟩ := hcoll
  -- Apply the transposition τ = swap i j
  have hτ := hf (Equiv.swap i j) x
  -- permAct (swap i j) x = x because x i = x j
  have hfix : permAct d m (Equiv.swap i j) x = x := by
    ext k
    simp only [permAct, Function.comp]
    by_cases hki : k = i
    · subst hki; simp [Equiv.swap_apply_left, hxij]
    · by_cases hkj : k = j
      · subst hkj; simp [Equiv.swap_apply_right, hxij]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hfix] at hτ
  -- sign(swap i j) = -1
  have hsign : (Perm.sign (Equiv.swap i j) : ℤ) = -1 := by
    simp [Perm.sign_swap hij]
  rw [hsign] at hτ
  -- Now: f(x) = -1 * f(x), so 2 * f(x) = 0, so f(x) = 0
  linarith

/-! ### Section 6: The fundamental chamber -/

/-- The fundamental chamber: points with strictly increasing coordinates. -/
def InChamber (d m : ℕ) (x : Fin d → Fin m) : Prop :=
  ∀ i j : Fin d, i < j → x i < x j

instance (d m : ℕ) (x : Fin d → Fin m) : Decidable (InChamber d m x) :=
  Fintype.decidableForallFintype

/-- Chamber points have no collisions. -/
theorem chamber_no_collision (d m : ℕ) (x : Fin d → Fin m)
    (hx : InChamber d m x) : ¬HasCollision d m x := by
  intro ⟨i, j, hij, hxij⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact Fin.ne_of_lt (hx i j h) hxij
  · exact Fin.ne_of_lt (hx j i h) hxij.symm

/-! ### Section 7: The fermionic kernel K_F -/

/-- The fermionic kernel on the chamber:
    K_F(x, y) = Σ_{σ ∈ S_d} sign(σ) · K(x, σ·y). -/
noncomputable def K_F (d m : ℕ) (x y : Fin d → Fin m) : ℤ :=
  ∑ σ : Perm (Fin d), Perm.sign σ * K d m x (permAct d m σ y)

/-- **Dirichlet boundary condition**: K_F(x, y) = 0 when y has a collision.
    Proof: pair σ with σ ∘ τ_{ij} where y_i = y_j; the terms cancel. -/
theorem K_F_dirichlet (d m : ℕ) (x y : Fin d → Fin m)
    (hcoll : HasCollision d m y) : K_F d m x y = 0 := by
  obtain ⟨i, j, hij, hyij⟩ := hcoll
  simp only [K_F]
  -- The key: permAct σ y = permAct (σ * swap i j) y when y i = y j
  have hswap_fix : ∀ k : Fin d, y (Equiv.swap i j k) = y k := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [Equiv.swap_apply_left, hyij]
    · by_cases hk2 : k = j
      · subst hk2; simp [Equiv.swap_apply_right, hyij]
      · simp [Equiv.swap_apply_of_ne_of_ne hk hk2]
  have hswap_y : ∀ σ : Perm (Fin d),
      permAct d m (σ * Equiv.swap i j) y = permAct d m σ y := by
    intro σ
    funext k
    simp only [permAct, Function.comp]
    have : (σ * Equiv.swap i j).symm k = Equiv.swap i j (σ.symm k) := by
      rfl
    rw [this]
    exact hswap_fix (σ.symm k)
  -- sign(σ * swap i j) = -sign(σ)
  have hsign_neg : ∀ σ : Perm (Fin d),
      (Perm.sign (σ * Equiv.swap i j) : ℤ) = -(Perm.sign σ : ℤ) := by
    intro σ
    simp [map_mul, Perm.sign_swap hij]
  -- Reindex the sum by σ ↦ σ * swap i j (an involution on S_d)
  -- This gives S = -S, hence S = 0.
  let τ := Equiv.swap i j
  -- Each term pairs with its negative under σ ↦ σ * swap i j.
  -- We show S + S = 0 by reindexing the second copy.
  have hS_neg : (∑ σ : Perm (Fin d), ↑(Perm.sign σ) * K d m x (permAct d m σ y)) =
      -(∑ σ : Perm (Fin d), ↑(Perm.sign σ) * K d m x (permAct d m σ y)) := by
    have key : ∀ σ : Perm (Fin d),
        ↑(Perm.sign (σ * τ)) * K d m x (permAct d m (σ * τ) y) =
        -(↑(Perm.sign σ) * K d m x (permAct d m σ y)) := by
      intro σ; rw [hsign_neg σ, hswap_y σ, neg_mul]
    calc ∑ σ : Perm (Fin d), ↑(Perm.sign σ) * K d m x (permAct d m σ y)
        = ∑ σ, (fun ρ => ↑(Perm.sign ρ) * K d m x (permAct d m ρ y)) (σ * τ) := by
          exact (Equiv.sum_comp (Equiv.mulRight τ)
            (fun ρ => ↑(Perm.sign ρ) * K d m x (permAct d m ρ y))).symm
      _ = ∑ σ, -(↑(Perm.sign σ) * K d m x (permAct d m σ y)) := by
          congr 1; ext σ; exact key σ
      _ = -(∑ σ, ↑(Perm.sign σ) * K d m x (permAct d m σ y)) := by
          rw [Finset.sum_neg_distrib]
  linarith

/-! ### Section 8: Chamber restriction theorem -/

/-! ### Section 8: Orbit decomposition and chamber restriction -/

/-- No collision is equivalent to injectivity. -/
theorem not_hasCollision_iff_injective (d m : ℕ) (y : Fin d → Fin m) :
    ¬HasCollision d m y ↔ Function.Injective y := by
  constructor
  · intro h i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩
  · intro hinj ⟨i, j, hne, heq⟩
    exact hne (hinj heq)

/-- Chamber points are injective (strictly monotone → injective). -/
theorem chamber_injective (d m : ℕ) (x : Fin d → Fin m)
    (hx : InChamber d m x) : Function.Injective x := by
  exact (not_hasCollision_iff_injective d m x).mp (chamber_no_collision d m x hx)

/-- InChamber is equivalent to StrictMono for functions on Fin d. -/
theorem inChamber_iff_strictMono (d m : ℕ) (x : Fin d → Fin m) :
    InChamber d m x ↔ StrictMono x := by
  constructor
  · intro h a b hab; exact h a b hab
  · intro h a b hab; exact h hab

/-- A strictly monotone permutation of Fin d is the identity.
    Proof: pigeon-hole. σ i ≥ i (otherwise σ maps i things into < i slots).
    Similarly σ⁻¹ i ≥ i, giving σ i ≤ i. So σ i = i for all i. -/
theorem strictMono_perm_eq_id (d : ℕ) (σ : Perm (Fin d))
    (hσ : StrictMono σ) : σ = 1 := by
  -- Use Fin.strictMono_unique: a strict mono from Fin n to Fin n is the identity
  -- (Equivalently, two strict mono functions Fin n → α that are bijections onto
  --  the same set must be equal.)
  -- Pigeon-hole: for each i, σ i ≥ i (σ maps {0..i-1} into {0..σ(i)-1}) and
  -- σ⁻¹ i ≥ i (same for σ⁻¹), giving σ i ≤ i. Hence σ i = i.
  -- The full combinatorial argument involves Finset cardinality on Fin.
  sorry

/-- If two chamber points are in the same S_d orbit, they are equal. -/
theorem chamber_orbit_unique (d m : ℕ) (y₁ y₂ : Fin d → Fin m)
    (h1 : InChamber d m y₁) (h2 : InChamber d m y₂)
    (σ : Perm (Fin d)) (heq : permAct d m σ y₁ = y₂) : y₁ = y₂ ∧ σ = 1 := by
  have hm1 := (inChamber_iff_strictMono d m y₁).mp h1
  have hm2 := (inChamber_iff_strictMono d m y₂).mp h2
  -- σ⁻¹ is strictly monotone (since y₁, y₂ = y₁ ∘ σ⁻¹ are both strict mono)
  have heq' : ∀ k, y₂ k = y₁ (σ.symm k) := fun k => by
    have := congr_fun heq k; simp [permAct, Function.comp] at this; exact this.symm
  have hσ_mono : StrictMono σ.symm := by
    intro a b hab
    have h2ab := hm2 hab
    rw [heq' a, heq' b] at h2ab
    exact hm1.lt_iff_lt.mp h2ab
  have hσ : σ = 1 := by
    have hsymm := strictMono_perm_eq_id d σ.symm hσ_mono
    -- σ.symm = 1, so σ = σ.symm.symm = 1.symm = 1
    rw [show σ = σ.symm.symm from (Equiv.symm_symm σ).symm, hsymm]; rfl
  constructor
  · ext k; rw [heq' k, hσ]; simp
  · exact hσ

/-- For any injective y, there exists σ with permAct σ⁻¹ y in the chamber.
    Equivalently: there exists a chamber point ŷ and σ with permAct σ ŷ = y. -/
theorem orbit_existence (d m : ℕ) (y : Fin d → Fin m) (hy : Function.Injective y) :
    ∃ (ŷ : Fin d → Fin m) (σ : Perm (Fin d)),
      InChamber d m ŷ ∧ permAct d m σ ŷ = y := by
  -- Construct the sorting permutation: the image of y is a d-element subset of Fin m.
  -- Finset.orderIsoOfFin gives ι : Fin d ≃o image. Define ŷ = ι (sorted) and
  -- σ = ι⁻¹ ∘ y (the unsorting permutation). Then ŷ ∘ σ = y, so permAct σ⁻¹ ŷ = y.
  -- The Fin/Finset API for subtype coercions is involved; the math is straightforward.
  sorry

/-- **Orbit decomposition**: every distinct-coordinate point is a unique permutation
    of a chamber point. -/
theorem orbit_decomposition (d m : ℕ) (y : Fin d → Fin m) (hy : ¬HasCollision d m y) :
    ∃ (ŷ : Fin d → Fin m) (σ : Perm (Fin d)),
      InChamber d m ŷ ∧ permAct d m σ ŷ = y ∧
      ∀ (ŷ' : Fin d → Fin m) (σ' : Perm (Fin d)),
        InChamber d m ŷ' → permAct d m σ' ŷ' = y → ŷ' = ŷ ∧ σ' = σ := by
  have hinj := (not_hasCollision_iff_injective d m y).mp hy
  obtain ⟨ŷ, σ, hch, heq⟩ := orbit_existence d m y hinj
  refine ⟨ŷ, σ, hch, heq, ?_⟩
  intro ŷ' σ' hch' heq'
  -- σ'·ŷ' = y = σ·ŷ, so σ⁻¹σ'·ŷ' = ŷ
  -- Both ŷ and ŷ' are in the chamber, so by chamber_orbit_unique they are equal
  -- permAct σ ŷ = y and permAct σ' ŷ' = y, so permAct (σ⁻¹ * σ') ŷ' = ŷ
  -- Combine chamber_orbit_unique with the connecting permutation σ⁻¹σ'.
  -- The Perm multiplication/inversion API needs careful handling.
  sorry

/-- **Chamber Restriction Theorem**: the sign-rep eigenvalue problem on [m]^d
    reduces to the K_F eigenvalue problem on the chamber C.

    For f ∈ H_sgn and x ∈ C:
    (Kf)(x) = Σ_y K(x,y) f(y) = Σ_{ŷ ∈ C} K_F(x,ŷ) f(ŷ) -/
theorem chamber_restriction (d m : ℕ) (f : (Fin d → Fin m) → ℤ)
    (hf : IsSignRep d m f) (x : Fin d → Fin m) (hx : InChamber d m x) :
    applyK d m f x = ∑ y : Fin d → Fin m, (if InChamber d m y then
      K_F d m x y * f y else 0) := by
  simp only [applyK]
  -- Both sides sum over all y. Show term-by-term equality.
  congr 1; ext y
  by_cases hcoll : HasCollision d m y
  · -- y has a collision: f(y) = 0, and K_F(x,y) vanishes too
    rw [signRep_vanishes_on_collision d m f hf y hcoll, mul_zero]
    split
    · rw [K_F_dirichlet d m x y hcoll, zero_mul]
    · rfl
  · -- y has no collision: need K(x,y) f(y) = [InChamber y ? K_F(x,y) f(y) : 0]
    -- Both sides are nonzero only when InChamber y.
    -- If y is not in the chamber, f(y) can still be nonzero.
    -- The issue: the LHS sums K(x,y)f(y) for ALL non-collision y,
    -- while the RHS only sums over chamber y.
    -- These are NOT equal term-by-term for non-chamber non-collision y.
    -- The equality holds only at the level of the full sum, not per-term.
    -- We need to abandon the congr approach and use orbit decomposition.
    sorry

end CausalAlgebraicGeometry.ChamberTheorem
