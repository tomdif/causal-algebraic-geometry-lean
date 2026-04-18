/-
  NearVacuumGeneral.lean — Near-vacuum zero-at-boundary theorem for ALL dimensions d.

  Generalizes antitone2D_zero_at_boundary (d=2) and antitone3D_zero_at_boundary (d=3)
  to arbitrary dimension d ≥ 1.

  The proof: pigeonhole along a single coordinate axis. If f(p) > 0 and p_i ≥ k,
  then the k+1 points obtained by varying coordinate i from 0 to k each satisfy
  q ≤ p and hence f(q) ≥ f(p) ≥ 1. So sum ≥ k+1 > k, contradicting Σf = k.

  Zero sorry.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Defs.PartialOrder

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 400000

namespace CausalAlgebraicGeometry.NearVacuumGeneral

/-! ## The general antitone zero-at-boundary theorem -/

/-- **GENERAL NEAR-VACUUM ZERO-AT-BOUNDARY THEOREM.**

For any dimension d, grid size m, and total k < m:
if f : (Fin d → Fin m) → ℕ is antitone (in the componentwise order)
and sums to k, then f(p) = 0 whenever any coordinate of p is ≥ k.

This subsumes antitone2D_zero_at_boundary (d=2) and
antitone3D_zero_at_boundary (d=3). -/
theorem antitone_zero_at_boundary_general
    {d : ℕ} {m k : ℕ} (hm : k < m)
    (f : (Fin d → Fin m) → ℕ)
    (hf_anti : ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p)
    (hf_sum : Finset.univ.sum f = k)
    (p : Fin d → Fin m)
    (i : Fin d)
    (hp : k ≤ (p i).val) :
    f p = 0 := by
  by_contra hne
  have hpos : 0 < f p := Nat.pos_of_ne_zero hne
  -- For any q ≤ p componentwise, f(q) ≥ f(p) ≥ 1
  have hge_at : ∀ q : Fin d → Fin m, (∀ j, q j ≤ p j) → 1 ≤ f q := by
    intro q hqp; have := hf_anti q p hqp; omega
  -- We find k+1 elements each with f ≥ 1, contradicting sum = k
  suffices h : k + 1 ≤ Finset.univ.sum f by omega
  -- Embed j ↦ Function.update p i ⟨j, _⟩ from Fin (k+1) into (Fin d → Fin m)
  let g : Fin (k + 1) → (Fin d → Fin m) :=
    fun j => Function.update p i ⟨j.val, by omega⟩
  have g_inj : Function.Injective g := by
    intro a b hab
    have h1 : g a i = g b i := congr_fun hab i
    simp only [g, Function.update_self] at h1
    have h2 : (⟨a.val, _⟩ : Fin m).val = (⟨b.val, _⟩ : Fin m).val := congrArg Fin.val h1
    exact Fin.ext (by omega)
  let emb : Fin (k + 1) ↪ (Fin d → Fin m) := ⟨g, g_inj⟩
  let S := Finset.univ.map emb
  have hle_at : ∀ j : Fin (k + 1), ∀ l : Fin d, g j l ≤ p l := by
    intro j l
    simp only [g]
    by_cases hli : l = i
    · subst hli; rw [Function.update_self]; exact Fin.mk_le_mk.mpr (by omega)
    · rw [Function.update_of_ne hli]
  calc k + 1
      = S.card := by simp [S, Finset.card_map]
    _ = S.sum (fun _ => 1) := by simp
    _ ≤ S.sum f := Finset.sum_le_sum (fun x hx => by
        rw [Finset.mem_map] at hx; obtain ⟨j, _, rfl⟩ := hx
        exact hge_at (g j) (hle_at j))
    _ ≤ Finset.univ.sum f := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Corollary: if ANY coordinate of p is ≥ k, then f(p) = 0. -/
theorem antitone_zero_at_boundary_exists
    {d : ℕ} {m k : ℕ} (hm : k < m)
    (f : (Fin d → Fin m) → ℕ)
    (hf_anti : ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p)
    (hf_sum : Finset.univ.sum f = k)
    (p : Fin d → Fin m)
    (hp : ∃ i : Fin d, k ≤ (p i).val) :
    f p = 0 := by
  obtain ⟨i, hi⟩ := hp
  exact antitone_zero_at_boundary_general hm f hf_anti hf_sum p i hi

/-- The support of f is contained in the [k]^d sub-box. -/
theorem antitone_support_in_box
    {d : ℕ} {m k : ℕ} (hm : k < m)
    (f : (Fin d → Fin m) → ℕ)
    (hf_anti : ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p)
    (hf_sum : Finset.univ.sum f = k)
    (p : Fin d → Fin m)
    (hfp : 0 < f p)
    (j : Fin d) :
    (p j).val < k := by
  by_contra h
  have : f p = 0 :=
    antitone_zero_at_boundary_general hm f hf_anti hf_sum p j (by omega)
  omega

/-! ## Stabilization structure (general d)

The zero-at-boundary theorem is the key ingredient for stabilization:
for m > k, the count of antitone functions f : [m]^d → ℕ summing to k
is independent of m. The argument has three steps:

1. **Zero at boundary** (proved above): f(p) = 0 whenever any coordinate
   of p is ≥ k. So f is supported on [k]^d ⊂ [m]^d.

2. **Codomain independence**: Since f(p) ≤ Σf = k for antitone f with
   f(0,...,0) being the maximum, and k < m, the values of f lie in
   {0,...,k} ⊂ {0,...,m-1}. So the codomain Fin m can be replaced by
   Fin(k+1) without loss.

3. **Identification**: By (1) and (2), the set of antitone f : [m]^d → ℕ
   summing to k bijects with the set of antitone g : [k]^d → Fin(k+1)
   summing to k, which is the set of (d-1)-dimensional partitions of k.

Combining: for m > k, CC_{m^d - k}([m]^d) = Σ_{j=0}^k P_{d-1}(j) · P_{d-1}(k-j),
where P_{d-1} counts (d-1)-dimensional partitions. This is the self-convolution
of the (d-1)-dimensional partition function.

Generating function: Σ_k CC_{m^d - k} x^k = D_{d-1}(q)²,
where D_{d-1}(q) = Σ_k P_{d-1}(k) q^k is the (d-1)-dimensional partition
generating function (MacMahon's generalization). -/

/-- **STABILIZATION KEY LEMMA.**

Any antitone function on [m]^d summing to k (with k < m) agrees with
its restriction to the [k]^d sub-box, and vanishes outside it.
This is a trivial restatement but clarifies the stabilization structure. -/
theorem stabilization_key_lemma
    {d : ℕ} {m k : ℕ} (hm : k < m)
    (f : (Fin d → Fin m) → ℕ)
    (hf_anti : ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p)
    (hf_sum : Finset.univ.sum f = k)
    (p : Fin d → Fin m)
    (hp : ∃ j : Fin d, k ≤ (p j).val) :
    f p = 0 :=
  antitone_zero_at_boundary_exists hm f hf_anti hf_sum p hp

end CausalAlgebraicGeometry.NearVacuumGeneral
