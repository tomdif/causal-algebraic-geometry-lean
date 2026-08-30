/-
  DivisibilityRenormalization.lean — The renormalization theorem for
  order-convex subsets of the divisibility poset (OEIS A394685).

  Let convCount U be the number of divisibility-convex subsets of a finite
  universe U ⊆ ℕ, and write a(n) = convCount (Icc 1 n) (= A394685(n)) and
  c_k(n) = convCount (Icc k n).

  MAIN RESULT (zero sorry), Theorem 1 of docs/DivisibilityRenormalization.md,
  in cross-multiplied form:

    renormalization : for 1 ≤ k, p prime, k ≤ p,
      c_k(kp) · a(k-1) = c_k(kp-1) · a(k)

  i.e. c_k(kp)/c_k(kp-1) = a(k)/a(k-1): multiplying the ambient scale by a
  large prime reproduces the ratio function of A394685 at the cofactor.
  The case k = 1 recovers the prime-doubling theorem of DivisibilityPoset.lean
  (derived below as `prime_doubling_of_renormalization`).

  Proof architecture:
    * convCount_insert_top — adjoining a maximal element t to a universe U
      adds topCount U t sets, where topCount counts convex sets satisfying the
      up-set condition on the divisors of t.
    * card_filter_image / isConvexIn_image_iff / topCond_image_iff —
      j ↦ j·p is a divisibility-poset isomorphism, so both counts transfer
      from Icc 1 (k-1) to its scaled copy C = (Icc 1 (k-1)).image (·*p).
    * card_filter_union / isConvexIn_union_iff / topCond_union_iff —
      if no divisibility relation crosses between C and R, convex counting
      decouples multiplicatively, and the top condition only constrains C.
    * copy_subset / mem_copy_of_p_dvd / copy_sep / copy_top_trivial —
      the arithmetic facts making C order-isolated inside P = Icc k (kp-1),
      with the divisors of kp in R imposing no condition (they are covered).
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CausalAlgebraicGeometry.DivisibilityRenormalization

open Finset

/-- `S` is divisibility-convex inside the universe `U`: it lies in `U` and is
    closed under divisibility intervals taken within `U`. -/
def IsConvexIn (U S : Finset ℕ) : Prop :=
  S ⊆ U ∧ ∀ a ∈ S, ∀ b ∈ S, a ∣ b → ∀ c ∈ U, a ∣ c → c ∣ b → c ∈ S

/-- The up-set condition governing whether `S ∪ {t}` stays convex after a
    maximal element `t` is adjoined to the universe: on the divisors of `t`
    inside `U`, `S` must be upward closed towards `t`. -/
def TopCond (U : Finset ℕ) (t : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, a ∣ t → ∀ c ∈ U, a ∣ c → c ∣ t → c ∈ S

noncomputable instance (U S : Finset ℕ) : Decidable (IsConvexIn U S) :=
  Classical.propDecidable _

noncomputable instance (U : Finset ℕ) (t : ℕ) (S : Finset ℕ) :
    Decidable (TopCond U t S) :=
  Classical.propDecidable _

/-- Number of divisibility-convex subsets of the universe `U`.
    `convCount (Icc 1 n)` is OEIS A394685(n). -/
noncomputable def convCount (U : Finset ℕ) : ℕ :=
  (U.powerset.filter (fun S => IsConvexIn U S)).card

/-- Number of convex subsets of `U` additionally satisfying the up-set
    condition for a prospective top element `t`. -/
noncomputable def topCount (U : Finset ℕ) (t : ℕ) : ℕ :=
  (U.powerset.filter (fun S => IsConvexIn U S ∧ TopCond U t S)).card

/-! ## Divisibility cancellation helpers -/

lemma mul_dvd_mul_iff_right' {a b m : ℕ} (hm : 0 < m) :
    a * m ∣ b * m ↔ a ∣ b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h : b * m = a * c * m := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_right hm h
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩

lemma mul_dvd_mul_iff_left' {a b m : ℕ} (hm : 0 < m) :
    m * a ∣ m * b ↔ a ∣ b := by
  rw [mul_comm m a, mul_comm m b]
  exact mul_dvd_mul_iff_right' hm

/-! ## Adjoining a maximal element -/

/-- Removing a top element from the universe preserves convexity. -/
theorem convex_restrict {U S : Finset ℕ} {t : ℕ} (htS : t ∉ S)
    (h : IsConvexIn (insert t U) S) : IsConvexIn U S := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp (h.1 hx) with rfl | hxU
    · exact absurd hx htS
    · exact hxU
  · intro a ha b hb hab c hcU hac hcb
    exact h.2 a ha b hb hab c (mem_insert_of_mem hcU) hac hcb

/-- Enlarging the universe by a maximal element preserves convexity: the new
    element cannot appear strictly inside a divisibility interval. -/
theorem convex_extend {U S : Finset ℕ} {t : ℕ}
    (hmax : ∀ y ∈ U, ¬ t ∣ y) (h : IsConvexIn U S) :
    IsConvexIn (insert t U) S := by
  refine ⟨fun x hx => mem_insert_of_mem (h.1 hx), ?_⟩
  intro a ha b hb hab c hcU hac hcb
  rcases mem_insert.mp hcU with rfl | hcU'
  · exact absurd hcb (hmax b (h.1 hb))
  · exact h.2 a ha b hb hab c hcU' hac hcb

/-- Characterization of convexity of `insert t S` when `t` is maximal over the
    universe: it is convexity of `S` plus the up-set condition towards `t`. -/
theorem insertTop_iff {U S : Finset ℕ} {t : ℕ} (htU : t ∉ U)
    (hmax : ∀ y ∈ U, ¬ t ∣ y) (hSU : S ⊆ U) :
    IsConvexIn (insert t U) (insert t S) ↔ IsConvexIn U S ∧ TopCond U t S := by
  constructor
  · intro h
    refine ⟨⟨hSU, ?_⟩, ?_⟩
    · intro a ha b hb hab c hcU hac hcb
      have hc' : c ∈ insert t S :=
        h.2 a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab c
          (mem_insert_of_mem hcU) hac hcb
      rcases mem_insert.mp hc' with rfl | hcS
      · exact absurd hcU htU
      · exact hcS
    · intro a ha hat c hcU hac hct
      have hc' : c ∈ insert t S :=
        h.2 a (mem_insert_of_mem ha) t (mem_insert_self t S) hat c
          (mem_insert_of_mem hcU) hac hct
      rcases mem_insert.mp hc' with rfl | hcS
      · exact absurd hcU htU
      · exact hcS
  · rintro ⟨hconv, htop⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hxS
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (hSU hxS)
    · intro a ha b hb hab c hcU hac hcb
      rcases mem_insert.mp hcU with rfl | hcU'
      · exact mem_insert_self _ _
      · rcases mem_insert.mp ha with rfl | haS
        · exact absurd hac (hmax c hcU')
        · rcases mem_insert.mp hb with rfl | hbS
          · exact mem_insert_of_mem (htop a haS hab c hcU' hac hcb)
          · exact mem_insert_of_mem (hconv.2 a haS b hbS hab c hcU' hac hcb)

/-- **Top-adjunction counting.** Adjoining a maximal element `t` to a universe
    `U` splits the convex count as `convCount U + topCount U t`: sets omitting
    `t` are unconstrained, sets containing `t` must satisfy the up-set
    condition on the divisors of `t`. -/
theorem convCount_insert_top {U : Finset ℕ} {t : ℕ} (htU : t ∉ U)
    (hmax : ∀ y ∈ U, ¬ t ∣ y) :
    convCount (insert t U) = convCount U + topCount U t := by
  unfold convCount topCount
  set Pp := (insert t U).powerset.filter
    (fun S => IsConvexIn (insert t U) S) with hPp_def
  have hsplit : Pp.card =
      (Pp.filter (fun S => t ∈ S)).card + (Pp.filter (fun S => t ∉ S)).card :=
    (Finset.card_filter_add_card_filter_not (s := Pp)
      (p := fun S : Finset ℕ => t ∈ S)).symm
  have h_without : (Pp.filter (fun S => t ∉ S)).card =
      (U.powerset.filter (fun S => IsConvexIn U S)).card := by
    apply Finset.card_bij (fun S _ => S)
    · intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hS1, htS⟩ := hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS1
      obtain ⟨hsub, hconv⟩ := hS1
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, convex_restrict htS hconv⟩
      intro x hx
      rcases mem_insert.mp (hsub hx) with rfl | hxU
      · exact absurd hx htS
      · exact hxU
    · intro S₁ _ S₂ _ h
      exact h
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨hsub, hconv⟩ := hS
      have htS : t ∉ S := fun ht => htU (hsub ht)
      refine ⟨S, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨?_, htS⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hsub.trans (Finset.subset_insert t U), convex_extend hmax hconv⟩
  have h_with : (Pp.filter (fun S => t ∈ S)).card =
      (U.powerset.filter (fun S => IsConvexIn U S ∧ TopCond U t S)).card := by
    apply Finset.card_bij (fun S _ => S.erase t)
    · intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hS1, htS⟩ := hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS1
      obtain ⟨hsub, hconv⟩ := hS1
      have hsub' : S.erase t ⊆ U := by
        intro x hx
        rw [Finset.mem_erase] at hx
        rcases mem_insert.mp (hsub hx.2) with h | h
        · exact absurd h hx.1
        · exact h
      have hS_eq : S = insert t (S.erase t) := (Finset.insert_erase htS).symm
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hsub', ?_⟩
      rw [← insertTop_iff htU hmax hsub', ← hS_eq]
      exact hconv
    · intro S₁ h₁ S₂ h₂ h
      rw [Finset.mem_filter] at h₁ h₂
      have e₁ : S₁ = insert t (S₁.erase t) := (Finset.insert_erase h₁.2).symm
      have e₂ : S₂ = insert t (S₂.erase t) := (Finset.insert_erase h₂.2).symm
      rw [e₁, h]
      exact e₂.symm
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      obtain ⟨hsub, hconv, htop⟩ := hT
      have htT : t ∉ T := fun ht => htU (hsub ht)
      refine ⟨insert t T, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, mem_insert_self _ _⟩
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset_insert t hsub,
          (insertTop_iff htU hmax hsub).mpr ⟨hconv, htop⟩⟩
      · exact Finset.erase_insert htT
  rw [hsplit, h_with, h_without]
  exact Nat.add_comm _ _

/-! ## Transfer along the scaling map j ↦ j·m -/

/-- Multiplication by a fixed positive `m` is a divisibility-poset isomorphism
    onto its image, so convexity transfers both ways. -/
theorem isConvexIn_image_iff {U S : Finset ℕ} {m : ℕ} (hm : 0 < m)
    (hSU : S ⊆ U) :
    IsConvexIn U S ↔ IsConvexIn (U.image (· * m)) (S.image (· * m)) := by
  constructor
  · intro h
    refine ⟨Finset.image_subset_image h.1, ?_⟩
    intro a' ha' b' hb' hab c' hc' hac hcb
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨c, hcU, rfl⟩ := Finset.mem_image.mp hc'
    rw [mul_dvd_mul_iff_right' hm] at hab hac hcb
    exact Finset.mem_image_of_mem _ (h.2 a haS b hbS hab c hcU hac hcb)
  · intro h
    refine ⟨hSU, ?_⟩
    intro a haS b hbS hab c hcU hac hcb
    have h' := h.2 (a * m) (Finset.mem_image_of_mem _ haS) (b * m)
      (Finset.mem_image_of_mem _ hbS) ((mul_dvd_mul_iff_right' hm).mpr hab)
      (c * m) (Finset.mem_image_of_mem _ hcU)
      ((mul_dvd_mul_iff_right' hm).mpr hac)
      ((mul_dvd_mul_iff_right' hm).mpr hcb)
    obtain ⟨c₀, hc₀S, hc₀⟩ := Finset.mem_image.mp h'
    have hc : c₀ = c := Nat.eq_of_mul_eq_mul_right hm hc₀
    rw [← hc]
    exact hc₀S

/-- The top condition transfers along the scaling map (with the prospective
    top scaled accordingly). -/
theorem topCond_image_iff {U S : Finset ℕ} {t m : ℕ} (hm : 0 < m) :
    TopCond U t S ↔ TopCond (U.image (· * m)) (t * m) (S.image (· * m)) := by
  constructor
  · intro h a' ha' hat c' hc' hac hct
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨c, hcU, rfl⟩ := Finset.mem_image.mp hc'
    rw [mul_dvd_mul_iff_right' hm] at hat hac hct
    exact Finset.mem_image_of_mem _ (h a haS hat c hcU hac hct)
  · intro h a haS hat c hcU hac hct
    have h' := h (a * m) (Finset.mem_image_of_mem _ haS)
      ((mul_dvd_mul_iff_right' hm).mpr hat) (c * m)
      (Finset.mem_image_of_mem _ hcU)
      ((mul_dvd_mul_iff_right' hm).mpr hac)
      ((mul_dvd_mul_iff_right' hm).mpr hct)
    obtain ⟨c₀, hc₀S, hc₀⟩ := Finset.mem_image.mp h'
    have hc : c₀ = c := Nat.eq_of_mul_eq_mul_right hm hc₀
    rw [← hc]
    exact hc₀S

/-- Generic filtered-powerset counting along the scaling bijection. -/
theorem card_filter_image {U : Finset ℕ} {m : ℕ} (hm : 0 < m)
    {Q Q' : Finset ℕ → Prop} [DecidablePred Q] [DecidablePred Q']
    (hQ : ∀ S, S ⊆ U → (Q S ↔ Q' (S.image (· * m)))) :
    (U.powerset.filter Q).card =
      ((U.image (· * m)).powerset.filter Q').card := by
  have hinj : Function.Injective (· * m) :=
    fun a b h => Nat.eq_of_mul_eq_mul_right hm h
  apply Finset.card_bij (fun S _ => S.image (· * m))
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨Finset.image_subset_image hS.1, (hQ S hS.1).mp hS.2⟩
  · intro S₁ h₁ S₂ h₂ heq
    exact Finset.image_injective hinj heq
  · intro S' hS'
    rw [Finset.mem_filter, Finset.mem_powerset] at hS'
    obtain ⟨hsub', hq'⟩ := hS'
    have hpre_sub : U.filter (fun u => u * m ∈ S') ⊆ U :=
      Finset.filter_subset _ _
    have himg : (U.filter (fun u => u * m ∈ S')).image (· * m) = S' := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨u, ⟨_, huS⟩, rfl⟩
        exact huS
      · intro hy
        obtain ⟨u, huU, hu_eq⟩ := Finset.mem_image.mp (hsub' hy)
        exact ⟨u, ⟨huU, by rw [hu_eq]; exact hy⟩, hu_eq⟩
    refine ⟨U.filter (fun u => u * m ∈ S'), ?_, himg⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hpre_sub, (hQ _ hpre_sub).mpr ?_⟩
    rw [himg]
    exact hq'

/-! ## Decoupling over an order-isolated component -/

/-- If no divisibility relation crosses between `C` and `R`, convexity in
    `C ∪ R` splits into independent convexity of the two halves. -/
theorem isConvexIn_union_iff {C R S : Finset ℕ}
    (hsep : ∀ x ∈ C, ∀ y ∈ R, ¬ x ∣ y ∧ ¬ y ∣ x) (hS : S ⊆ C ∪ R) :
    IsConvexIn (C ∪ R) S ↔ IsConvexIn C (S ∩ C) ∧ IsConvexIn R (S ∩ R) := by
  constructor
  · intro h
    refine ⟨⟨Finset.inter_subset_right, ?_⟩, ⟨Finset.inter_subset_right, ?_⟩⟩
    · intro a ha b hb hab c hcC hac hcb
      rw [Finset.mem_inter] at ha hb
      exact Finset.mem_inter.mpr
        ⟨h.2 a ha.1 b hb.1 hab c (Finset.mem_union_left R hcC) hac hcb, hcC⟩
    · intro a ha b hb hab c hcR hac hcb
      rw [Finset.mem_inter] at ha hb
      exact Finset.mem_inter.mpr
        ⟨h.2 a ha.1 b hb.1 hab c (Finset.mem_union_right C hcR) hac hcb, hcR⟩
  · rintro ⟨hC, hR⟩
    refine ⟨hS, ?_⟩
    intro a ha b hb hab c hcU hac hcb
    rcases Finset.mem_union.mp (hS ha) with haC | haR
    · have hbC : b ∈ C := by
        rcases Finset.mem_union.mp (hS hb) with h' | h'
        · exact h'
        · exact absurd hab (hsep a haC b h').1
      have hcC : c ∈ C := by
        rcases Finset.mem_union.mp hcU with h' | h'
        · exact h'
        · exact absurd hac (hsep a haC c h').1
      have hmem := hC.2 a (Finset.mem_inter.mpr ⟨ha, haC⟩) b
        (Finset.mem_inter.mpr ⟨hb, hbC⟩) hab c hcC hac hcb
      exact (Finset.mem_inter.mp hmem).1
    · have hbR : b ∈ R := by
        rcases Finset.mem_union.mp (hS hb) with h' | h'
        · exact absurd hab (hsep b h' a haR).2
        · exact h'
      have hcR : c ∈ R := by
        rcases Finset.mem_union.mp hcU with h' | h'
        · exact absurd hac (hsep c h' a haR).2
        · exact h'
      have hmem := hR.2 a (Finset.mem_inter.mpr ⟨ha, haR⟩) b
        (Finset.mem_inter.mpr ⟨hb, hbR⟩) hab c hcR hac hcb
      exact (Finset.mem_inter.mp hmem).1

/-- If additionally every divisor of `t` in `R` is covered (any `c` between it
    and `t` equals it), the top condition only constrains the `C` half. -/
theorem topCond_union_iff {C R S : Finset ℕ} {t : ℕ}
    (hsep : ∀ x ∈ C, ∀ y ∈ R, ¬ x ∣ y ∧ ¬ y ∣ x)
    (hRtriv : ∀ a ∈ R, a ∣ t → ∀ c ∈ C ∪ R, a ∣ c → c ∣ t → c = a)
    (hS : S ⊆ C ∪ R) :
    TopCond (C ∪ R) t S ↔ TopCond C t (S ∩ C) := by
  constructor
  · intro h a ha hat c hcC hac hct
    rw [Finset.mem_inter] at ha
    exact Finset.mem_inter.mpr
      ⟨h a ha.1 hat c (Finset.mem_union_left R hcC) hac hct, hcC⟩
  · intro h a ha hat c hcU hac hct
    rcases Finset.mem_union.mp (hS ha) with haC | haR
    · rcases Finset.mem_union.mp hcU with hcC | hcR
      · exact (Finset.mem_inter.mp
          (h a (Finset.mem_inter.mpr ⟨ha, haC⟩) hat c hcC hac hct)).1
      · exact absurd hac (hsep a haC c hcR).1
    · have hca : c = a := hRtriv a haR hat c hcU hac hct
      rw [hca]
      exact ha

/-- Generic filtered-powerset counting over a separated union: the count over
    `C ∪ R` is the product of the counts over the halves. -/
theorem card_filter_union {C R : Finset ℕ} (hdisj : Disjoint C R)
    {Q QC QR : Finset ℕ → Prop}
    [DecidablePred Q] [DecidablePred QC] [DecidablePred QR]
    (hQ : ∀ S, S ⊆ C ∪ R → (Q S ↔ QC (S ∩ C) ∧ QR (S ∩ R))) :
    ((C ∪ R).powerset.filter Q).card =
      (C.powerset.filter QC).card * (R.powerset.filter QR).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun S _ => (S ∩ C, S ∩ R))
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hsub, hq⟩ := hS
    rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, ((hQ S hsub).mp hq).1⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, ((hQ S hsub).mp hq).2⟩
  · intro S₁ hS₁ S₂ hS₂ heq
    rw [Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
    have e1 : S₁ ∩ C = S₂ ∩ C := congrArg Prod.fst heq
    have e2 : S₁ ∩ R = S₂ ∩ R := congrArg Prod.snd heq
    have r1 : S₁ = S₁ ∩ C ∪ S₁ ∩ R := by
      rw [← Finset.inter_union_distrib_left,
        Finset.inter_eq_left.mpr hS₁.1]
    have r2 : S₂ = S₂ ∩ C ∪ S₂ ∩ R := by
      rw [← Finset.inter_union_distrib_left,
        Finset.inter_eq_left.mpr hS₂.1]
    rw [r1, e1, e2]
    exact r2.symm
  · intro pr hpr
    rw [Finset.mem_product] at hpr
    obtain ⟨h1, h2⟩ := hpr
    rw [Finset.mem_filter, Finset.mem_powerset] at h1 h2
    have hsub : pr.1 ∪ pr.2 ⊆ C ∪ R :=
      Finset.union_subset_union h1.1 h2.1
    have hCpart : (pr.1 ∪ pr.2) ∩ C = pr.1 := by
      have e2 : pr.2 ∩ C = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp (hdisj.symm.mono_left h2.1)
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h1.1,
        e2, Finset.union_empty]
    have hRpart : (pr.1 ∪ pr.2) ∩ R = pr.2 := by
      have e1 : pr.1 ∩ R = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp (hdisj.mono_left h1.1)
      rw [Finset.union_inter_distrib_right, e1,
        Finset.inter_eq_left.mpr h2.1, Finset.empty_union]
    refine ⟨pr.1 ∪ pr.2, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hsub, (hQ _ hsub).mpr ?_⟩
      rw [hCpart, hRpart]
      exact ⟨h1.2, h2.2⟩
    · rw [hCpart, hRpart]

/-! ## The arithmetic of the scaled copy C = {jp : 1 ≤ j ≤ k-1} inside
    P = {k, ..., kp-1} -/

/-- The scaled copy sits inside `P`: `jp ≥ p ≥ k` and `jp ≤ (k-1)p ≤ kp - 1`. -/
lemma copy_subset {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k ≤ p) :
    (Icc 1 (k - 1)).image (· * p) ⊆ Icc k (k * p - 1) := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Icc] at hj ⊢
  obtain ⟨hj1, hj2⟩ := hj
  have hp2 : 2 ≤ p := hp.two_le
  constructor
  · calc k ≤ p := hkp
      _ ≤ j * p := Nat.le_mul_of_pos_left p (by omega)
  · have h1 : j * p ≤ (k - 1) * p := Nat.mul_le_mul_right p hj2
    have h2 : (k - 1) * p + p = k * p := by
      have h3 : (k - 1 + 1) * p = k * p := by rw [Nat.sub_add_cancel hk]
      rw [add_mul, one_mul] at h3
      omega
    omega

/-- Every multiple of `p` in `P` lies in the scaled copy: this is where
    `p ≥ k` enters (the quotient is forced below `k`). -/
lemma mem_copy_of_p_dvd {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k ≤ p)
    {y : ℕ} (hy : y ∈ Icc k (k * p - 1)) (hdvd : p ∣ y) :
    y ∈ (Icc 1 (k - 1)).image (· * p) := by
  rw [Finset.mem_Icc] at hy
  obtain ⟨i, rfl⟩ := hdvd
  have hppos : 0 < p := hp.pos
  have hkppos : 0 < k * p := Nat.mul_pos (by omega) hppos
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [Nat.mul_zero] at hy
      omega
    · exact hi
  have hik : i < k := by
    have h1 : p * i < k * p := by omega
    rw [mul_comm p i] at h1
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le p)
  rw [Finset.mem_image]
  exact ⟨i, Finset.mem_Icc.mpr ⟨hi1, by omega⟩, mul_comm i p⟩

/-- **Order isolation.** No divisibility relation crosses between the scaled
    copy and its complement in `P`: a multiple of an element of `C` in `P` is
    again a multiple of `p` (hence in `C`), and a divisor either keeps the
    factor `p` (hence is in `C`) or divides the cofactor `j < k`, which is too
    small to lie in `P`. -/
lemma copy_sep {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k ≤ p) :
    ∀ x ∈ (Icc 1 (k - 1)).image (· * p),
      ∀ y ∈ Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p),
        ¬ x ∣ y ∧ ¬ y ∣ x := by
  intro x hx y hy
  rw [Finset.mem_sdiff] at hy
  obtain ⟨hyP, hyC⟩ := hy
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Icc] at hj
  constructor
  · intro hdvd
    exact hyC (mem_copy_of_p_dvd hk hp hkp hyP
      (dvd_trans (dvd_mul_left p j) hdvd))
  · intro hdvd
    by_cases hpy : p ∣ y
    · exact hyC (mem_copy_of_p_dvd hk hp hkp hyP hpy)
    · have hcop : Nat.Coprime y p :=
        ((hp.coprime_iff_not_dvd).mpr hpy).symm
      have hyj : y ∣ j := hcop.dvd_of_dvd_mul_right hdvd
      have hy_le : y ≤ j := Nat.le_of_dvd (by omega) hyj
      rw [Finset.mem_Icc] at hyP
      omega

/-- **Covered divisors in R.** Any divisor of `kp` lying in `R = P \ C` equals
    `k`, and `k` is covered by `kp`: the only `c ∈ P` with `k ∣ c ∣ kp` is `k`
    itself (the cofactor divides the prime `p` and cannot be `p`). Hence the
    top condition imposes nothing on the `R` half. -/
lemma copy_top_trivial {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k ≤ p) :
    ∀ a ∈ Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p),
      a ∣ k * p →
        ∀ c ∈ (Icc 1 (k - 1)).image (· * p) ∪
            (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p)),
          a ∣ c → c ∣ k * p → c = a := by
  intro a ha hat c hc hac hct
  rw [Finset.mem_sdiff] at ha
  obtain ⟨haP, haC⟩ := ha
  have hak : a = k := by
    by_cases hpa : p ∣ a
    · exact absurd (mem_copy_of_p_dvd hk hp hkp haP hpa) haC
    · have hcop : Nat.Coprime a p :=
        ((hp.coprime_iff_not_dvd).mpr hpa).symm
      have hax : a ∣ k := hcop.dvd_of_dvd_mul_right hat
      have h1 : a ≤ k := Nat.le_of_dvd (by omega) hax
      rw [Finset.mem_Icc] at haP
      omega
  subst hak
  have hcP : c ∈ Icc a (a * p - 1) := by
    rcases Finset.mem_union.mp hc with h | h
    · exact copy_subset hk hp hkp h
    · exact (Finset.mem_sdiff.mp h).1
  rw [Finset.mem_Icc] at hcP
  obtain ⟨n, rfl⟩ := hac
  have hnp : n ∣ p := (mul_dvd_mul_iff_left' (show 0 < a by omega)).mp hct
  rcases (Nat.dvd_prime hp).mp hnp with rfl | rfl
  · exact mul_one a
  · exfalso
    have h1 : 0 < a * n := Nat.mul_pos (by omega) hp.pos
    omega

/-! ## The renormalization theorem -/

/-- **Theorem 1 (exact self-similarity), cross-multiplied form.** For `k ≥ 1`
    and a prime `p ≥ k`,

      c_k(kp) · a(k-1) = c_k(kp-1) · a(k),

    where `a(n) = convCount (Icc 1 n)` (= A394685) and
    `c_k(n) = convCount (Icc k n)`. Equivalently,
    `c_k(kp)/c_k(kp-1) = a(k)/a(k-1) = r(k)`: the convex-set statistics of the
    divisibility poset are scale-free under multiplication by a large prime. -/
theorem renormalization {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k ≤ p) :
    convCount (Icc k (k * p)) * convCount (Icc 1 (k - 1)) =
      convCount (Icc k (k * p - 1)) * convCount (Icc 1 k) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : 0 < p := hp.pos
  have hkppos : 0 < k * p := Nat.mul_pos (by omega) hppos
  have hkkp : k ≤ k * p := Nat.le_mul_of_pos_right k hppos
  have hCP := copy_subset hk hp hkp
  have hunion : (Icc 1 (k - 1)).image (· * p) ∪
      (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p)) =
      Icc k (k * p - 1) := Finset.union_sdiff_of_subset hCP
  have hdisj : Disjoint ((Icc 1 (k - 1)).image (· * p))
      (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p)) :=
    Finset.disjoint_sdiff
  have hsep := copy_sep hk hp hkp
  have hRtriv := copy_top_trivial hk hp hkp
  -- decoupling of the plain convex count over P = C ∪ R
  have h1 : convCount ((Icc 1 (k - 1)).image (· * p) ∪
      (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p))) =
      convCount ((Icc 1 (k - 1)).image (· * p)) *
        convCount (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p)) := by
    unfold convCount
    exact card_filter_union hdisj
      (fun S hS => isConvexIn_union_iff hsep hS)
  -- decoupling of the top-conditioned count over P = C ∪ R
  have h2 : topCount ((Icc 1 (k - 1)).image (· * p) ∪
      (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p))) (k * p) =
      topCount ((Icc 1 (k - 1)).image (· * p)) (k * p) *
        convCount (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p)) := by
    unfold topCount convCount
    refine card_filter_union hdisj (fun S hS => ?_)
    constructor
    · rintro ⟨hc, ht⟩
      exact ⟨⟨((isConvexIn_union_iff hsep hS).mp hc).1,
        (topCond_union_iff hsep hRtriv hS).mp ht⟩,
        ((isConvexIn_union_iff hsep hS).mp hc).2⟩
    · rintro ⟨⟨hcC, htC⟩, hcR⟩
      exact ⟨(isConvexIn_union_iff hsep hS).mpr ⟨hcC, hcR⟩,
        (topCond_union_iff hsep hRtriv hS).mpr htC⟩
  -- transfer both counts from Icc 1 (k-1) to the scaled copy
  have h3 : convCount (Icc 1 (k - 1)) =
      convCount ((Icc 1 (k - 1)).image (· * p)) := by
    unfold convCount
    exact card_filter_image hppos
      (fun S hS => isConvexIn_image_iff hppos hS)
  have h4 : topCount (Icc 1 (k - 1)) k =
      topCount ((Icc 1 (k - 1)).image (· * p)) (k * p) := by
    unfold topCount
    refine card_filter_image hppos (fun S hS => ?_)
    constructor
    · rintro ⟨hc, ht⟩
      exact ⟨(isConvexIn_image_iff hppos hS).mp hc,
        (topCond_image_iff hppos).mp ht⟩
    · rintro ⟨hc, ht⟩
      exact ⟨(isConvexIn_image_iff hppos hS).mpr hc,
        (topCond_image_iff hppos).mpr ht⟩
  -- insert-top at scale k : a(k) = a(k-1) + topCount
  have hins_k : Icc 1 k = insert k (Icc 1 (k - 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h5 : convCount (Icc 1 k) =
      convCount (Icc 1 (k - 1)) + topCount (Icc 1 (k - 1)) k := by
    rw [hins_k]
    apply convCount_insert_top
    · simp only [Finset.mem_Icc]
      omega
    · intro y hy hdvd
      rw [Finset.mem_Icc] at hy
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  -- insert-top at scale kp : c_k(kp) = c_k(kp-1) + topCount
  have hins_kp : Icc k (k * p) = insert (k * p) (Icc k (k * p - 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h6 : convCount (Icc k (k * p)) =
      convCount (Icc k (k * p - 1)) + topCount (Icc k (k * p - 1)) (k * p) := by
    rw [hins_kp]
    apply convCount_insert_top
    · simp only [Finset.mem_Icc]
      omega
    · intro y hy hdvd
      rw [Finset.mem_Icc] at hy
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  -- assemble
  rw [hunion] at h1 h2
  have e1 : convCount (Icc k (k * p - 1)) =
      convCount (Icc 1 (k - 1)) *
        convCount (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p)) := by
    rw [h1, ← h3]
  have e2 : topCount (Icc k (k * p - 1)) (k * p) =
      topCount (Icc 1 (k - 1)) k *
        convCount (Icc k (k * p - 1) \ (Icc 1 (k - 1)).image (· * p)) := by
    rw [h2, ← h4]
  rw [h6, e1, e2, h5]
  ring

/-! ## Corollary: prime doubling (the case k = 1) -/

lemma convCount_empty : convCount (∅ : Finset ℕ) = 1 := by
  unfold convCount
  have hconv : IsConvexIn (∅ : Finset ℕ) ∅ :=
    ⟨Finset.Subset.refl _, fun a ha => by simp at ha⟩
  rw [Finset.powerset_empty, Finset.filter_singleton, if_pos hconv]
  rfl

lemma convCount_Icc_one_one : convCount (Icc 1 1) = 2 := by
  unfold convCount
  have hall : ∀ S ∈ (Icc 1 1).powerset, IsConvexIn (Icc 1 1) S := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    refine ⟨hS, ?_⟩
    intro a ha b hb hab c hc hac hcb
    have haI := hS ha
    rw [Finset.mem_Icc] at hc haI
    have hca : c = a := by omega
    rw [hca]
    exact ha
  rw [Finset.filter_true_of_mem hall, Finset.card_powerset, Nat.card_Icc]
  norm_num

/-- The prime-doubling theorem of A394685 as the `k = 1` instance of the
    renormalization theorem (cf. `DivisibilityPoset.prime_doubling`). -/
theorem prime_doubling_of_renormalization {p : ℕ} (hp : p.Prime) :
    convCount (Icc 1 p) = 2 * convCount (Icc 1 (p - 1)) := by
  have h := renormalization (k := 1) (p := p) le_rfl hp hp.one_lt.le
  rw [one_mul] at h
  simp only [Nat.sub_self] at h
  have h0 : convCount (Icc 1 0) = 1 := by
    rw [Finset.Icc_eq_empty (by omega)]
    exact convCount_empty
  rw [h0, mul_one, convCount_Icc_one_one] at h
  omega

/-! ## Summary

`renormalization` : c_k(kp) · a(k-1) = c_k(kp-1) · a(k) for every k ≥ 1 and
every prime p ≥ k. The proof is exactly the two-step structure of the paper
document:

  (i)  P = {k,...,kp-1} splits as C ⊔ R with C = {jp : j ≤ k-1} order-isolated
       (`copy_sep`), so c_k(kp-1) = a(k-1)·Conv(R) via the scaling isomorphism
       (`card_filter_image`) and multiplicative decoupling (`card_filter_union`).
  (ii) kp is maximal over P, so adjoining it contributes topCount P (kp)
       (`convCount_insert_top`); the top condition ignores R because the only
       divisor of kp in R is k, which is covered (`copy_top_trivial`), and on C
       it is the pullback of the top condition for adjoining k to [k-1] — the
       same quantity a(k) - a(k-1) produced by `convCount_insert_top` at scale k.

Both hypotheses `p prime` and `k ≤ p` are load-bearing: primality gives the
coprimality splits in `copy_sep`/`copy_top_trivial` and the covered-divisor
dichotomy n ∣ p ⟹ n ∈ {1,p}; p ≥ k forces every multiple of p that divides
into P to have cofactor < k (`mem_copy_of_p_dvd`). For p < k the identity can
fail, e.g. (k,p) = (4,2): c_4(8)/c_4(7) = 2 ≠ 7/4 = a(4)/a(3).
-/

end CausalAlgebraicGeometry.DivisibilityRenormalization
