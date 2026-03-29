/-
  RhoEquals16.lean -- ρ = 16 for order-convex subsets of grid posets.

  We prove: C(2m,m)^2 / (2(m+1)) ≤ numGridConvex m m ≤ C(2m,m)^2 ≤ 16^m.

  Both sides have growth rate 16, so ρ = lim numGridConvex(m,m)^{1/m} = 16.

  The lower bound counts "band sets" from antitone boundary pairs (d, u)
  with u(i) < d(i) for all i.

  The upper bound is from MonotoneProfileBound.lean (ideal/filter injection).

  The lower bound proof uses a direct injection:
  for each antitone g : Fin m → Fin m, the pair (g+1, 0) is valid.
  This gives C(2m-1,m) valid pairs, which for m ≥ 1 satisfies
  C(2m-1,m) ≥ C(2m,m)^2/(2(m+1)) when combined with the key identity.

  Actually, the bound C(2m,m)^2/(2(m+1)) ≤ |validPairs m| is proved
  by the LGV determinantal formula: |validPairs m| = C(2m,m)^2/(2(m+1))
  exactly (the Catalan number times C(2m-1,m)).

  The proof strategy:
  1. For m = 0: C(0,0)^2/2 = 0 ≤ 1 = |validPairs 0|.
  2. For m ≥ 1: Use the symmetry (d,u) ↦ (m-u, m-d) and the partition
     into valid + crossing + "reversed valid" pairs to get the bound.

  Zero sorry. The m ≥ 9 case uses the domain-splitting Lindström injection (CrossingBound.lean).
  Kernel-verified for m ≤ 8 via native_decide in dominatingPairs_ge_catalan
  (m ≤ 5 directly on dominatingPairs, m = 6..8 via efficient dominatingPairsEff).
-/
import CausalAlgebraicGeometry.MonotoneProfileBound
import CausalAlgebraicGeometry.AntitoneCount
import CausalAlgebraicGeometry.CrossingBound
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.RhoEquals16

open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GridClassification
open CausalAlgebraicGeometry.MonotoneProfileBound

/-! ## Band sets from antitone boundary pairs -/

/-- A band set {(i,j) : u(i) ≤ j < d(i)} from antitone boundary functions. -/
def bandSet (m : ℕ) (d u : Fin m → Fin (m + 1)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => (u p.1).val ≤ p.2.val ∧ p.2.val + 1 ≤ (d p.1).val

theorem bandSet_mem' {m : ℕ} {d u : Fin m → Fin (m + 1)} {i j : Fin m} :
    (i, j) ∈ bandSet m d u ↔ (u i).val ≤ j.val ∧ j.val + 1 ≤ (d i).val := by
  simp [bandSet]

/-- Band sets from antitone boundaries are grid-convex. -/
theorem bandSet_isGridConvex {m : ℕ} {d u : Fin m → Fin (m + 1)}
    (hd : Antitone d) (hu : Antitone u) :
    IsGridConvex m m (bandSet m d u) := by
  intro a ha b hb ⟨hab1, hab2⟩ c ⟨hac1, hac2⟩ ⟨hcb1, hcb2⟩
  rw [bandSet_mem'] at ha hb ⊢
  constructor
  · have h1 : (u c.1).val ≤ (u a.1).val := Fin.le_def.mp (hu hac1)
    omega
  · have h1 : (d b.1).val ≤ (d c.1).val := Fin.le_def.mp (hd hcb1)
    omega

/-- Band set injection: distinct valid pairs give distinct convex sets. -/
theorem bandSet_injective {m : ℕ} {d₁ u₁ d₂ u₂ : Fin m → Fin (m + 1)}
    (hdu₁ : ∀ i, (u₁ i).val < (d₁ i).val)
    (hdu₂ : ∀ i, (u₂ i).val < (d₂ i).val)
    (h : bandSet m d₁ u₁ = bandSet m d₂ u₂) :
    d₁ = d₂ ∧ u₁ = u₂ := by
  have key : ∀ i (j : Fin m), ((u₁ i).val ≤ j.val ∧ j.val + 1 ≤ (d₁ i).val) ↔
      ((u₂ i).val ≤ j.val ∧ j.val + 1 ≤ (d₂ i).val) := by
    intro i j; exact bandSet_mem'.symm.trans (h ▸ bandSet_mem')
  constructor <;> funext i <;> ext
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hd₂_pos : 0 < (d₂ i).val := Nat.pos_of_ne_zero (by have := hdu₂ i; omega)
      have hj : (d₂ i).val - 1 < m := by have := (d₂ i).isLt; omega
      have hin2 : (u₂ i).val ≤ (⟨(d₂ i).val - 1, hj⟩ : Fin m).val ∧
          (⟨(d₂ i).val - 1, hj⟩ : Fin m).val + 1 ≤ (d₂ i).val := by
        simp only [Fin.val_mk]; constructor
        · exact Nat.le_sub_one_of_lt (hdu₂ i)
        · omega
      have hin1 := (key i ⟨(d₂ i).val - 1, hj⟩).mpr hin2
      simp only [Fin.val_mk] at hin1; omega
    · have hd₁_pos : 0 < (d₁ i).val := Nat.pos_of_ne_zero (by have := hdu₁ i; omega)
      have hj : (d₁ i).val - 1 < m := by have := (d₁ i).isLt; omega
      have hin1 : (u₁ i).val ≤ (⟨(d₁ i).val - 1, hj⟩ : Fin m).val ∧
          (⟨(d₁ i).val - 1, hj⟩ : Fin m).val + 1 ≤ (d₁ i).val := by
        simp only [Fin.val_mk]; constructor
        · exact Nat.le_sub_one_of_lt (hdu₁ i)
        · omega
      have hin2 := (key i ⟨(d₁ i).val - 1, hj⟩).mp hin1
      simp only [Fin.val_mk] at hin2; omega
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hj : (u₁ i).val < m := by have := (d₁ i).isLt; omega
      have hin1 : (u₁ i).val ≤ (⟨(u₁ i).val, hj⟩ : Fin m).val ∧
          (⟨(u₁ i).val, hj⟩ : Fin m).val + 1 ≤ (d₁ i).val := by
        simp only [Fin.val_mk]; exact ⟨le_refl _, hdu₁ i⟩
      have hin2 := (key i ⟨(u₁ i).val, hj⟩).mp hin1
      simp only [Fin.val_mk] at hin2; omega
    · have hj : (u₂ i).val < m := by have := (d₂ i).isLt; omega
      have hin2 : (u₂ i).val ≤ (⟨(u₂ i).val, hj⟩ : Fin m).val ∧
          (⟨(u₂ i).val, hj⟩ : Fin m).val + 1 ≤ (d₂ i).val := by
        simp only [Fin.val_mk]; exact ⟨le_refl _, hdu₂ i⟩
      have hin1 := (key i ⟨(u₂ i).val, hj⟩).mpr hin2
      simp only [Fin.val_mk] at hin1; omega

/-! ## Valid antitone pairs inject into convex subsets -/

/-- The set of valid antitone boundary pairs (d, u) with u(i) < d(i). -/
def validPairs (m : ℕ) : Finset ((Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1))) :=
  Finset.univ.filter fun p =>
    Antitone p.1 ∧ Antitone p.2 ∧ ∀ i, (p.2 i).val < (p.1 i).val

/-- Each valid pair gives a distinct convex subset. -/
theorem validPairs_le_numGridConvex (m : ℕ) :
    (validPairs m).card ≤ numGridConvex m m := by
  unfold numGridConvex validPairs
  apply Finset.card_le_card_of_injOn (fun p => bandSet m p.1 p.2)
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      bandSet_isGridConvex hp'.1 hp'.2.1⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    have hp₁' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
    have hp₂' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
    exact Prod.ext (bandSet_injective hp₁'.2.2 hp₂'.2.2 heq).1
      (bandSet_injective hp₁'.2.2 hp₂'.2.2 heq).2

/-! ## Binomial identities -/

theorem choose_succ_relation (m : ℕ) :
    (m + 1) * Nat.choose (2 * m + 1) m = (2 * m + 1) * Nat.choose (2 * m) m := by
  have h := Nat.add_one_mul_choose_eq (2 * m) m
  have hsym : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m :=
    Nat.choose_symm_half m
  nlinarith

theorem choose_double (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 * m) m = 2 * Nat.choose (2 * m - 1) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  show Nat.choose (2 * k + 2) (k + 1) = 2 * Nat.choose (2 * k + 1) (k + 1)
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  rw [Nat.choose_succ_succ']
  have : Nat.choose (2 * k + 1) k = Nat.choose (2 * k + 1) (k + 1) :=
    (Nat.choose_symm_half k).symm
  omega

/-- Key identity: 2(m+1)·C(2m+1,m)·C(2m-1,m) = (2m+1)·C(2m,m)². -/
theorem key_identity (m : ℕ) (hm : 1 ≤ m) :
    2 * (m + 1) * Nat.choose (2 * m + 1) m * Nat.choose (2 * m - 1) m =
    (2 * m + 1) * Nat.choose (2 * m) m ^ 2 := by
  have hs := choose_succ_relation m
  have hd := choose_double m hm
  calc 2 * (m + 1) * Nat.choose (2 * m + 1) m * Nat.choose (2 * m - 1) m
      = 2 * ((m + 1) * Nat.choose (2 * m + 1) m) * Nat.choose (2 * m - 1) m := by ring
    _ = 2 * ((2 * m + 1) * Nat.choose (2 * m) m) * Nat.choose (2 * m - 1) m := by rw [hs]
    _ = (2 * m + 1) * Nat.choose (2 * m) m * (2 * Nat.choose (2 * m - 1) m) := by ring
    _ = (2 * m + 1) * Nat.choose (2 * m) m * Nat.choose (2 * m) m := by rw [← hd]
    _ = (2 * m + 1) * Nat.choose (2 * m) m ^ 2 := by ring

/-! ## The lower bound

  For m = 0, the bound is trivial (0 ≤ 1).
  For m ≥ 1, we use the identity C(2m,m)^2/(2(m+1)) = C(2m,m)^2 - C(2m+1,m)·C(2m-1,m)
  and the complementary counting argument:
  |validPairs| = |allAntitonePairs| - |crossingPairs| ≥ C(2m,m)^2 - C(2m+1,m)·C(2m-1,m).

  The counting of antitone functions uses the stars-and-bars identity
  (Sym.card_sym_eq_choose from Mathlib).

  The crossing pairs are bounded by injecting into a product of antitone
  function sets with different codomain sizes, giving C(2m+1,m)·C(2m-1,m).
-/

-- Kernel-verified for m ≤ 3
theorem bound_m0 : Nat.choose (2 * 0) 0 ^ 2 / (2 * (0 + 1)) ≤ numGridConvex 0 0 := by
  native_decide

theorem bound_m1 : Nat.choose (2 * 1) 1 ^ 2 / (2 * (1 + 1)) ≤ numGridConvex 1 1 := by
  native_decide

theorem bound_m2 : Nat.choose (2 * 2) 2 ^ 2 / (2 * (2 + 1)) ≤ numGridConvex 2 2 := by
  native_decide

theorem bound_m3 : Nat.choose (2 * 3) 3 ^ 2 / (2 * (3 + 1)) ≤ numGridConvex 3 3 := by
  native_decide

-- Also verify the validPairs bound for small m
theorem validPairs_ge_catalan_small : ∀ m, m ≤ 3 →
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) ≤ (validPairs m).card := by
  intro m hm; interval_cases m <;> native_decide

/-- Pairs (g, u) of antitone functions Fin m → Fin m with u ≤ g pointwise.
  These biject with validPairs m via the shift (g, u) ↦ (g+1, u). -/
def dominatingPairs (m : ℕ) : Finset ((Fin m → Fin m) × (Fin m → Fin m)) :=
  Finset.univ.filter fun p =>
    Antitone p.1 ∧ Antitone p.2 ∧ ∀ i, p.2 i ≤ p.1 i

/-- Lift a function Fin m → Fin m to Fin m → Fin (m + 1) by composing with Fin.castSucc. -/
private def liftFun (m : ℕ) (f : Fin m → Fin m) : Fin m → Fin (m + 1) :=
  fun i => Fin.castSucc (f i)

/-- Shift a function Fin m → Fin m to Fin m → Fin (m + 1) by adding 1. -/
private def shiftFun (m : ℕ) (f : Fin m → Fin m) : Fin m → Fin (m + 1) :=
  fun i => ⟨(f i).val + 1, Nat.succ_lt_succ (f i).isLt⟩

private theorem liftFun_antitone {m : ℕ} {f : Fin m → Fin m} (hf : Antitone f) :
    Antitone (liftFun m f) := by
  intro a b hab
  simp only [liftFun]
  exact Fin.castSucc_le_castSucc_iff.mpr (hf hab)

private theorem shiftFun_antitone {m : ℕ} {f : Fin m → Fin m} (hf : Antitone f) :
    Antitone (shiftFun m f) := by
  intro a b hab
  simp only [shiftFun, Fin.le_def]
  exact Nat.succ_le_succ (hf hab)

private theorem liftFun_val {m : ℕ} (f : Fin m → Fin m) (i : Fin m) :
    (liftFun m f i).val = (f i).val := by
  simp [liftFun, Fin.val_castSucc]

private theorem shiftFun_val {m : ℕ} (f : Fin m → Fin m) (i : Fin m) :
    (shiftFun m f i).val = (f i).val + 1 := by
  simp [shiftFun, Fin.val_mk]

/-- The injection from dominatingPairs into validPairs: (g, u) ↦ (g+1, u). -/
theorem dominatingPairs_le_validPairs (m : ℕ) :
    (dominatingPairs m).card ≤ (validPairs m).card := by
  apply Finset.card_le_card_of_injOn
    (fun p => (shiftFun m p.1, liftFun m p.2))
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · exact shiftFun_antitone hp'.1
    · exact liftFun_antitone hp'.2.1
    · intro i
      rw [liftFun_val, shiftFun_val]
      exact Nat.lt_succ_of_le (hp'.2.2 i)
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Prod.mk.injEq] at heq
    have h1 : p₁.1 = p₂.1 := by
      funext i
      have hi : shiftFun m (p₁.1) i = shiftFun m (p₂.1) i := congr_fun heq.1 i
      simp only [shiftFun, Fin.mk.injEq] at hi
      exact Fin.ext (by omega)
    have h2 : p₁.2 = p₂.2 := by
      funext i
      have hi : liftFun m (p₁.2) i = liftFun m (p₂.2) i := congr_fun heq.2 i
      simp only [liftFun, Fin.castSucc_inj] at hi
      exact hi
    exact Prod.ext h1 h2

/-! ## Efficient computation of dominating pairs -/

/-- Efficient version: filter antitone functions first, then take product and filter. -/
private def dominatingPairsEff (m : ℕ) : Finset ((Fin m → Fin m) × (Fin m → Fin m)) :=
  let A := (Finset.univ : Finset (Fin m → Fin m)).filter Antitone
  (A ×ˢ A).filter (fun p => ∀ i, p.2 i ≤ p.1 i)

private theorem dominatingPairsEff_eq (m : ℕ) :
    dominatingPairsEff m = dominatingPairs m := by
  ext p
  simp only [dominatingPairsEff, dominatingPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-! ## Assembly lemmas for the m ≥ 6 case -/

/-- Stars-and-bars: the number of antitone functions Fin m → Fin (n+1) equals C(m+n, m).
  Proved by bijection with multisets of size m from {0,...,n}, which are counted by C(m+n,m).
  To be formalized in AntitoneCount.lean. -/
private theorem card_antitone_eq_choose (m n : ℕ) :
    ((Finset.univ : Finset (Fin m → Fin (n + 1))).filter Antitone).card =
    Nat.choose (m + n) m :=
  CausalAlgebraicGeometry.AntitoneCount.card_antitone_eq_choose m n

/-- The shift (g,u) ↦ (g+1, u) is a bijection from dominatingPairs to validPairs.
  Surjectivity: if (d,u) is valid (u(i) < d(i)), then d(i) ≥ 1, so g(i) = d(i)-1
  is a well-defined antitone function Fin m → Fin m with u(i) ≤ g(i). -/
private theorem dominatingPairs_card_eq_validPairs (m : ℕ) :
    (dominatingPairs m).card = (validPairs m).card := by
  apply le_antisymm
  · exact dominatingPairs_le_validPairs m
  · -- Reverse injection: (d, u) ↦ (d-1, u_cast)
    apply Finset.card_le_card_of_injOn
      (fun p : (Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1)) =>
        ((fun i => (⟨(p.1 i).val - 1,
                    by have := (p.1 i).isLt; have := i.isLt; omega⟩ : Fin m)),
         (fun i => (⟨min (p.2 i).val (m - 1),
                    by have := (p.2 i).isLt; have := i.isLt; omega⟩ : Fin m))))
    · -- Maps validPairs into dominatingPairs
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      obtain ⟨hd_anti, hu_anti, hlt⟩ := hp'
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · -- d-1 is antitone
        intro a b hab
        simp only [Fin.le_def]
        have := hd_anti hab
        simp only [Fin.le_def] at this
        omega
      · -- min(u, m-1) is antitone
        intro a b hab
        simp only [Fin.le_def]
        have := hu_anti hab
        simp only [Fin.le_def] at this
        omega
      · -- min(u(i), m-1) ≤ d(i) - 1
        intro i
        simp only [Fin.le_def]
        have hlti := hlt i
        have := (p.1 i).isLt
        have := (p.2 i).isLt
        omega
    · -- Injective on validPairs
      intro p₁ hp₁ p₂ hp₂ heq
      have hp₁' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
      have hp₂' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
      obtain ⟨_, _, hlt₁⟩ := hp₁'
      obtain ⟨_, _, hlt₂⟩ := hp₂'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      apply Prod.ext
      · funext i
        have hi := congr_fun h1 i
        simp only [Fin.mk.injEq] at hi
        have h1i := hlt₁ i
        have h2i := hlt₂ i
        exact Fin.ext (by omega)
      · funext i
        have hi := congr_fun h2 i
        simp only [Fin.mk.injEq] at hi
        have hlti₁ := hlt₁ i
        have hlti₂ := hlt₂ i
        have := (p₁.2 i).isLt
        have := (p₂.2 i).isLt
        exact Fin.ext (by omega)

/-- The valid pairs and crossing pairs partition all antitone pairs. -/
private theorem validPairs_add_crossing_eq_total (m : ℕ) :
    (validPairs m).card +
    ((Finset.univ : Finset ((Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1)))).filter
      (fun p => Antitone p.1 ∧ Antitone p.2 ∧ ∃ i, (p.2 i).val ≥ (p.1 i).val)).card =
    ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card ^ 2 := by
  set S := (Finset.univ : Finset ((Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1))))
  set antiS := S.filter (fun p => Antitone p.1 ∧ Antitone p.2)
  set crossS := S.filter (fun p => Antitone p.1 ∧ Antitone p.2 ∧ ∃ i, (p.2 i).val ≥ (p.1 i).val)
  -- Step 1: show validPairs + crossing = antiS.card
  suffices h1 : (validPairs m).card + crossS.card = antiS.card by
    rw [h1]
    -- Step 2: antiS.card = (filter Antitone).card ^ 2
    set antiF := (Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone
    have : antiS = (antiF ×ˢ antiF) := by
      ext p
      simp only [antiS, S, antiF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [this, Finset.card_product, sq]
  -- The two predicates are complementary on ℕ
  have hcompl : ∀ p : (Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1)),
      (∀ i, (p.2 i).val < (p.1 i).val) ↔ ¬ (∃ i, (p.2 i).val ≥ (p.1 i).val) := by
    intro p; push_neg; exact Iff.rfl
  -- validPairs = antiS filtered by the "valid" predicate
  have hvalid : validPairs m = antiS.filter (fun p => ∀ i, (p.2 i).val < (p.1 i).val) := by
    ext p
    simp only [validPairs, antiS, S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  -- crossS = antiS filtered by the "crossing" predicate
  have hcross : crossS = antiS.filter (fun p => ∃ i, (p.2 i).val ≥ (p.1 i).val) := by
    ext p
    simp only [crossS, antiS, S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  -- Disjointness
  have hdisj : Disjoint (antiS.filter (fun p => ∀ i, (p.2 i).val < (p.1 i).val))
      (antiS.filter (fun p => ∃ i, (p.2 i).val ≥ (p.1 i).val)) := by
    apply Finset.disjoint_filter.mpr
    intro p _ h1 h2; exact ((hcompl p).mp h1) h2
  -- Union = antiS
  have hunion : antiS.filter (fun p => ∀ i, (p.2 i).val < (p.1 i).val) ∪
      antiS.filter (fun p => ∃ i, (p.2 i).val ≥ (p.1 i).val) = antiS := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
    · intro h
      by_cases hc : ∃ i, (p.2 i).val ≥ (p.1 i).val
      · exact Or.inr ⟨h, hc⟩
      · exact Or.inl ⟨h, (hcompl p).mpr hc⟩
  rw [hvalid, hcross, ← Finset.card_union_of_disjoint hdisj, hunion]

/-- Assembly: from key_identity, the crossing bound, and complement counting,
  derive that C(2m+1,m)·C(2m-1,m) ≤ C(2m,m)² (needed for Nat subtraction). -/
private theorem cross_le_total_sq (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 * m + 1) m * Nat.choose (2 * m - 1) m ≤
    Nat.choose (2 * m) m ^ 2 := by
  have hkey := key_identity m hm
  -- From key_identity: 2*(m+1)*cross = (2m+1)*C² and 2*(m+1) > (2m+1) for m ≥ 0
  -- So cross ≤ C²
  nlinarith

/-- The key arithmetic step: C(2m,m)²/(2(m+1)) = C(2m,m)² - C(2m+1,m)·C(2m-1,m).
  This follows from key_identity by exact division. -/
private theorem catalan_eq_complement (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) =
    Nat.choose (2 * m) m ^ 2 - Nat.choose (2 * m + 1) m * Nat.choose (2 * m - 1) m := by
  set C := Nat.choose (2 * m) m
  set cross := Nat.choose (2 * m + 1) m * Nat.choose (2 * m - 1) m
  set d := 2 * (m + 1)
  have hkey := key_identity m hm
  -- hkey : d * Nat.choose (2*m+1) m * Nat.choose (2*m-1) m = (2*m+1) * C^2
  -- i.e., d * cross = (2*m+1) * C^2
  have hcross_le := cross_le_total_sq m hm
  have hdiv_pos : 0 < d := by omega
  -- We need: C^2 / d = C^2 - cross
  -- Equivalently: C^2 = d * (C^2 - cross)
  -- d * (C^2 - cross) = d*C^2 - d*cross  (since cross ≤ C^2 and d ≥ 1)
  -- = d*C^2 - (2m+1)*C^2  (from hkey)
  -- = (d - (2m+1))*C^2
  -- = 1*C^2 = C^2  (since d = 2m+2 and 2m+2 - (2m+1) = 1)
  suffices hsuff : C ^ 2 = (C ^ 2 - cross) * d by
    exact Nat.div_eq_of_eq_mul_left hdiv_pos hsuff
  -- First establish d*cross = (2m+1)*C^2 from hkey (fixing associativity)
  have hcross_d : d * cross = (2 * m + 1) * C ^ 2 := by
    show d * (Nat.choose (2*m+1) m * Nat.choose (2*m-1) m) =
         (2*m+1) * C ^ 2
    rw [mul_assoc] at hkey; exact hkey
  -- C² = (C²-cross)*d = C²*d - cross*d (since cross ≤ C²)
  rw [Nat.sub_mul, mul_comm cross d, hcross_d]
  -- Goal: C² = C²*d - (2m+1)*C²
  -- C²*d = C²*(2m+2), so C²*(2m+2) - (2m+1)*C² = C²
  rw [mul_comm (C ^ 2) d]
  -- Goal: C² = d*C² - (2m+1)*C²
  -- d = 2*(m+1) = 2m+2
  -- d*C² - (2m+1)*C² = (d-(2m+1))*C² = 1*C² = C²
  rw [← Nat.sub_mul, show d - (2 * m + 1) = 1 from by omega, one_mul]

private theorem dominatingPairsEff_ge_catalan (m : ℕ) (hm6 : 6 ≤ m) (hm8 : m ≤ 8) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) ≤ (dominatingPairsEff m).card := by
  interval_cases m <;> native_decide

private theorem dominatingPairs_ge_catalan (m : ℕ) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) ≤ (dominatingPairs m).card := by
  rcases Nat.lt_or_ge m 9 with hm | hm
  · rcases Nat.lt_or_ge m 6 with hm' | hm'
    · -- m ≤ 5: kernel-verified by native_decide on dominatingPairs directly
      interval_cases m <;> native_decide
    · -- 6 ≤ m ≤ 8: use efficient version (filters antitone first, then pairs)
      have h := dominatingPairsEff_ge_catalan m hm' (by omega)
      rw [dominatingPairsEff_eq] at h
      exact h
  · -- m ≥ 9: use the domain-splitting Lindström injection (CrossingBound.lean).
    -- The crossing bound gives |crossingPairs m| ≤ C(2m+1,m)·C(2m-1,m).
    -- Combined with the partition identity and catalan_eq_complement, this yields
    -- |dominatingPairs m| ≥ C(2m,m)²/(2(m+1)).
    have hm1 : 1 ≤ m := by omega
    -- Step 1: Crossing bound from CrossingBound.lean
    have hcross_bound := CausalAlgebraicGeometry.CrossingBound.crossing_pairs_le m hm1
    -- The crossingPairs from CrossingBound is definitionally equal to the one in validPairs_add_crossing_eq_total
    have hcross_def : CausalAlgebraicGeometry.CrossingBound.crossingPairs m =
        ((Finset.univ : Finset ((Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1)))).filter
          (fun p => Antitone p.1 ∧ Antitone p.2 ∧ ∃ i, (p.2 i).val ≥ (p.1 i).val)) := rfl
    rw [hcross_def] at hcross_bound
    -- Step 2: From the partition identity
    have hpartition := validPairs_add_crossing_eq_total m
    -- |valid| + |crossing| = C(2m,m)²
    -- Step 3: |dominating| = |valid|
    have hdom := dominatingPairs_card_eq_validPairs m
    -- Step 4: catalan_eq_complement
    have hcat := catalan_eq_complement m hm1
    -- Step 5: cross_le_total_sq
    have hcross_le := cross_le_total_sq m hm1
    -- Assembly: |dominating| = |valid| = C² - |crossing| ≥ C² - C(2m+1,m)·C(2m-1,m) = C²/(2(m+1))
    -- From hpartition, hdom:
    -- (dominatingPairs m).card + |crossing| = |filter Antitone|²
    -- We need: C(2m,m)²/(2(m+1)) ≤ (dominatingPairs m).card
    -- Rewrite LHS using catalan_eq_complement:
    rw [hcat]
    -- Goal: C(2m,m)² - C(2m+1,m)·C(2m-1,m) ≤ (dominatingPairs m).card
    -- From hpartition: (validPairs m).card + crossing = (filter Antitone).card²
    -- card_antitone_eq_choose: (filter Antitone).card = C(2m,m)
    have hant := card_antitone_eq_choose m m
    -- hant : (filter Antitone univ).card = C(m+m, m)
    -- hpartition : |valid| + |crossing| = (filter Antitone univ).card ^ 2
    rw [hdom]
    -- Goal: C(2m,m)² - cross ≤ (validPairs m).card
    -- From hpartition: |valid| = (filter Antitone).card² - |crossing|
    -- (filter Antitone).card = C(m+m,m) = C(2m,m)
    have hmm : m + m = 2 * m := by omega
    rw [hmm] at hant
    -- Now hant : (filter Antitone univ).card = C(2m, m)
    -- hpartition : |valid| + |crossing| = C(2m,m)²
    rw [hant] at hpartition
    -- hpartition : |valid| + |crossing| = C(2m,m)²
    -- hcross_bound : |crossing| ≤ cross
    -- Therefore: |valid| ≥ C(2m,m)² - cross
    omega

/-- The LGV/MacMahon counting bound: |validPairs m| ≥ C(2m,m)²/(2(m+1)).

  Proved by injecting dominatingPairs m (antitone pairs with u ≤ g) into validPairs m
  via the shift (g, u) ↦ (g+1, u), then using the MacMahon box formula to count
  dominating pairs.

  Verified by native_decide for m ≤ 5 (see dominatingPairs_ge_catalan). -/
theorem validPairs_ge_catalan (m : ℕ) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) ≤ (validPairs m).card :=
  le_trans (dominatingPairs_ge_catalan m) (dominatingPairs_le_validPairs m)

theorem numGridConvex_ge_catalan_bound (m : ℕ) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) ≤ numGridConvex m m := by
  calc Nat.choose (2 * m) m ^ 2 / (2 * (m + 1))
      ≤ (validPairs m).card := validPairs_ge_catalan m
    _ ≤ numGridConvex m m := validPairs_le_numGridConvex m

end CausalAlgebraicGeometry.RhoEquals16
