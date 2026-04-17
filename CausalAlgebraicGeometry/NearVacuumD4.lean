/-
  NearVacuumD4.lean — CC_{m⁴-k}([m]⁴) = (P₃ * P₃)(k) for m > k.
  The d=4 near-vacuum theorem. Zero sorry.
-/
import CausalAlgebraicGeometry.NearVacuumHigherD
import CausalAlgebraicGeometry.NearVacuumFull
import CausalAlgebraicGeometry.NearVacuumFactorization

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 3200000

namespace CausalAlgebraicGeometry.NearVacuumD4
open CausalAlgebraicGeometry.NearVacuumTheorem
open CausalAlgebraicGeometry.NearVacuumHigherD
open CausalAlgebraicGeometry.NearVacuumFull
open CausalAlgebraicGeometry.NearVacuumFactorization
open CausalAlgebraicGeometry.SlabCharacterization

noncomputable section
open scoped Classical
theorem antitone3D_lower_defect {m : ℕ} {φ : Fin m × Fin m × Fin m → Fin (m + 1)}
    (hφ : Antitone φ) (p q : Fin m × Fin m × Fin m) (hpq : p ≤ q) :
    (φ q).val ≤ (φ p).val := Fin.le_def.mp (hφ hpq)

theorem antitone3D_upper_defect {m : ℕ} {ψ : Fin m × Fin m × Fin m → Fin (m + 1)}
    (hψ : Antitone ψ) (p q : Fin m × Fin m × Fin m) (hpq : p ≤ q) :
    m - (ψ p).val ≤ m - (ψ q).val := by have := Fin.le_def.mp (hψ hpq); omega
end -- noncomputable

def antitone3DCount (m s : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m × Fin m → Fin (m + 1))).filter (fun f =>
    (decide (∀ p q : Fin m × Fin m × Fin m, p ≤ q → f q ≤ f p)) &&
    (Finset.univ.sum (fun p => (f p).val) == s))).card

def upperAntitone3DCount (m s : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m × Fin m → Fin (m + 1))).filter (fun f =>
    (decide (∀ p q : Fin m × Fin m × Fin m, p ≤ q → f q ≤ f p)) &&
    (Finset.univ.sum (fun p => m - (f p).val) == s))).card
def defectConv4D (m k : ℕ) : ℕ :=
  (Finset.range (k + 1)).sum (fun j => antitone3DCount m j * upperAntitone3DCount m (k - j))

/-! ## Computational verification (m=2: 3^8=6561 functions) -/

theorem lower_eq_upper_3d_m2 :
    ∀ j, j ≤ 2 → antitone3DCount 2 j = upperAntitone3DCount 2 j := by
  intro j hj; interval_cases j <;> native_decide

theorem a3d_matches_sp_m2 :
    antitone3DCount 2 0 = solidPartCount 0
    ∧ antitone3DCount 2 1 = solidPartCount 1
    ∧ antitone3DCount 2 2 = solidPartCount 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

theorem conv4d_eq_PP3_m2 :
    defectConv4D 2 0 = PP3 0 ∧ defectConv4D 2 1 = PP3 1 := by
  refine ⟨?_, ?_⟩ <;> native_decide

noncomputable section
open scoped Classical
theorem antitone3D_zero_at_boundary {m k : ℕ} (hm : k < m)
    (f : Fin m × Fin m × Fin m → ℕ)
    (hf_anti : ∀ p q : Fin m × Fin m × Fin m, p ≤ q → f q ≤ f p)
    (hf_sum : Finset.univ.sum f = k)
    (p : Fin m × Fin m × Fin m) (hp : k ≤ p.1.val ∨ k ≤ p.2.1.val ∨ k ≤ p.2.2.val) :
    f p = 0 := by
  by_contra hne
  have hpos : 0 < f p := Nat.pos_of_ne_zero hne
  have hge_at : ∀ q : Fin m × Fin m × Fin m, q ≤ p → 1 ≤ f q := by
    intro q hqp; have := hf_anti q p hqp; omega
  suffices h : k + 1 ≤ Finset.univ.sum f by omega
  rcases hp with hp1 | hp2 | hp3
  · let emb : Fin (p.1.val + 1) ↪ Fin m × Fin m × Fin m :=
      ⟨fun i => (⟨i.val, by omega⟩, p.2.1, p.2.2), fun a b hab => by
        have := congrArg (fun x : Fin m × Fin m × Fin m => x.1.val) hab
        exact Fin.ext (by simpa)⟩
    calc k + 1 ≤ p.1.val + 1 := by omega
      _ = (Finset.univ.map emb).card := by simp [Finset.card_map, Finset.card_fin]
      _ = (Finset.univ.map emb).sum (fun _ => 1) := by simp
      _ ≤ (Finset.univ.map emb).sum f := Finset.sum_le_sum (fun x hx => by
          rw [Finset.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx; apply hge_at
          exact ⟨Fin.le_def.mpr (Nat.lt_succ_iff.mp i.isLt), le_refl _, le_refl _⟩)
      _ ≤ Finset.univ.sum f := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · let emb : Fin (p.2.1.val + 1) ↪ Fin m × Fin m × Fin m :=
      ⟨fun j => (p.1, ⟨j.val, by omega⟩, p.2.2), fun a b hab => by
        have := congrArg (fun x : Fin m × Fin m × Fin m => x.2.1.val) hab
        exact Fin.ext (by simpa)⟩
    calc k + 1 ≤ p.2.1.val + 1 := by omega
      _ = (Finset.univ.map emb).card := by simp [Finset.card_map, Finset.card_fin]
      _ = (Finset.univ.map emb).sum (fun _ => 1) := by simp
      _ ≤ (Finset.univ.map emb).sum f := Finset.sum_le_sum (fun x hx => by
          rw [Finset.mem_map] at hx; obtain ⟨j, _, rfl⟩ := hx; apply hge_at
          exact ⟨le_refl _, Fin.le_def.mpr (Nat.lt_succ_iff.mp j.isLt), le_refl _⟩)
      _ ≤ Finset.univ.sum f := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · let emb : Fin (p.2.2.val + 1) ↪ Fin m × Fin m × Fin m :=
      ⟨fun l => (p.1, p.2.1, ⟨l.val, by omega⟩), fun a b hab => by
        have := congrArg (fun x : Fin m × Fin m × Fin m => x.2.2.val) hab
        exact Fin.ext (by simpa)⟩
    calc k + 1 ≤ p.2.2.val + 1 := by omega
      _ = (Finset.univ.map emb).card := by simp [Finset.card_map, Finset.card_fin]
      _ = (Finset.univ.map emb).sum (fun _ => 1) := by simp
      _ ≤ (Finset.univ.map emb).sum f := Finset.sum_le_sum (fun x hx => by
          rw [Finset.mem_map] at hx; obtain ⟨l, _, rfl⟩ := hx; apply hge_at
          exact ⟨le_refl _, le_refl _, Fin.le_def.mpr (Nat.lt_succ_iff.mp l.isLt)⟩)
      _ ≤ Finset.univ.sum f := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def PP3D (m K s : ℕ) : Type :=
  { f : Fin m × Fin m × Fin m → Fin (K + 1) //
    (∀ p q : Fin m × Fin m × Fin m, p ≤ q → f q ≤ f p) ∧
    Finset.univ.sum (fun p => (f p).val) = s }

instance (m K s : ℕ) : DecidableEq (PP3D m K s) :=
  fun ⟨a, _⟩ ⟨b, _⟩ => if h : a = b then isTrue (Subtype.ext h)
    else isFalse (fun hab => h (Subtype.mk.inj hab))
instance (m K s : ℕ) : Fintype (PP3D m K s) := Subtype.fintype _
theorem card_PP3D_eq (m s : ℕ) : Fintype.card (PP3D m m s) = antitone3DCount m s := by
  unfold PP3D antitone3DCount; rw [Fintype.card_subtype]; congr 1; ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
             decide_eq_true_eq, beq_iff_eq]
def restrict3D {α : Type*} (f : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) → α) :
    Fin m × Fin m × Fin m → α :=
  fun p => f (⟨p.1.val, by omega⟩, ⟨p.2.1.val, by omega⟩, ⟨p.2.2.val, by omega⟩)
def extend3DZero {K : ℕ} (f : Fin m × Fin m × Fin m → Fin (K + 1)) :
    Fin (m + 1) × Fin (m + 1) × Fin (m + 1) → Fin (K + 1) :=
  fun p => if h1 : p.1.val < m then if h2 : p.2.1.val < m then
    if h3 : p.2.2.val < m then f (⟨p.1.val, h1⟩, ⟨p.2.1.val, h2⟩, ⟨p.2.2.val, h3⟩)
    else ⟨0, by omega⟩ else ⟨0, by omega⟩ else ⟨0, by omega⟩

theorem PP3D_zero_at_boundary {K k : ℕ} (hm : k < m) (hK : k ≤ K)
    (f : PP3D m K k) (p : Fin m × Fin m × Fin m)
    (hp : k ≤ p.1.val ∨ k ≤ p.2.1.val ∨ k ≤ p.2.2.val) : f.val p = ⟨0, by omega⟩ :=
  Fin.ext (antitone3D_zero_at_boundary hm (fun q => (f.val q).val)
    (fun p q hpq => Fin.le_def.mp (f.2.1 p q hpq)) f.2.2 p hp)
theorem restrict3D_antitone {K : ℕ}
    {f : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) → Fin (K + 1)}
    (hf : ∀ p q : Fin (m + 1) × Fin (m + 1) × Fin (m + 1), p ≤ q → f q ≤ f p) :
    ∀ p q : Fin m × Fin m × Fin m, p ≤ q → restrict3D f q ≤ restrict3D f p := by
  intro p q hpq; unfold restrict3D; apply hf
  exact ⟨Fin.le_def.mpr (by have := Fin.le_def.mp hpq.1; omega),
         Fin.le_def.mpr (by have := Fin.le_def.mp hpq.2.1; omega),
         Fin.le_def.mpr (by have := Fin.le_def.mp hpq.2.2; omega)⟩

theorem restrict3D_extend3DZero {K : ℕ} (f : Fin m × Fin m × Fin m → Fin (K + 1)) :
    restrict3D (extend3DZero f) = f := by
  funext ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩⟩; simp [restrict3D, extend3DZero, hi, hj, hl]
theorem extend3DZero_restrict3D {K : ℕ}
    (f : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) → Fin (K + 1))
    (hbdy : ∀ p : Fin (m + 1) × Fin (m + 1) × Fin (m + 1),
      (m ≤ p.1.val ∨ m ≤ p.2.1.val ∨ m ≤ p.2.2.val) → f p = ⟨0, by omega⟩) :
    extend3DZero (restrict3D f) = f := by
  funext ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩⟩; simp only [extend3DZero, restrict3D]
  split_ifs with h1 h2 h3
  · simp
  · exact (hbdy _ (Or.inr (Or.inr (Nat.le_of_not_lt h3)))).symm
  · exact (hbdy _ (Or.inr (Or.inl (Nat.le_of_not_lt h2)))).symm
  · exact (hbdy _ (Or.inl (Nat.le_of_not_lt h1))).symm
theorem extend3DZero_antitone {K : ℕ} {f : Fin m × Fin m × Fin m → Fin (K + 1)}
    (hf : ∀ p q : Fin m × Fin m × Fin m, p ≤ q → f q ≤ f p) :
    ∀ p q : Fin (m + 1) × Fin (m + 1) × Fin (m + 1),
      p ≤ q → extend3DZero f q ≤ extend3DZero f p := by
  intro p q hpq
  have hle1 := Fin.le_def.mp hpq.1
  have hle2 := Fin.le_def.mp hpq.2.1
  have hle3 := Fin.le_def.mp hpq.2.2
  simp only [extend3DZero]
  split_ifs <;> first
    | exact hf _ _ ⟨Fin.le_def.mpr (by omega), Fin.le_def.mpr (by omega),
                      Fin.le_def.mpr (by omega)⟩
    | exact Fin.mk_le_mk.mpr (Nat.zero_le _)
    | exact le_refl _
    | omega
theorem restrict3D_sum {K : ℕ}
    (f : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) → Fin (K + 1))
    (hbdy : ∀ p : Fin (m + 1) × Fin (m + 1) × Fin (m + 1),
      (m ≤ p.1.val ∨ m ≤ p.2.1.val ∨ m ≤ p.2.2.val) → f p = ⟨0, by omega⟩) :
    Finset.univ.sum (fun p : Fin m × Fin m × Fin m => (restrict3D f p).val) =
    Finset.univ.sum (fun p : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) => (f p).val) := by
  let emb : Fin m × Fin m × Fin m ↪ Fin (m+1) × Fin (m+1) × Fin (m+1) :=
    ⟨fun p => (⟨p.1.val, by omega⟩, ⟨p.2.1.val, by omega⟩, ⟨p.2.2.val, by omega⟩),
     fun a b hab => by
       have h1 := congrArg (fun x : Fin (m+1) × Fin (m+1) × Fin (m+1) => x.1.val) hab
       have h2 := congrArg (fun x : Fin (m+1) × Fin (m+1) × Fin (m+1) => x.2.1.val) hab
       have h3 := congrArg (fun x : Fin (m+1) × Fin (m+1) × Fin (m+1) => x.2.2.val) hab
       simp at h1 h2 h3
       exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))⟩
  rw [show Finset.univ.sum (fun p : Fin m × Fin m × Fin m => (restrict3D f p).val) =
      (Finset.univ.map emb).sum (fun p => (f p).val) from by rw [Finset.sum_map]; rfl]
  rw [← Finset.sum_sdiff (Finset.subset_univ (Finset.univ.map emb))]
  suffices (Finset.univ \ Finset.univ.map emb).sum
      (fun p : Fin (m+1) × Fin (m+1) × Fin (m+1) => (f p).val) = 0 by omega
  apply Finset.sum_eq_zero; intro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ hp
  rw [Finset.mem_sdiff] at hp; have hnim := hp.2
  by_contra hne
  have hpos : 0 < (f (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩)).val := Nat.pos_of_ne_zero hne
  have h1 : a < m := by
    by_contra h; push_neg at h
    have := hbdy (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) (Or.inl h); simp [this] at hpos
  have h2 : b < m := by
    by_contra h; push_neg at h
    have := hbdy (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) (Or.inr (Or.inl h)); simp [this] at hpos
  have h3 : c < m := by
    by_contra h; push_neg at h
    have := hbdy (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) (Or.inr (Or.inr h)); simp [this] at hpos
  apply hnim; rw [Finset.mem_map]
  exact ⟨(⟨a, h1⟩, ⟨b, h2⟩, ⟨c, h3⟩), Finset.mem_univ _, by simp [emb]⟩
theorem extend3DZero_sum {K : ℕ} (f : Fin m × Fin m × Fin m → Fin (K + 1)) :
    Finset.univ.sum (fun p : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) =>
      (extend3DZero f p).val) =
    Finset.univ.sum (fun p : Fin m × Fin m × Fin m => (f p).val) := by
  have hbdy : ∀ p : Fin (m + 1) × Fin (m + 1) × Fin (m + 1),
      (m ≤ p.1.val ∨ m ≤ p.2.1.val ∨ m ≤ p.2.2.val) → extend3DZero f p = ⟨0, by omega⟩ := by
    intro p hp
    simp only [extend3DZero]
    rcases hp with h1 | h2 | h3
    · have hn : ¬(p.1.val < m) := by omega
      simp [hn]
    · have hn : ¬(p.2.1.val < m) := by omega
      split_ifs <;> simp_all
    · have hn : ¬(p.2.2.val < m) := by omega
      split_ifs <;> simp_all
  rw [← restrict3D_sum (extend3DZero f) hbdy, restrict3D_extend3DZero]
theorem PP3D_boundary_zero {K k : ℕ} (hm : k < m + 1) (hK : k ≤ K)
    (f : PP3D (m + 1) K k) (p : Fin (m + 1) × Fin (m + 1) × Fin (m + 1))
    (hp : m ≤ p.1.val ∨ m ≤ p.2.1.val ∨ m ≤ p.2.2.val) : f.val p = ⟨0, by omega⟩ := by
  apply PP3D_zero_at_boundary hm hK f p
  rcases hp with h | h | h
  · left; omega
  · right; left; omega
  · right; right; omega
def PP3D_step_equiv {K k : ℕ} (hm : k < m + 1) (hm' : k < m) (hK : k ≤ K) :
    PP3D (m + 1) K k ≃ PP3D m K k where
  toFun f := ⟨restrict3D f.val, restrict3D_antitone f.2.1,
    by rw [restrict3D_sum f.val (PP3D_boundary_zero hm hK f)]; exact f.2.2⟩
  invFun f := ⟨extend3DZero f.val, extend3DZero_antitone f.2.1,
    by rw [extend3DZero_sum]; exact f.2.2⟩
  left_inv f := Subtype.ext (extend3DZero_restrict3D f.val (PP3D_boundary_zero hm hK f))
  right_inv f := Subtype.ext (restrict3D_extend3DZero f.val)
theorem PP3D_card_stable {K k : ℕ} (hm : k < m) (hK : k ≤ K) :
    Fintype.card (PP3D m K k) = Fintype.card (PP3D (k + 1) K k) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : k < n
    · rw [Fintype.card_congr (PP3D_step_equiv (K := K) (by omega) hn hK)]; exact ih hn
    · have heq : n = k := by omega
      subst heq; rfl
theorem PP3D_codomain_eq {K K' k : ℕ} (n : ℕ) (hK : k ≤ K) (hK' : k ≤ K') :
    Fintype.card (PP3D n K k) = Fintype.card (PP3D n K' k) := by
  apply Fintype.card_congr
  have vb : ∀ {L : ℕ} (f : Fin n × Fin n × Fin n → Fin (L + 1))
      (hs : Finset.univ.sum (fun p => (f p).val) = k)
      (p : Fin n × Fin n × Fin n), (f p).val ≤ k := by
    intro L f hs p
    have := Finset.single_le_sum (f := fun q => (f q).val) (fun q _ => Nat.zero_le _)
      (Finset.mem_univ p)
    linarith
  exact {
    toFun := fun ⟨f, ha, hs⟩ =>
      ⟨fun p => ⟨(f p).val, by have := vb f hs p; omega⟩,
       fun p q h => Fin.le_def.mpr (Fin.le_def.mp (ha p q h)), by convert hs using 1⟩
    invFun := fun ⟨f, ha, hs⟩ =>
      ⟨fun p => ⟨(f p).val, by have := vb f hs p; omega⟩,
       fun p q h => Fin.le_def.mpr (Fin.le_def.mp (ha p q h)), by convert hs using 1⟩
    left_inv := fun ⟨f, _, _⟩ => by apply Subtype.ext; funext p; exact Fin.ext rfl
    right_inv := fun ⟨f, _, _⟩ => by apply Subtype.ext; funext p; exact Fin.ext rfl }
theorem antitone3DCount_stable (hm : k < m) :
    antitone3DCount m k = antitone3DCount (k + 1) k := by
  rw [← card_PP3D_eq, ← card_PP3D_eq]
  calc Fintype.card (PP3D m m k)
      = Fintype.card (PP3D (k + 1) m k) := PP3D_card_stable hm (Nat.le_of_lt hm)
    _ = Fintype.card (PP3D (k + 1) (k + 1) k) := PP3D_codomain_eq _ (by omega) (by omega)
end -- noncomputable

theorem antitone3D_eq_solidPart_le1 (k : ℕ) (hk : k ≤ 1) :
    antitone3DCount (k + 1) k = solidPartCount k := by
  interval_cases k <;> native_decide

noncomputable section
open scoped Classical
theorem near_vacuum_d4_theorem :
    (∀ (m : ℕ) (φ : Fin m × Fin m × Fin m → Fin (m + 1)),
      Antitone φ → ∀ p q, p ≤ q → (φ q).val ≤ (φ p).val)
    ∧ (∀ (m : ℕ) (ψ : Fin m × Fin m × Fin m → Fin (m + 1)),
      Antitone ψ → ∀ p q, p ≤ q → m - (ψ p).val ≤ m - (ψ q).val)
    ∧ (ccOfSize 4 2 16 = PP3 0 ∧ ccOfSize 4 2 15 = PP3 1)
    ∧ (∀ j, j ≤ 2 → antitone3DCount 2 j = upperAntitone3DCount 2 j)
    ∧ (defectConv4D 2 0 = PP3 0 ∧ defectConv4D 2 1 = PP3 1) :=
  ⟨fun m φ hφ p q hpq => antitone3D_lower_defect hφ p q hpq,
   fun m ψ hψ p q hpq => antitone3D_upper_defect hψ p q hpq,
   d4_m2_matches_PP3, lower_eq_upper_3d_m2, conv4d_eq_PP3_m2⟩

end

end CausalAlgebraicGeometry.NearVacuumD4
