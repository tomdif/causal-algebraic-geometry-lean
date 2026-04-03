/-
  DepthThreshold.lean — The contact-depth threshold theorem.
  T_d(m) = (d+2)m − d = 2m + d(m−1).
  Zero sorry.
-/
import CausalAlgebraicGeometry.SharpThreshold

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 3200000

namespace CausalAlgebraicGeometry.DepthThreshold

noncomputable section
open scoped Classical

/-! ## Monotone sum bounds -/

private theorem card_filter_ge {m : ℕ} (x₀ : Fin m) :
    m - x₀.val ≤ (Finset.univ.filter (fun i : Fin m => x₀ ≤ i)).card := by
  let f : Fin (m - x₀.val) → Fin m := fun k => ⟨x₀.val + k.val, by omega⟩
  have hinj : Function.Injective f := by intro a b h; ext; simp [f, Fin.ext_iff] at h; omega
  have himg : (Finset.univ.image f) ⊆ Finset.univ.filter (fun i : Fin m => x₀ ≤ i) := by
    intro i hi; rw [Finset.mem_image] at hi; obtain ⟨k, _, rfl⟩ := hi
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Fin.le_def.mpr (by simp [f])⟩
  linarith [Finset.card_le_card himg, (Finset.card_image_of_injective _ hinj).symm ▸
    show (Finset.univ : Finset (Fin (m - x₀.val))).card = m - x₀.val from by simp]

private theorem card_filter_le {m : ℕ} (x₀ : Fin m) :
    x₀.val + 1 ≤ (Finset.univ.filter (fun i : Fin m => i ≤ x₀)).card := by
  let g : Fin (x₀.val + 1) → Fin m := fun k => ⟨k.val, by omega⟩
  have hinj : Function.Injective g := by intro a b h; ext; simp [g, Fin.ext_iff] at h; omega
  have himg : (Finset.univ.image g) ⊆ Finset.univ.filter (fun i : Fin m => i ≤ x₀) := by
    intro i hi; rw [Finset.mem_image] at hi; obtain ⟨k, _, rfl⟩ := hi
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Fin.le_def.mpr (by simp [g]; omega)⟩
  linarith [Finset.card_le_card himg, (Finset.card_image_of_injective _ hinj).symm ▸
    show (Finset.univ : Finset (Fin (x₀.val + 1))).card = x₀.val + 1 from by simp]

theorem nondec_tail_sum {m : ℕ} (a : Fin m → ℕ)
    (ha : ∀ i j : Fin m, i ≤ j → a i ≤ a j) (x₀ : Fin m) :
    (m - x₀.val) * a x₀ ≤ Finset.univ.sum a :=
  calc (m - x₀.val) * a x₀
      ≤ (Finset.univ.filter (x₀ ≤ ·)).card * a x₀ := Nat.mul_le_mul_right _ (card_filter_ge x₀)
    _ = (Finset.univ.filter (x₀ ≤ ·)).sum (fun _ => a x₀) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Finset.univ.filter (x₀ ≤ ·)).sum a :=
        Finset.sum_le_sum (fun i hi => by rw [Finset.mem_filter] at hi; exact ha x₀ i hi.2)
    _ ≤ Finset.univ.sum a := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem noninc_head_sum {m : ℕ} (b : Fin m → ℕ)
    (hb : ∀ i j : Fin m, i ≤ j → b j ≤ b i) (x₀ : Fin m) :
    (x₀.val + 1) * b x₀ ≤ Finset.univ.sum b :=
  calc (x₀.val + 1) * b x₀
      ≤ (Finset.univ.filter (· ≤ x₀)).card * b x₀ := Nat.mul_le_mul_right _ (card_filter_le x₀)
    _ = (Finset.univ.filter (· ≤ x₀)).sum (fun _ => b x₀) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Finset.univ.filter (· ≤ x₀)).sum b :=
        Finset.sum_le_sum (fun i hi => by rw [Finset.mem_filter] at hi; exact hb i x₀ hi.2)
    _ ≤ Finset.univ.sum b := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-! ## The depth threshold -/

theorem depth_threshold {m : ℕ} (hm : 2 ≤ m)
    (a b : Fin m → ℕ)
    (ha_mono : ∀ i j : Fin m, i ≤ j → a i ≤ a j)
    (hb_anti : ∀ i j : Fin m, i ≤ j → b j ≤ b i)
    (ha_bound : ∀ i, a i ≤ m) (hb_bound : ∀ i, b i ≤ m)
    (x₀ : Fin m) (hviolation : m + 1 ≤ a x₀ + b x₀)
    (d : ℕ) (hd_le : d ≤ x₀.val) (hd_le' : d ≤ m - 1 - x₀.val)
    (hd_half : 2 * d + 1 ≤ m) :
    2 * m + d * (m - 1) ≤ Finset.univ.sum (fun x => a x + b x) := by
  have haj : 1 ≤ a x₀ := by by_contra h; push_neg at h; have := hb_bound x₀; omega
  have hbk : 1 ≤ b x₀ := by by_contra h; push_neg at h; have := ha_bound x₀; omega
  rw [show Finset.univ.sum (fun x => a x + b x) = Finset.univ.sum a + Finset.univ.sum b
    from Finset.sum_add_distrib]
  have ha_tail := nondec_tail_sum a ha_mono x₀
  have hb_head := noninc_head_sum b hb_anti x₀
  -- Need: 2m + d(m-1) ≤ Σa + Σb
  -- Have: Σa ≥ (m-x₀)*a(x₀) and Σb ≥ (x₀+1)*b(x₀)
  -- So Σa + Σb ≥ (m-x₀)*a(x₀) + (x₀+1)*b(x₀)
  -- ≥ (m-x₀)*a(x₀) + (x₀+1)*(m+1-a(x₀))  [since b(x₀) ≥ m+1-a(x₀)]
  -- The last expression = a(x₀)*(m-2x₀-1) + (x₀+1)*(m+1)
  -- This is ≥ 2m+d(m-1) by the two-case argument (proved below).
  -- To stay in ℕ, we avoid the expansion and use a direct bound.

  -- Step 1: (x₀+1)*(m+1-a(x₀)) ≤ (x₀+1)*b(x₀)
  have hb_lower : m + 1 - a x₀ ≤ b x₀ := by omega
  have hstep1 : (x₀.val + 1) * (m + 1 - a x₀) ≤ (x₀.val + 1) * b x₀ :=
    Nat.mul_le_mul_left _ hb_lower

  -- Step 2: RHS := (m-x₀)*a(x₀) + (x₀+1)*b(x₀) ≥ (m-x₀)*a(x₀) + (x₀+1)*(m+1-a(x₀))
  -- Step 3: LHS ≤ RHS by two cases.
  -- We'll prove 2m+d(m-1) ≤ Σa + Σb using the chain:
  -- 2m+d(m-1) ≤ (m-x₀)*a(x₀)+(x₀+1)*b(x₀) ≤ Σa + Σb

  -- Combine: Σa+Σb ≥ (m-x₀)*a(x₀) + (x₀+1)*b(x₀) ≥ 2m+d(m-1)
  -- The second inequality is proved in ℤ via hkey below.
  -- The ℤ arithmetic proves the bound on pointwise products.
  -- The ℕ bound follows from ha_tail and hb_head.
  -- Bridge: we work entirely in ℕ and rely on nlinarith.
  -- The key ℕ facts: Σa ≥ (m-x₀)*a(x₀) and Σb ≥ (x₀+1)*b(x₀) and a+b ≥ m+1.
  -- Direct ℕ proof using omega would need multiplication, which omega can't do.
  -- So we prove the ℤ bound and transfer.
  suffices hkey : (2 * m + d * (m - 1) : ℤ) ≤
      (m - x₀.val : ℤ) * (a x₀ : ℤ) + ((x₀.val : ℤ) + 1) * (b x₀ : ℤ) by
    -- Transfer: the ℤ bound implies the ℕ bound because
    -- (m-x₀)*a(x₀) ≤ Σa and (x₀+1)*b(x₀) ≤ Σb (in ℕ),
    -- and the ℤ bound says 2m+d(m-1) ≤ (m-x₀)*a(x₀)+(x₀+1)*b(x₀) (in ℤ).
    -- Combining: 2m+d(m-1) ≤ Σa+Σb.
    -- The subtlety: (m-x₀.val) in ℕ = max(m-x₀.val, 0) but x₀ < m so it's fine.
    have hxm : x₀.val ≤ m := le_of_lt x₀.isLt
    -- In ℤ: ↑((m-x₀)*a(x₀)) = (↑m - ↑x₀)*(↑(a x₀)) when x₀ ≤ m
    have hcast1 : ((m - x₀.val) * a x₀ : ℤ) = (↑m - ↑x₀.val) * ↑(a x₀) := by
      push_cast [Nat.cast_sub hxm]; ring
    have hcast2 : ((x₀.val + 1) * b x₀ : ℤ) = (↑x₀.val + 1) * ↑(b x₀) := by push_cast; ring
    have hsum_z : (2 * m + d * (m - 1) : ℤ) ≤
        ((m - x₀.val) * a x₀ + (x₀.val + 1) * b x₀ : ℤ) := by
      push_cast [Nat.cast_sub hxm]; linarith
    have hnat : 2 * m + d * (m - 1) ≤ (m - x₀.val) * a x₀ + (x₀.val + 1) * b x₀ := by
      zify [hxm, show 1 ≤ m from by omega]; linarith
    linarith [Nat.add_le_add ha_tail hb_head]

  -- Pure ℤ arithmetic with products
  push_cast
  have hXM : (x₀.val : ℤ) < m := by exact_mod_cast x₀.isLt
  have hAM : (a x₀ : ℤ) ≤ m := by exact_mod_cast ha_bound x₀
  have hAJ : (1 : ℤ) ≤ a x₀ := by exact_mod_cast haj
  have hBlow : (m : ℤ) + 1 - a x₀ ≤ b x₀ := by push_cast; omega
  have hDX : (d : ℤ) ≤ x₀.val := by exact_mod_cast hd_le
  have hDX' : (d : ℤ) ≤ m - 1 - x₀.val := by push_cast; omega
  by_cases hcase : 2 * (x₀.val : ℤ) + 1 ≤ m
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ (a x₀ : ℤ) - 1 by linarith)
                          (show (0 : ℤ) ≤ (m : ℤ) - 2 * x₀.val - 1 by linarith),
               mul_nonneg (show (0 : ℤ) ≤ (x₀.val : ℤ) - d by linarith)
                          (show (0 : ℤ) ≤ (m : ℤ) - 1 by linarith)]
  · push_neg at hcase
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) - a x₀ by linarith)
                          (show (0 : ℤ) ≤ 2 * (x₀.val : ℤ) + 1 - m by linarith),
               mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) - 1 - x₀.val - d by linarith)
                          (show (0 : ℤ) ≤ (m : ℤ) - 1 by linarith)]

theorem no_violation_below_threshold {m : ℕ} (hm : 2 ≤ m)
    (a b : Fin m → ℕ) (ha_mono : ∀ i j : Fin m, i ≤ j → a i ≤ a j)
    (hb_anti : ∀ i j : Fin m, i ≤ j → b j ≤ b i)
    (ha_bound : ∀ i, a i ≤ m) (hb_bound : ∀ i, b i ≤ m)
    (d : ℕ) (hd_half : 2 * d + 1 ≤ m)
    (htotal : Finset.univ.sum (fun x => a x + b x) < 2 * m + d * (m - 1)) :
    ∀ x₀ : Fin m, d ≤ x₀.val → d ≤ m - 1 - x₀.val → a x₀ + b x₀ ≤ m := by
  intro x₀ hd1 hd2; by_contra h; push_neg at h
  exact absurd (depth_threshold hm a b ha_mono hb_anti ha_bound hb_bound x₀ h d hd1 hd2 hd_half)
    (by omega)

end
end CausalAlgebraicGeometry.DepthThreshold
