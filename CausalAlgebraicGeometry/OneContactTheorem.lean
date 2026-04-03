/-
  OneContactTheorem.lean — Single-violation structure for 2m ≤ k ≤ 3m-2.

  THEOREM: For monotone defect pairs with total k ≤ 3m-2,
  at most one violation can occur, and it must be at a boundary.

  Zero sorry.
-/
import CausalAlgebraicGeometry.DepthThreshold

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000

namespace CausalAlgebraicGeometry.OneContactTheorem

open CausalAlgebraicGeometry.DepthThreshold

noncomputable section
open scoped Classical

/-! ## Interior violations need total ≥ 3m-1 -/

/-- An interior violation (1 ≤ x₀ ≤ m-2) forces total ≥ 3m-1.
    Direct from depth_threshold at d = 1. -/
theorem interior_violation_lower_bound {m : ℕ} (hm : 3 ≤ m)
    (a b : Fin m → ℕ)
    (ha_mono : ∀ i j : Fin m, i ≤ j → a i ≤ a j)
    (hb_anti : ∀ i j : Fin m, i ≤ j → b j ≤ b i)
    (ha_bound : ∀ i, a i ≤ m) (hb_bound : ∀ i, b i ≤ m)
    (x₀ : Fin m) (hv : m + 1 ≤ a x₀ + b x₀)
    (hx_lo : 1 ≤ x₀.val) (hx_hi : x₀.val ≤ m - 2) :
    3 * m - 1 ≤ Finset.univ.sum (fun x => a x + b x) := by
  have := depth_threshold (by omega) a b ha_mono hb_anti ha_bound hb_bound
    x₀ hv 1 hx_lo (by omega) (by omega)
  omega

/-- Corollary: interior violations are impossible when total ≤ 3m-2. -/
theorem no_interior_violation {m : ℕ} (hm : 3 ≤ m)
    (a b : Fin m → ℕ)
    (ha_mono : ∀ i j : Fin m, i ≤ j → a i ≤ a j)
    (hb_anti : ∀ i j : Fin m, i ≤ j → b j ≤ b i)
    (ha_bound : ∀ i, a i ≤ m) (hb_bound : ∀ i, b i ≤ m)
    (htotal : Finset.univ.sum (fun x => a x + b x) ≤ 3 * m - 2)
    (x₀ : Fin m) (hv : m + 1 ≤ a x₀ + b x₀) :
    x₀.val = 0 ∨ x₀.val = m - 1 := by
  by_contra h; push_neg at h
  have hx_lo : 1 ≤ x₀.val := by omega
  have hx_hi : x₀.val ≤ m - 2 := by omega
  have := interior_violation_lower_bound hm a b ha_mono hb_anti ha_bound hb_bound x₀ hv hx_lo hx_hi
  omega

/-! ## Two endpoint violations need total ≥ 4m-2 -/

/-- Helper: extracting a single term from a Finset sum. -/
private theorem sum_ge_single_plus_rest {m : ℕ} (f : Fin m → ℕ)
    (x : Fin m) (c : ℕ) (hc : c ≤ f x)
    (hrest : ∀ i : Fin m, i ≠ x → 1 ≤ f i) :
    c + (m - 1) ≤ Finset.univ.sum f := by
  have hmem : x ∈ Finset.univ := Finset.mem_univ x
  -- Σf = f(x) + Σ_{i≠x} f(i)
  rw [← Finset.add_sum_erase _ _ hmem]
  -- f(x) ≥ c and Σ_{i≠x} f(i) ≥ m-1 (since each ≥ 1 and there are m-1 terms)
  apply Nat.add_le_add hc
  have hcard : (Finset.univ.erase x).card = m - 1 := by
    simp [Finset.card_erase_of_mem hmem]
  calc m - 1 = (Finset.univ.erase x).card * 1 := by omega
    _ = (Finset.univ.erase x).sum (fun _ => (1 : ℕ)) := by
        rw [Finset.sum_const]; simp [smul_eq_mul]
    _ ≤ (Finset.univ.erase x).sum f :=
        Finset.sum_le_sum (fun i hi => by
          rw [Finset.mem_erase] at hi; exact hrest i hi.1)

/-- Key arithmetic: if S₁ ≥ m·α and S₂ ≥ c+(m-1) and c ≥ m+1-α
    and α ≥ 1 and α ≤ m and m ≥ 2, then S₁+S₂ ≥ 2m-1.
    Combined with symmetric bound, gives total ≥ 4m-2. -/
private theorem endpoint_bound_aux (m α c S : ℕ)
    (hm : 2 ≤ m) (hα : 1 ≤ α) (hαm : α ≤ m)
    (hc : m + 1 - α ≤ c)
    (hS_first : m * α ≤ S) (hS_second : c + (m - 1) ≤ S) :
    2 * m - 1 ≤ S := by
  by_cases h : α = 1
  · omega  -- c ≥ m, so S ≥ m + (m-1) = 2m-1
  · have : 2 ≤ α := by omega
    have : m * 2 ≤ m * α := Nat.mul_le_mul_left m this
    omega  -- S ≥ m·α ≥ 2m > 2m-1

/-- Two violations at x₀ = 0 and x₁ = m-1 force total ≥ 4m-2.
    Proof: a(0) ≥ 1 and b(m-1) ≥ 1 (from violations + bounds).
    If both equal 1, then a(m-1) = m and b(0) = m.
    Σa ≥ m + (m-1) = 2m-1 and Σb ≥ m + (m-1) = 2m-1.
    Total ≥ 4m-2. -/
theorem two_endpoint_violations_lower_bound {m : ℕ} (hm : 2 ≤ m)
    (a b : Fin m → ℕ)
    (ha_mono : ∀ i j : Fin m, i ≤ j → a i ≤ a j)
    (hb_anti : ∀ i j : Fin m, i ≤ j → b j ≤ b i)
    (ha_bound : ∀ i, a i ≤ m) (hb_bound : ∀ i, b i ≤ m)
    (x₀ x₁ : Fin m) (hne : x₀ ≠ x₁)
    (hx0 : x₀.val = 0) (hx1 : x₁.val = m - 1)
    (hv0 : m + 1 ≤ a x₀ + b x₀)
    (hv1 : m + 1 ≤ a x₁ + b x₁) :
    4 * m - 2 ≤ Finset.univ.sum (fun x => a x + b x) := by
  -- a(x₀) ≥ 1 and b(x₁) ≥ 1
  have ha0 : 1 ≤ a x₀ := by have := hb_bound x₀; omega
  have hbm : 1 ≤ b x₁ := by have := ha_bound x₁; omega
  -- All a values ≥ 1 (nondec from a(0) ≥ 1)
  have ha_ge1 : ∀ i : Fin m, 1 ≤ a i := fun i =>
    le_trans ha0 (ha_mono x₀ i (by rw [Fin.le_def, hx0]; exact Nat.zero_le _))
  -- All b values ≥ 1 (noninc from b(m-1) ≥ 1)
  have hb_ge1 : ∀ i : Fin m, 1 ≤ b i := fun i =>
    le_trans hbm (hb_anti i x₁ (by rw [Fin.le_def, hx1]; exact Nat.le_sub_one_of_lt i.isLt))
  -- a(x₁) ≥ m (from violation: a(x₁) ≥ m+1-b(x₁) ≥ m+1-m ≥ 1; but also ≥ m+1-1 = m when b(x₁)=1)
  -- Actually: a(x₁) + b(x₁) ≥ m+1, so a(x₁) ≥ m+1-b(x₁).
  -- And a(x₁) ≤ m. So a(x₁) ≥ m+1-m = 1 at minimum.
  -- But we need a(x₁) ≥ m for the 2m-1 bound. This requires b(x₁) = 1.
  -- General approach: Σa ≥ a(x₁) + (m-1) (from a(x₁) + rest ≥ 1 each)
  -- And Σb ≥ b(x₀) + (m-1). Total ≥ a(x₁)+b(x₀) + 2(m-1).
  -- From x₁: a(x₁) ≥ m+1-b(x₁). From x₀: b(x₀) ≥ m+1-a(x₀).
  -- Also a(x₁) ≥ a(x₀) (nondec) and b(x₀) ≥ b(x₁) (noninc).
  -- a(x₁) + b(x₀) ≥ (m+1-b(x₁)) + (m+1-a(x₀)) = 2m+2 - (a(x₀)+b(x₁)).
  -- And a(x₀)+b(x₁) ≤ m+m = 2m, so a(x₁)+b(x₀) ≥ 2.
  -- Also a(x₀) ≤ a(x₁) ≤ m and b(x₁) ≤ b(x₀) ≤ m.
  -- Let me just bound: a(x₁)+b(x₀) ≥ (m+1-b(x₁)) + (m+1-a(x₀)).
  -- With a(x₀)+b(x₁) ≤ m (since all non-violation terms have a+b ≤ m)...
  -- Wait, x₀ IS a violation point! So a(x₀)+b(x₀) ≥ m+1, not ≤ m.
  -- OK. a(x₁)+b(x₀) ≥ (m+1-b(x₁)) + (m+1-a(x₀)) = 2(m+1) - (a(x₀)+b(x₁)).

  -- Hmm, let me use the sum extraction approach directly.
  -- Σa ≥ a(x₁) + (m-1) [using sum_ge_single_plus_rest with all a ≥ 1]
  have hSa : a x₁ + (m - 1) ≤ Finset.univ.sum a :=
    sum_ge_single_plus_rest a x₁ (a x₁) le_rfl (fun i _ => ha_ge1 i)
  -- Σb ≥ b(x₀) + (m-1)
  have hSb : b x₀ + (m - 1) ≤ Finset.univ.sum b :=
    sum_ge_single_plus_rest b x₀ (b x₀) le_rfl (fun i _ => hb_ge1 i)
  -- Total = Σa + Σb
  have htot : Finset.univ.sum (fun x => a x + b x) =
      Finset.univ.sum a + Finset.univ.sum b := Finset.sum_add_distrib
  -- a(x₁) + b(x₀) ≥ (m+1-b(x₁)) + (m+1-a(x₀)) = 2m+2-(a(x₀)+b(x₁))
  -- Need: 4m-2 ≤ a(x₁)+(m-1) + b(x₀)+(m-1) = a(x₁)+b(x₀)+2m-2
  -- i.e., a(x₁)+b(x₀) ≥ 2m.
  -- a(x₁) ≥ m+1-b(x₁) and b(x₀) ≥ m+1-a(x₀).
  -- So a(x₁)+b(x₀) ≥ 2m+2-(a(x₀)+b(x₁)).
  -- We need a(x₀)+b(x₁) ≤ 2, i.e., a(x₀) ≤ 1 and b(x₁) ≤ 1.
  -- But we only know a(x₀) ≥ 1, so a(x₀) ≥ 1, and similarly b(x₁) ≥ 1.
  -- So a(x₀)+b(x₁) ≥ 2, giving a(x₁)+b(x₀) ≥ 2m+2-2m = ... wait that's ≥ 2m+2-(a(x₀)+b(x₁)).
  -- We need a(x₁)+b(x₀) ≥ 2m. Using a(x₀)+b(x₁) ≤ ???
  -- Actually a(x₀) ≤ m and b(x₁) ≤ m so a(x₀)+b(x₁) ≤ 2m.
  -- a(x₁)+b(x₀) ≥ 2m+2-2m = 2. That's way too weak.

  -- Better: a(x₁) ≥ a(x₀) and b(x₀) ≥ b(x₁) (monotonicity).
  -- From hv0: a(x₀)+b(x₀) ≥ m+1. So b(x₀) ≥ m+1-a(x₀) ≥ m+1-m = 1.
  -- From hv1: a(x₁)+b(x₁) ≥ m+1. So a(x₁) ≥ m+1-b(x₁) ≥ m+1-m = 1.
  -- Direct: a(x₁)+b(x₀) ≥ a(x₁)+m+1-a(x₀) [from hv0: b(x₀) ≥ m+1-a(x₀)]
  --        ≥ (m+1-b(x₁))+m+1-a(x₀)  [from hv1: a(x₁) ≥ m+1-b(x₁)]
  --        = 2m+2-a(x₀)-b(x₁).
  -- With a(x₀) ≤ m and b(x₁) ≤ m: ≥ 2.
  -- With a(x₀)=1, b(x₁)=1: ≥ 2m. Then total ≥ 2m+2(m-1) = 4m-2.

  -- The general case: total ≥ a(x₁)+b(x₀)+2(m-1) ≥ 2m+2-a(x₀)-b(x₁)+2m-2 = 4m-a(x₀)-b(x₁).
  -- Need 4m-a(x₀)-b(x₁) ≥ 4m-2, i.e., a(x₀)+b(x₁) ≤ 2.
  -- Since a(x₀) ≥ 1 and b(x₁) ≥ 1: a(x₀)+b(x₁) ≥ 2.
  -- So a(x₀)+b(x₁) = 2, giving total ≥ 4m-2. But this only works when a(x₀)=1, b(x₁)=1!
  -- For a(x₀) ≥ 2 or b(x₁) ≥ 2: need different bound.

  -- Alternative: Σa ≥ m·a(x₀) [nondec_tail_sum at x₀, since all ≥ a(x₀)].
  --             Σb ≥ m·b(x₁) [noninc_head_sum at x₁, since all ≥ b(x₁)].
  -- Also Σa ≥ a(x₁)+(m-1) and Σb ≥ b(x₀)+(m-1).
  -- So Σa ≥ max(m·a(x₀), a(x₁)+(m-1)) and Σb ≥ max(m·b(x₁), b(x₀)+(m-1)).
  -- Total ≥ m·a(x₀) + m·b(x₁) + ???
  -- No, can't add two bounds on the same quantity.

  -- Use the ℤ approach from DepthThreshold.
  -- Total = Σa + Σb ≥ m·a(x₀) + m·b(x₁) (combining ha_lower + hb_lower, both full-range bounds)
  -- Also total ≥ a(x₁)+(m-1) + b(x₀)+(m-1) (combining hSa + hSb, extraction bounds)
  -- Take the MAX: total ≥ max(m(α+β), a(x₁)+b(x₀)+2m-2).
  -- If α+β ≥ 4: m·4 = 4m ≥ 4m-2 ✓.
  -- If α+β = 3: m·3 = 3m. Need 3m ≥ 4m-2, so m ≤ 2. Contradicts m ≥ 4... wait, we need 4m-2, not 3m-2.
  -- Hmm. 3m ≥ 4m-2 iff m ≤ 2. For m ≥ 3 this fails.
  -- Need the OTHER bound: a(x₁)+b(x₀)+2m-2.
  -- a(x₁) ≥ m+1-β and b(x₀) ≥ m+1-α.
  -- So a(x₁)+b(x₀) ≥ 2m+2-(α+β) = 2m+2-3 = 2m-1.
  -- Total ≥ 2m-1+2m-2 = 4m-3. For m ≥ 4: 4m-3 ≥ 4m-2? No, 4m-3 < 4m-2.

  -- Hmm, I need a tighter analysis. Let me combine BOTH bounds on Σa:
  -- Σa ≥ m·α and Σa ≥ a(x₁)+(m-1)·1.
  -- Σb ≥ m·β and Σb ≥ b(x₀)+(m-1)·1.
  -- From hv1: a(x₁) ≥ m+1-β. From hv0: b(x₀) ≥ m+1-α.
  -- Using SECOND bound: Σa ≥ m+1-β+m-1 = 2m-β.
  -- Using SECOND bound: Σb ≥ m+1-α+m-1 = 2m-α.
  -- Total ≥ (2m-β) + (2m-α) = 4m-(α+β).
  -- Need 4m-(α+β) ≥ 4m-2, i.e., α+β ≤ 2.
  -- But α ≥ 1, β ≥ 1, so α+β ≥ 2. So α+β = 2 gives total ≥ 4m-2. ✓
  -- α+β ≥ 3: use FIRST bounds: total ≥ m(α+β) ≥ 3m. For m ≥ 4: 3m ≥ 12 ≥ 4m-2 iff m ≤ 4.
  -- So for m = 3: 3·3 = 9 vs 4·3-2 = 10. 9 < 10. Need second bound.
  -- For α+β = 3: second bound gives total ≥ 4m-3 < 4m-2. NOT ENOUGH.

  -- WAIT. For α+β = 3: say α = 1, β = 2.
  -- Σa ≥ m·1 = m and Σa ≥ m+1-2+m-1 = 2m-2.
  -- Σb ≥ m·2 = 2m and Σb ≥ m+1-1+m-1 = 2m-1.
  -- Take Σa ≥ 2m-2, Σb ≥ 2m. Total ≥ 4m-2. ✓!
  -- Or α = 2, β = 1: Σa ≥ 2m, Σb ≥ 2m-2. Total ≥ 4m-2. ✓

  -- So for α+β ≤ 2: use second bounds (total ≥ 4m-α-β ≥ 4m-2 ✓)
  -- For α+β = 3: use first bound for the ≥ 2 value and second for the = 1 value.
  -- For α+β ≥ 4: use first bounds (total ≥ 4m ≥ 4m-2 ✓).

  -- General: total ≥ max(mα, 2m-β) + max(mβ, 2m-α)
  -- ≥ mα + 2m-α = (m-1)α + 2m ≥ 2m (trivially). Not tight enough.

  -- Actually the simplest: use FIRST for Σb and SECOND for Σa (or vice versa).
  -- Σa ≥ 2m-β and Σb ≥ mβ.
  -- Total ≥ 2m-β+mβ = 2m+β(m-1) ≥ 2m+(m-1) = 3m-1. For m ≥ 4: 3m-1 ≥ 11.
  -- But we need 4m-2. 3m-1 < 4m-2 for m ≥ 2.

  -- OK, I need to use BOTH first bounds and BOTH second bounds simultaneously. Let me use ℤ.
  -- In ℤ: Σa ≥ mα and Σa ≥ 2m-β.
  -- If mα ≥ 2m-β, use mα, else use 2m-β.
  -- Worst case for total: minimize max(mα,2m-β)+max(mβ,2m-α) over α,β ≥ 1.

  -- Let f(α,β) = max(mα,2m-β)+max(mβ,2m-α).
  -- At α=β=1: max(m,2m-1)+max(m,2m-1) = (2m-1)+(2m-1) = 4m-2.
  -- At α=1,β=2: max(m,2m-2)+max(2m,2m-1) = (2m-2)+2m = 4m-2.
  -- At α=2,β=1: max(2m,2m-1)+max(m,2m-2) = 2m+(2m-2) = 4m-2.
  -- At α=2,β=2: max(2m,2m-2)+max(2m,2m-2) = 2m+2m = 4m.
  -- So f(α,β) ≥ 4m-2 always! That's the result.

  -- Proof: f(α,β) = max(mα,2m-β)+max(mβ,2m-α) ≥ mα+2m-α = (m-1)α+2m ≥ 3m-1.
  -- Wait, that only gives 3m-1. Need to be smarter.
  -- f(α,β) ≥ max(mα+mβ, mα+2m-α, 2m-β+mβ, 2m-β+2m-α)
  --        = max(m(α+β), (m-1)α+2m, (m-1)β+2m, 4m-(α+β))
  -- For the last term: ≥ 4m-2m = 2m (α+β ≤ 2m). Not useful alone.
  -- But 4m-(α+β) ≥ 4m-2 when α+β ≤ 2. And m(α+β) ≥ 4m-2 when α+β ≥ 4-2/m, so α+β ≥ 4 gives ≥ 4m.
  -- For α+β = 3: max(3m, ..., ..., 4m-3) = max(3m, ...).
  -- (m-1)α+2m with α+β=3: if α=1: m-1+2m=3m-1. If α=2: 2m-2+2m=4m-2. ✓
  -- So for α=2: (m-1)·2+2m = 4m-2. ✓

  -- General proof that f(α,β) ≥ 4m-2:
  -- Case α ≥ 2: max(mα,2m-β) ≥ mα ≥ 2m. And max(mβ,2m-α) ≥ 2m-α ≥ 2m-m = m.
  --   Wait that gives ≥ 2m+m = 3m. Still not 4m-2.
  --   Better: max(mα,2m-β) ≥ 2m (since mα ≥ 2m). max(mβ,2m-α) ≥ 2m-2 (since α ≤ m, so 2m-α ≥ m ≥ 2... hmm).
  --   Actually: max(mβ,2m-α) ≥ 2m-α ≥ 2m-m = m. So total ≥ 2m+m = 3m. Not 4m-2.
  --   BUT: max(mβ,2m-α) ≥ mβ ≥ m (since β ≥ 1). AND max(mβ,2m-α) ≥ 2m-α.
  --   For α = 2: 2m-α = 2m-2. So max ≥ 2m-2. Total ≥ 2m + 2m-2 = 4m-2. ✓

  -- OK I think the cleanest Lean proof is: prove via ℤ with nlinarith and the four bounds.

  -- The four bounds:
  have h_Sa1 := nondec_tail_sum a ha_mono x₀  -- Σa ≥ (m-x₀)·a(x₀) = m·a(x₀)
  have h_Sb1 := noninc_head_sum b hb_anti x₁  -- Σb ≥ (x₁+1)·b(x₁) = m·b(x₁)
  -- Rewrite with x₀.val = 0 and x₁.val = m-1
  have hSa_first : m * a x₀ ≤ Finset.univ.sum a := by
    have := h_Sa1; rw [show m - x₀.val = m from by omega] at this; exact this
  have hSb_first : m * b x₁ ≤ Finset.univ.sum b := by
    have := h_Sb1; rw [show x₁.val + 1 = m from by omega] at this; exact this
  -- Second bounds from extraction:
  -- Σa ≥ a(x₁) + (m-1) where a(x₁) ≥ m+1-b(x₁)
  -- Σb ≥ b(x₀) + (m-1) where b(x₀) ≥ m+1-a(x₀)
  have hax1_lower : m + 1 - b x₁ ≤ a x₁ := by omega
  have hbx0_lower : m + 1 - a x₀ ≤ b x₀ := by omega
  have hSa_second : m + 1 - b x₁ + (m - 1) ≤ Finset.univ.sum a :=
    sum_ge_single_plus_rest a x₁ (m + 1 - b x₁) hax1_lower (fun i _ => ha_ge1 i)
  have hSb_second : m + 1 - a x₀ + (m - 1) ≤ Finset.univ.sum b :=
    sum_ge_single_plus_rest b x₀ (m + 1 - a x₀) hbx0_lower (fun i _ => hb_ge1 i)
  -- Now combine in ℤ: total ≥ max(m·α, 2m-β) + max(m·β, 2m-α) ≥ 4m-2.
  rw [htot]
  -- Have four bounds, need to show 4m-2 ≤ Σa + Σb.
  -- Strategy: Σa ≥ max(m·α, 2m-β) and Σb ≥ max(m·β, 2m-α).
  -- Use: Σa+Σb ≥ m·α + (2m-α) = (m-1)α+2m when we mix first+second.
  -- Or: Σa+Σb ≥ (2m-β) + m·β = (m-1)β+2m.
  -- Or: Σa+Σb ≥ (2m-β)+(2m-α) = 4m-(α+β).
  -- Or: Σa+Σb ≥ m·α+m·β = m(α+β).
  -- Combine: ≥ max(m(α+β), 4m-(α+β)).
  -- For α+β ≤ 2: 4m-(α+β) ≥ 4m-2. ✓
  -- For α+β ≥ 4: m(α+β) ≥ 4m ≥ 4m-2. ✓
  -- For α+β = 3: need min over (α,β) with α+β=3, α,β ≥ 1.
  --   max(3m, 4m-3). For m ≥ 3: 3m ≥ 4m-3 iff m ≤ 3. Hmm.
  --   For m = 3: max(9, 9) = 9 ≥ 10? NO! 9 < 10.
  --   BUT m ≥ 4 is given. For m = 4: max(12, 13) = 13 ≥ 14? NO! 13 < 14.
  --   This approach isn't working for α+β = 3.
  --   Need the mixed bound: Σa+Σb ≥ m·α + (2m-α) = (m-1)α+2m.
  --   For α = 2, β = 1: (m-1)·2+2m = 4m-2. ✓
  --   For α = 1, β = 2: use Σa+Σb ≥ (2m-β)+m·β = (m-1)·2+2m = 4m-2. ✓

  -- The trick: for α+β = 3, one of α,β ≥ 2. WLOG α ≥ 2. Then Σa ≥ mα ≥ 2m and Σb ≥ 2m-α ≥ 2m-m = m.
  -- Total ≥ 2m + max(mβ, 2m-α). With α ≥ 2, β ≥ 1: mβ ≥ m and 2m-α ≥ m.
  -- For α = 2: total ≥ 2m + max(m, 2m-2) = 2m + 2m-2 = 4m-2. ✓ (since m ≥ 4 > 2)

  -- General ℤ argument:
  -- total ≥ max(mα, 2m-β) + max(mβ, 2m-α).
  -- If α ≥ 2: total ≥ mα + 2m-α = (m-1)α + 2m ≥ 2(m-1)+2m = 4m-2. ✓
  -- If β ≥ 2: total ≥ 2m-β + mβ = (m-1)β + 2m ≥ 2(m-1)+2m = 4m-2. ✓
  -- If α = β = 1: total ≥ 2m-1 + 2m-1 = 4m-2. ✓
  -- Done! Because at least one of: α ≥ 2, β ≥ 2, or α = β = 1 must hold (since α,β ≥ 1).

  -- Lean proof: case split on whether a(x₀) ≥ 2.
  -- Derive: m+1-a(x₀) ≤ a(x₁) and m+1-b(x₁) ≤ b(x₀)
  -- From: a(x₀)+b(x₀) ≥ m+1 → b(x₀) ≥ m+1-a(x₀)
  --       b(x₁) ≤ b(x₀) (noninc) and a(x₁)+b(x₁) ≥ m+1 → a(x₁) ≥ m+1-b(x₁) ≥ m+1-b(x₀)
  --       But we need m+1-a(x₀) ≤ a(x₁). Since a(x₁) ≥ a(x₀) (nondec):
  --       m+1-a(x₀) ≤ m ≤ ... not necessarily ≤ a(x₁).
  -- Actually: from hv1, a(x₁) ≥ m+1-b(x₁). And b(x₁) ≤ b(x₀). And b(x₀) ≤ m.
  -- And from hv0: b(x₀) ≥ m+1-a(x₀).
  -- So a(x₁) ≥ m+1-b(x₁) ≥ m+1-b(x₀) ≥ m+1-m = 1. Not enough.
  -- Key insight: we need m+1-a(x₀) ≤ a(x₁), NOT m+1-b(x₁) ≤ a(x₁).
  -- This follows if a(x₁) ≥ a(x₀) and m+1-a(x₀) ≤ a(x₀),
  -- i.e., a(x₀) ≥ (m+1)/2. Only when α is large enough!
  -- For small α: need the c+m-1 bound to carry the weight (α=1 case in helper).
  -- The helper's condition is: m+1-α ≤ c. For α = a(x₀), c = a(x₁):
  -- Need m+1-a(x₀) ≤ a(x₁). From hv1: a(x₁) ≥ m+1-b(x₁).
  -- And from b(x₁) ≤ b(x₀) and hv0: b(x₀) ≥ m+1-a(x₀), so b(x₁) ≤ b(x₀) ≤ m.
  -- Need: m+1-a(x₀) ≤ m+1-b(x₁). This iff b(x₁) ≤ a(x₀).
  -- b(x₁) ≤ b(x₀) ≤ m and a(x₀) ≥ 1. Not necessarily b(x₁) ≤ a(x₀).
  -- Example: m=4, a(x₀)=1, b(x₁)=3. Then m+1-a(x₀) = 4, a(x₁) ≥ m+1-b(x₁) = 2. 4 > 2.
  -- So the condition DOESN'T hold in general! The helper needs a different formulation.

  -- Alternative: forget the helper. Do the case split directly here.
  -- Case a(x₀) = 1: a(x₁) ≥ m+1-b(x₁) and b(x₁) ≥ 1 so a(x₁) ≥ m+1-m = m... wait.
  --   b(x₁) ≤ m. a(x₁) ≥ m+1-b(x₁) ≥ 1. But b(x₁) = 1 gives a(x₁) ≥ m.
  --   Actually b(x₁) is free. From Σa ≥ a(x₁) + (m-1):
  --   If a(x₁) ≥ m: Σa ≥ m + m - 1 = 2m-1. ✓
  --   If a(x₁) < m: need Σa ≥ m·1 = m from tail sum. And a(x₁) + (m-1) < m + m - 1 = 2m-1.
  --     Both bounds give Σa ≥ max(m, a(x₁)+m-1). With a(x₁) ≥ m+1-b(x₁):
  --     Σa ≥ max(m, m+1-b(x₁)+m-1) = max(m, 2m-b(x₁)).
  --     Similarly Σb ≥ max(m, 2m-a(x₀)).
  --     With a(x₀)=1: Σb ≥ max(m, 2m-1) = 2m-1.
  --     So Σb ≥ 2m-1 and Σa ≥ m. Total ≥ 3m-1. Not 4m-2.
  --     Need Σa ≥ 2m-1 too. Σa ≥ 2m-b(x₁). And Σb ≥ 2m-1.
  --     Total ≥ 2m-b(x₁) + 2m-1 = 4m-1-b(x₁). For b(x₁) ≤ 1: ≥ 4m-2. ✓
  --     For b(x₁) = 2: ≥ 4m-3. Not enough!

  -- Hmm, this doesn't work with just the extraction bound alone.
  -- The two_endpoint case needs BOTH bounds on BOTH sums.
  -- I was overcomplicating it. Let me use the depth_threshold directly for this case.
  -- Two violations at 0 and m-1. Use depth_threshold at x₀ with d = x₀.val = 0:
  -- gives total ≥ 2m. At x₁ with d = 0: gives total ≥ 2m. Neither is 4m-2.
  -- Actually: I can use the full two-violation argument from the depth_threshold approach.
  -- depth_threshold at x₁ = m-1 with d = 0: need 0 ≤ x₁.val = m-1 ✓ and 0 ≤ m-1-x₁.val = 0 ✓.
  -- This gives 2*m + 0*(m-1) = 2m ≤ total. Not enough.

  -- The REAL proof: from the DepthThreshold file, depth_threshold with d gives T_d = (d+2)m-d.
  -- With TWO violations at 0 and m-1: not a single-violation setup.
  -- Need to prove the two-violation case separately.

  -- Direct combinatorial argument:
  -- Each a(i)+b(i) ≥ 2 (from ha_ge1, hb_ge1). There are m terms.
  -- Two of them (i=x₀, i=x₁) satisfy a(i)+b(i) ≥ m+1.
  -- Rest (m-2 terms) satisfy a(i)+b(i) ≥ 2.
  -- Total ≥ 2(m+1) + 2(m-2) = 2m+2+2m-4 = 4m-2.
  -- This REQUIRES we can separate x₀ and x₁ as distinct terms!

  -- Formalize via Finset sum extraction.
  have hab_ge2 : ∀ i : Fin m, 2 ≤ a i + b i := fun i => by
    have := ha_ge1 i; have := hb_ge1 i; omega
  -- Σ(a+b) = (a(x₀)+b(x₀)) + (a(x₁)+b(x₁)) + Σ_{i∉{x₀,x₁}} (a(i)+b(i))
  -- ≥ (m+1) + (m+1) + 2·(m-2) = 4m-2.
  let f := fun x : Fin m => a x + b x
  have hmem0 : x₀ ∈ Finset.univ := Finset.mem_univ x₀
  have hmem1_e : x₁ ∈ Finset.univ.erase x₀ := by
    rw [Finset.mem_erase]; exact ⟨hne.symm, Finset.mem_univ _⟩
  -- Extract x₀
  have hstep1 : Finset.univ.sum f = f x₀ + (Finset.univ.erase x₀).sum f := by
    rw [Finset.add_sum_erase _ _ hmem0]
  -- Extract x₁ from the erased set
  have hstep2 : (Finset.univ.erase x₀).sum f = f x₁ + ((Finset.univ.erase x₀).erase x₁).sum f := by
    rw [Finset.add_sum_erase _ _ hmem1_e]
  -- Rest has m-2 terms, each ≥ 2
  have hcard_rest : ((Finset.univ.erase x₀).erase x₁).card = m - 2 := by
    rw [Finset.card_erase_of_mem hmem1_e, Finset.card_erase_of_mem hmem0]
    simp [Finset.card_univ, Fintype.card_fin]; omega
  have hrest : 2 * (m - 2) ≤ ((Finset.univ.erase x₀).erase x₁).sum f := by
    calc 2 * (m - 2) = (m - 2) * 2 := by ring
      _ = ((Finset.univ.erase x₀).erase x₁).card * 2 := by rw [hcard_rest]
      _ = ((Finset.univ.erase x₀).erase x₁).sum (fun _ => 2) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ((Finset.univ.erase x₀).erase x₁).sum f :=
          Finset.sum_le_sum (fun i _ => hab_ge2 i)
  -- Combine: need 4m-2 ≤ Σ(a+b). Since Σ(a+b) = Σf, use the decomposition.
  -- The goal is about Finset.univ.sum a + Finset.univ.sum b (from htot rewrite).
  -- Rewrite back to Σ(a+b) = Σf.
  rw [← Finset.sum_add_distrib]
  -- Now goal: 4m-2 ≤ Σf where f = fun x => a x + b x
  change 4 * m - 2 ≤ Finset.univ.sum f
  rw [hstep1, hstep2]
  -- f x₀ = a x₀ + b x₀ ≥ m+1, f x₁ = a x₁ + b x₁ ≥ m+1, rest ≥ 2(m-2)
  show 4 * m - 2 ≤ f x₀ + (f x₁ + ((Finset.univ.erase x₀).erase x₁).sum f)
  have hf0 : m + 1 ≤ f x₀ := hv0
  have hf1 : m + 1 ≤ f x₁ := hv1
  omega

end
end CausalAlgebraicGeometry.OneContactTheorem
