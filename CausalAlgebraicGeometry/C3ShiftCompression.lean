/-
  C3ShiftCompression.lean — Finite shift/compression core of the c₃ argument.

  Suppose a large family T of boxed plane partitions lies in a vertical tube
  of radius k around an integer barrier b.  Shift every member of T down by k
  to obtain a profile below b, and shift every member up by k+1 to obtain a
  profile strictly above b.

  A down-shift forgets only the residual min(h,k), itself an antitone profile
  of height at most k.  Thus every fiber is bounded by one thin-box
  plane-partition count.  The same statement for the up-shift follows from
  the analogous upper residual.  Combining the two compression maps with the
  barrier product theorem gives the exact finite inequality proved at the end:

    |T|^2 <= Q(m) * Thin(m,k) * Thin(m,k+1).

  Analytically, uniform limit-shape concentration supplies k=o(m) and
  |T|=(1-o(1))*PP(m,m,m), while MacMahon gives
  log Thin(m,k) <= 2mk=o(m^2).  This closes the c₃ entropy lower bound once
  those standard external asymptotic inputs are connected to the finite
  objects here.  Zero sorry.
-/
import CausalAlgebraicGeometry.C3BarrierLowerBound

namespace CausalAlgebraicGeometry.C3ShiftCompression

open CausalAlgebraicGeometry.C3BarrierLowerBound
open CausalAlgebraicGeometry.C3Conjecture
open CausalAlgebraicGeometry.FullSupportLowerBound

noncomputable section
open scoped Classical

/-- Antitone profiles on `[m]^d` with an independent height bound `k`.
For `d=2`, these are plane partitions in an `m x m x k` box. -/
structure ThinProfile (d m k : ℕ) where
  toFun : (Fin d → Fin m) → Fin (k + 1)
  antitone : Antitone toFun

theorem ThinProfile.ext {d m k : ℕ} {p q : ThinProfile d m k}
    (h : p.toFun = q.toFun) : p = q := by
  cases p
  cases q
  cases h
  rfl

instance (d m k : ℕ) : Fintype (ThinProfile d m k) := by
  classical
  apply Fintype.ofInjective (fun p : ThinProfile d m k => p.toFun)
  intro p q h
  exact ThinProfile.ext h

/-- Forget the strict ordering in a full-support pair. -/
def profilePairOfFullSupport {d m : ℕ} (p : FullSupportPair d m) :
    AntitoneProfile d m × AntitoneProfile d m :=
  (⟨fun f => ⟨p.phi f, by
      have hlt := p.phi_lt_psi f
      have hle := p.psi_le_m f
      omega⟩,
    by
      intro f g hfg
      exact Fin.mk_le_mk.mpr (p.phi_antitone hfg)⟩,
   ⟨fun f => ⟨p.psi f, by
      have hle := p.psi_le_m f
      omega⟩,
    by
      intro f g hfg
      exact Fin.mk_le_mk.mpr (p.psi_antitone hfg)⟩)

theorem profilePairOfFullSupport_injective {d m : ℕ} :
    Function.Injective (profilePairOfFullSupport (d := d) (m := m)) := by
  intro p q hpq
  apply FullSupportPair.ext
  · funext f
    have h := congrArg (fun z => (z.1.toFun f).val) hpq
    exact h
  · funext f
    have h := congrArg (fun z => (z.2.toFun f).val) hpq
    exact h

/-- The elementary matching upper bound: `Q(m)` is at most the square of the
one-profile count. -/
theorem Q_le_profile_square (m : ℕ) :
    Q m ≤ Fintype.card (AntitoneProfile 2 m) ^ 2 := by
  unfold Q
  rw [pow_two, ← Fintype.card_prod]
  exact Fintype.card_le_of_injective profilePairOfFullSupport
    profilePairOfFullSupport_injective

/-- Remove `k` vertical units, truncating at zero. -/
def downShift {d m : ℕ} (k : ℕ) (p : AntitoneProfile d m) :
    AntitoneProfile d m where
  toFun f := ⟨(p.toFun f).val - k, by omega⟩
  antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    have hp := Fin.le_def.mp (p.antitone hfg)
    omega

/-- The data discarded by `downShift`: `min(h,k)`. -/
def lowerResidual {d m : ℕ} (k : ℕ) (p : AntitoneProfile d m) :
    ThinProfile d m k where
  toFun f := ⟨min (p.toFun f).val k, by omega⟩
  antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    have hp := Fin.le_def.mp (p.antitone hfg)
    omega

/-- A height is recovered from its truncated down-shift and its lower
residual.  Hence each down-shift fiber injects into a thin-box profile set. -/
theorem downShift_lowerResidual_injective {d m : ℕ} (k : ℕ) :
    Function.Injective
      (fun p : AntitoneProfile d m => (downShift k p, lowerResidual k p)) := by
  intro p q hpq
  apply AntitoneProfile.ext
  funext f
  apply Fin.ext
  have hdown := congrArg (fun z => (z.1.toFun f).val) hpq
  have hres := congrArg (fun z => (z.2.toFun f).val) hpq
  simp only [downShift, lowerResidual] at hdown hres
  omega

/-- Add `k` vertical units, truncating at the top of the box. -/
def upShift {d m : ℕ} (k : ℕ) (p : AntitoneProfile d m) :
    AntitoneProfile d m where
  toFun f := ⟨min ((p.toFun f).val + k) m, by omega⟩
  antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    have hp := Fin.le_def.mp (p.antitone hfg)
    omega

/-- The upper residual, rotated so that it is again antitone. -/
def upperResidual {d m : ℕ} (k : ℕ) (p : AntitoneProfile d m) :
    ThinProfile d m k :=
  lowerResidual k (dualProfile p)

/-- An upper-truncated height is recovered from its up-shift and rotated
upper residual. -/
theorem upShift_upperResidual_injective {d m : ℕ} (k : ℕ) :
    Function.Injective
      (fun p : AntitoneProfile d m => (upShift k p, upperResidual k p)) := by
  intro p q hpq
  apply AntitoneProfile.ext
  funext f
  apply Fin.ext
  have hup := congrArg (fun z => (z.1.toFun f).val) hpq
  have hres := congrArg (fun z => (z.2.toFun (rotatePoint f)).val) hpq
  simp only [upShift, upperResidual, lowerResidual, dualProfile,
    rotatePoint_involutive] at hup hres
  have hpfin := (p.toFun f).isLt
  have hqfin := (q.toFun f).isLt
  omega

/-- Profiles in the two-sided vertical tube of radius `k` around `b`. -/
def LimitTube (d m : ℕ) (b : (Fin d → Fin m) → ℕ) (k : ℕ) : Type :=
  {p : AntitoneProfile d m //
    ∀ f, (p.toFun f).val ≤ b f + k ∧ b f ≤ (p.toFun f).val + k}

instance (d m : ℕ) (b : (Fin d → Fin m) → ℕ) (k : ℕ) :
    Fintype (LimitTube d m b k) := by
  classical
  unfold LimitTube
  infer_instance

/-- Down-shift a tube profile and retain its thin residual. -/
def tubeToBelowTimesThin {d m k : ℕ} {b : (Fin d → Fin m) → ℕ} :
    LimitTube d m b k → BelowBarrier d m b × ThinProfile d m k :=
  fun p =>
    (⟨downShift k p.val, by
      intro f
      have hp := (p.property f).1
      change (p.val.toFun f).val - k ≤ b f
      omega⟩,
    lowerResidual k p.val)

theorem tubeToBelowTimesThin_injective {d m k : ℕ}
    {b : (Fin d → Fin m) → ℕ} :
    Function.Injective (tubeToBelowTimesThin (d := d) (m := m) (k := k) (b := b)) := by
  intro p q hpq
  apply Subtype.ext
  apply downShift_lowerResidual_injective k
  apply Prod.ext
  · exact congrArg (fun z => z.1.val) hpq
  · simpa only [tubeToBelowTimesThin] using congrArg (fun z => z.2) hpq

/-- Up-shift a tube profile by `k+1` and retain its thin upper residual. -/
def tubeToAboveTimesThin {d m k : ℕ} {b : (Fin d → Fin m) → ℕ}
    (hb : ∀ f, b f < m) :
    LimitTube d m b k → AboveBarrier d m b × ThinProfile d m (k + 1) :=
  fun p =>
    (⟨upShift (k + 1) p.val, by
      intro f
      have hp := (p.property f).2
      have hbf := hb f
      change b f < min ((p.val.toFun f).val + (k + 1)) m
      omega⟩,
    upperResidual (k + 1) p.val)

theorem tubeToAboveTimesThin_injective {d m k : ℕ}
    {b : (Fin d → Fin m) → ℕ} (hb : ∀ f, b f < m) :
    Function.Injective (tubeToAboveTimesThin (d := d) (m := m) (k := k) (b := b) hb) := by
  intro p q hpq
  apply Subtype.ext
  apply upShift_upperResidual_injective (k + 1)
  apply Prod.ext
  · exact congrArg (fun z => z.1.val) hpq
  · simpa only [tubeToAboveTimesThin] using congrArg (fun z => z.2) hpq

theorem tube_card_le_below_mul_thin {d m k : ℕ}
    (b : (Fin d → Fin m) → ℕ) :
    Fintype.card (LimitTube d m b k) ≤
      Fintype.card (BelowBarrier d m b) * Fintype.card (ThinProfile d m k) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_injective tubeToBelowTimesThin
    tubeToBelowTimesThin_injective

theorem tube_card_le_above_mul_thin {d m k : ℕ}
    (b : (Fin d → Fin m) → ℕ) (hb : ∀ f, b f < m) :
    Fintype.card (LimitTube d m b k) ≤
      Fintype.card (AboveBarrier d m b) * Fintype.card (ThinProfile d m (k + 1)) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_injective (tubeToAboveTimesThin hb)
    (tubeToAboveTimesThin_injective hb)

/-- **FINITE SHIFT-COMPRESSION INEQUALITY.**  A large limit-shape tube forces
a large full-support count, up to two thin-box plane-partition factors. -/
theorem tube_square_le_Q_mul_thin (m k : ℕ)
    (b : (Fin 2 → Fin m) → ℕ) (hb : ∀ f, b f < m) :
    Fintype.card (LimitTube 2 m b k) ^ 2 ≤
      Q m * (Fintype.card (ThinProfile 2 m k) *
        Fintype.card (ThinProfile 2 m (k + 1))) := by
  have hbelow := tube_card_le_below_mul_thin (d := 2) (m := m) (k := k) b
  have habove := tube_card_le_above_mul_thin (d := 2) (m := m) (k := k) b hb
  have hproduct := Nat.mul_le_mul hbelow habove
  have hbarrier := barrier_product_le_Q m b
  calc
    Fintype.card (LimitTube 2 m b k) ^ 2 =
        Fintype.card (LimitTube 2 m b k) * Fintype.card (LimitTube 2 m b k) :=
      pow_two _
    _ ≤ (Fintype.card (BelowBarrier 2 m b) * Fintype.card (ThinProfile 2 m k)) *
        (Fintype.card (AboveBarrier 2 m b) *
          Fintype.card (ThinProfile 2 m (k + 1))) := hproduct
    _ = (Fintype.card (BelowBarrier 2 m b) * Fintype.card (AboveBarrier 2 m b)) *
        (Fintype.card (ThinProfile 2 m k) *
          Fintype.card (ThinProfile 2 m (k + 1))) := by ac_rfl
    _ ≤ Q m * (Fintype.card (ThinProfile 2 m k) *
        Fintype.card (ThinProfile 2 m (k + 1))) :=
      Nat.mul_le_mul_right _ hbarrier

end
end CausalAlgebraicGeometry.C3ShiftCompression
