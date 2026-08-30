/-
  C3BarrierLowerBound.lean — A deterministic-barrier route to c₃ = 2 L₃.

  Instead of estimating the rare-event probability that two independent
  plane partitions happen to be pointwise ordered, fix a barrier b and choose
  one antitone profile below b and one strictly above b.  Every such pair is a
  full-support pair, so

    (# profiles below b) * (# profiles above b) ≤ Q(m).

  The finite inequality is proved here in every base dimension.  Analytically,
  it suggests choosing b near the plane-partition limit shape and proving that
  both constrained profile families retain the full one-surface entropy L₃.
  That would imply log Q(m) ≥ 2 L₃ m² - o(m²) without any global hard-wall
  probability estimate.  Zero sorry.
-/
import CausalAlgebraicGeometry.C3OrderIdealReduction

namespace CausalAlgebraicGeometry.C3BarrierLowerBound

open CausalAlgebraicGeometry.FullSupportLowerBound
open CausalAlgebraicGeometry.C3Conjecture

noncomputable section
open scoped Classical

/-- An antitone height profile on `[m]^d`, with heights in `{0,...,m}`. -/
structure AntitoneProfile (d m : ℕ) where
  toFun : (Fin d → Fin m) → Fin (m + 1)
  antitone : Antitone toFun

theorem AntitoneProfile.ext {d m : ℕ} {p q : AntitoneProfile d m}
    (h : p.toFun = q.toFun) : p = q := by
  cases p
  cases q
  cases h
  rfl

instance (d m : ℕ) : Fintype (AntitoneProfile d m) := by
  classical
  apply Fintype.ofInjective (fun p : AntitoneProfile d m => p.toFun)
  intro p q h
  exact AntitoneProfile.ext h

/-- Antitone profiles lying weakly below a prescribed integer barrier. -/
def BelowBarrier (d m : ℕ) (b : (Fin d → Fin m) → ℕ) : Type :=
  { p : AntitoneProfile d m // ∀ f, (p.toFun f).val ≤ b f }

/-- Antitone profiles lying strictly above a prescribed integer barrier. -/
def AboveBarrier (d m : ℕ) (b : (Fin d → Fin m) → ℕ) : Type :=
  { p : AntitoneProfile d m // ∀ f, b f < (p.toFun f).val }

instance (d m : ℕ) (b : (Fin d → Fin m) → ℕ) :
    Fintype (BelowBarrier d m b) := by
  classical
  unfold BelowBarrier
  infer_instance

instance (d m : ℕ) (b : (Fin d → Fin m) → ℕ) :
    Fintype (AboveBarrier d m b) := by
  classical
  unfold AboveBarrier
  infer_instance

/-- Rotate every base coordinate through the center of the box. -/
def rotatePoint {d m : ℕ} (f : Fin d → Fin m) : Fin d → Fin m :=
  fun i => Fin.rev (f i)

@[simp]
theorem rotatePoint_involutive {d m : ℕ} (f : Fin d → Fin m) :
    rotatePoint (rotatePoint f) = f := by
  funext i
  exact Fin.rev_rev (f i)

/-- Box complementation followed by central rotation.  This is the standard
order-preserving involution on boxed plane partitions. -/
def dualProfile {d m : ℕ} (p : AntitoneProfile d m) : AntitoneProfile d m where
  toFun f := ⟨m - (p.toFun (rotatePoint f)).val, by omega⟩
  antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    have hrot : rotatePoint g ≤ rotatePoint f := by
      intro i
      simpa only [rotatePoint] using (Fin.rev_le_rev.mpr (hfg i))
    have hp := Fin.le_def.mp (p.antitone hrot)
    omega

@[simp]
theorem dualProfile_involutive {d m : ℕ} (p : AntitoneProfile d m) :
    dualProfile (dualProfile p) = p := by
  apply AntitoneProfile.ext
  funext f
  apply Fin.ext
  simp only [dualProfile, rotatePoint_involutive]
  have hp := (p.toFun f).isLt
  omega

/-- A threshold is self-dual when rotation exchanges the weak-below and
strict-above inequalities. -/
def SelfDualBarrier {d m : ℕ} (b : (Fin d → Fin m) → ℕ) : Prop :=
  ∀ f, b f + b (rotatePoint f) = m - 1

/-- For a nonempty box and a self-dual barrier, complement-rotation is an
explicit bijection from profiles strictly above the barrier to profiles
weakly below it. -/
def aboveEquivBelowOfSelfDual {d m : ℕ} (hm : 0 < m)
    {b : (Fin d → Fin m) → ℕ} (hb : SelfDualBarrier b) :
    AboveBarrier d m b ≃ BelowBarrier d m b where
  toFun p := ⟨dualProfile p.val, by
    intro f
    have hp := p.property (rotatePoint f)
    have hself := hb f
    change m - (p.val.toFun (rotatePoint f)).val ≤ b f
    omega⟩
  invFun p := ⟨dualProfile p.val, by
    intro f
    have hp := p.property (rotatePoint f)
    have hself := hb f
    change b f < m - (p.val.toFun (rotatePoint f)).val
    omega⟩
  left_inv p := by
    apply Subtype.ext
    exact dualProfile_involutive p.val
  right_inv p := by
    apply Subtype.ext
    exact dualProfile_involutive p.val

theorem card_above_eq_card_below_of_selfDual {d m : ℕ} (hm : 0 < m)
    {b : (Fin d → Fin m) → ℕ} (hb : SelfDualBarrier b) :
    Fintype.card (AboveBarrier d m b) = Fintype.card (BelowBarrier d m b) := by
  exact Fintype.card_congr (aboveEquivBelowOfSelfDual hm hb)

/-- A below/above barrier pair is automatically a full-support pair. -/
def separatedPairOfBarrier {d m : ℕ} {b : (Fin d → Fin m) → ℕ}
    (p : BelowBarrier d m b × AboveBarrier d m b) : FullSupportPair d m where
  phi f := (p.1.val.toFun f).val
  psi f := (p.2.val.toFun f).val
  psi_le_m := by
    intro f
    exact Nat.le_of_lt_succ (p.2.val.toFun f).isLt
  phi_antitone := by
    intro f g hfg
    exact Fin.le_def.mp (p.1.val.antitone hfg)
  psi_antitone := by
    intro f g hfg
    exact Fin.le_def.mp (p.2.val.antitone hfg)
  phi_lt_psi := by
    intro f
    exact lt_of_le_of_lt (p.1.property f) (p.2.property f)

theorem separatedPairOfBarrier_injective {d m : ℕ}
    {b : (Fin d → Fin m) → ℕ} :
    Function.Injective (separatedPairOfBarrier (d := d) (m := m) (b := b)) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    apply AntitoneProfile.ext
    funext f
    apply Fin.ext
    exact congrArg (fun r : FullSupportPair d m => r.phi f) h
  · apply Subtype.ext
    apply AntitoneProfile.ext
    funext f
    apply Fin.ext
    exact congrArg (fun r : FullSupportPair d m => r.psi f) h

/-- **BARRIER PRODUCT INEQUALITY.**  Any barrier splits off a Cartesian
product of profiles inside the full-support pair count. -/
theorem barrier_product_le_fullSupport (d m : ℕ)
    (b : (Fin d → Fin m) → ℕ) :
    Fintype.card (BelowBarrier d m b) * Fintype.card (AboveBarrier d m b) ≤
      Fintype.card (FullSupportPair d m) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_injective separatedPairOfBarrier
    separatedPairOfBarrier_injective

/-- The c₃ specialization: every barrier on `[m]²` gives a certified product
lower bound for `Q(m)`. -/
theorem barrier_product_le_Q (m : ℕ) (b : (Fin 2 → Fin m) → ℕ) :
    Fintype.card (BelowBarrier 2 m b) * Fintype.card (AboveBarrier 2 m b) ≤ Q m := by
  exact barrier_product_le_fullSupport 2 m b

/-- A self-dual c₃ barrier turns the product bound into a square bound. -/
theorem selfDual_barrier_square_le_Q (m : ℕ) (hm : 0 < m)
    (b : (Fin 2 → Fin m) → ℕ) (hb : SelfDualBarrier b) :
    Fintype.card (BelowBarrier 2 m b) ^ 2 ≤ Q m := by
  have hcard := card_above_eq_card_below_of_selfDual hm hb
  calc
    Fintype.card (BelowBarrier 2 m b) ^ 2 =
        Fintype.card (BelowBarrier 2 m b) * Fintype.card (BelowBarrier 2 m b) :=
      pow_two _
    _ = Fintype.card (BelowBarrier 2 m b) * Fintype.card (AboveBarrier 2 m b) := by
      rw [hcard]
    _ ≤ Q m := barrier_product_le_Q m b

/-- The affine central-plane threshold for odd side length `2n+1`.  It is
the exact finite-volume mean barrier in the experiments through side 7. -/
def centralBarrierOdd (n : ℕ) (f : Fin 2 → Fin (2 * n + 1)) : ℕ :=
  min (2 * n) (3 * n - (f 0).val - (f 1).val)

theorem centralBarrierOdd_selfDual (n : ℕ) :
    SelfDualBarrier (centralBarrierOdd n) := by
  intro f
  have h0 := (f 0).isLt
  have h1 := (f 1).isLt
  simp only [centralBarrierOdd, rotatePoint, Fin.val_rev]
  simp only [Nat.min_def]
  split <;> split <;> omega

/-- Concrete certified lower bound for the odd central-plane family.  The
remaining breakthrough target is a subquadratic entropy deficit for the
single cardinality on the left. -/
theorem centralBarrierOdd_square_le_Q (n : ℕ) :
    Fintype.card (BelowBarrier 2 (2 * n + 1) (centralBarrierOdd n)) ^ 2 ≤
      Q (2 * n + 1) := by
  exact selfDual_barrier_square_le_Q (2 * n + 1) (by omega)
    (centralBarrierOdd n) (centralBarrierOdd_selfDual n)

end
end CausalAlgebraicGeometry.C3BarrierLowerBound
