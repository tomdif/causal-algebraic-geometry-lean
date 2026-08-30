/-
  C3OrderIdealReduction.lean — Exact finite reduction of the c₃ lower-bound count.

  A full-support pair φ < ψ with values in {0,...,m} is equivalent, after
  replacing ψ by ψ-1, to a weakly ordered pair φ ≤ θ of antitone profiles
  with values in Fin m.  Thus Q(m) is exactly the number of two-layer solid
  partitions of base [m]² and height at most m-1.  Equivalently (under the
  standard subgraph encoding), it is the number of ideals in the four-chain
  product [2] × [m] × [m] × [m-1].

  This file machine-checks the first equivalence and its cardinality identity.
  The final subgraph/order-ideal packaging is left as presentation work; it
  contains no asymptotic input.  Zero sorry.
-/
import CausalAlgebraicGeometry.C3Conjecture

namespace CausalAlgebraicGeometry.C3OrderIdealReduction

open CausalAlgebraicGeometry.FullSupportLowerBound
open CausalAlgebraicGeometry.C3Conjecture

noncomputable section
open scoped Classical

/-- A weakly ordered pair of antitone profiles with values in `Fin m`.
The intended names are `lower = φ` and `upper = ψ - 1`. -/
structure WeakOrderedPair (d m : ℕ) where
  lower : (Fin d → Fin m) → Fin m
  upper : (Fin d → Fin m) → Fin m
  lower_antitone : Antitone lower
  upper_antitone : Antitone upper
  lower_le_upper : lower ≤ upper

theorem WeakOrderedPair.ext {d m : ℕ} {p q : WeakOrderedPair d m}
    (hlower : p.lower = q.lower) (hupper : p.upper = q.upper) : p = q := by
  cases p
  cases q
  cases hlower
  cases hupper
  rfl

instance (d m : ℕ) : Fintype (WeakOrderedPair d m) := by
  classical
  let enc : WeakOrderedPair d m →
      (((Fin d → Fin m) → Fin m) × ((Fin d → Fin m) → Fin m)) :=
    fun p => (p.lower, p.upper)
  apply Fintype.ofInjective enc
  intro p q h
  exact WeakOrderedPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-! ## Removing and restoring the strict unit gap -/

/-- Replace a strict pair `φ < ψ ≤ m` by the weak pair `φ ≤ ψ-1 < m`. -/
def fullSupportToWeak {d m : ℕ} (p : FullSupportPair d m) :
    WeakOrderedPair d m where
  lower f := ⟨p.phi f, by
    exact lt_of_lt_of_le (p.phi_lt_psi f) (p.psi_le_m f)⟩
  upper f := ⟨p.psi f - 1, by
    have hpos : 0 < p.psi f := lt_of_le_of_lt (Nat.zero_le _) (p.phi_lt_psi f)
    have hle : p.psi f ≤ m := p.psi_le_m f
    omega⟩
  lower_antitone := by
    intro f g hfg
    exact Fin.mk_le_mk.mpr (p.phi_antitone hfg)
  upper_antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    have h := p.psi_antitone hfg
    omega
  lower_le_upper := by
    intro f
    apply Fin.mk_le_mk.mpr
    have h := p.phi_lt_psi f
    omega

/-- Restore the strict pair by replacing `θ` with `θ+1`. -/
def weakToFullSupport {d m : ℕ} (p : WeakOrderedPair d m) :
    FullSupportPair d m where
  phi f := (p.lower f).val
  psi f := (p.upper f).val + 1
  psi_le_m := by
    intro f
    have h := (p.upper f).isLt
    omega
  phi_antitone := by
    intro f g hfg
    exact Fin.le_def.mp (p.lower_antitone hfg)
  psi_antitone := by
    intro f g hfg
    have h := Fin.le_def.mp (p.upper_antitone hfg)
    exact Nat.add_le_add_right h 1
  phi_lt_psi := by
    intro f
    have h := Fin.le_def.mp (p.lower_le_upper f)
    omega

/-- The strict unit gap carries no information: subtraction and addition of
one give an exact equivalence of the two finite profile types. -/
def fullSupportPairEquivWeak (d m : ℕ) :
    FullSupportPair d m ≃ WeakOrderedPair d m where
  toFun := fullSupportToWeak
  invFun := weakToFullSupport
  left_inv p := by
    apply FullSupportPair.ext
    · funext f
      rfl
    · funext f
      change p.psi f - 1 + 1 = p.psi f
      have hpos : 0 < p.psi f := lt_of_le_of_lt (Nat.zero_le _) (p.phi_lt_psi f)
      omega
  right_inv p := by
    apply WeakOrderedPair.ext
    · funext f
      apply Fin.ext
      rfl
    · funext f
      apply Fin.ext
      simp only [fullSupportToWeak, weakToFullSupport, Fin.val_mk]
      omega

/-! ## The exact c₃ reduction -/

/-- **EXACT FINITE REDUCTION.**  `Q(m)` is the number of weakly ordered pairs
of antitone `[m]² → Fin m` profiles.  These are precisely the two layers of
the four-dimensional order-ideal model `[2] × [m] × [m] × [m-1]`. -/
theorem Q_eq_weakOrderedPair_card (m : ℕ) :
    Q m = Fintype.card (WeakOrderedPair 2 m) := by
  unfold Q
  exact Fintype.card_congr (fullSupportPairEquivWeak 2 m)

end
end CausalAlgebraicGeometry.C3OrderIdealReduction
