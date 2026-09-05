/-
  CSpecChamberRootsCounterexample.lean — Why the unstratified root sheaf
  need not be a local system.

  On the two-element chain, the empty causal prime specializes to the prime
  `{1}`.  Every open neighbourhood of `{1}` therefore also contains the
  empty prime, while their complement sizes are one and two.  The associated
  chamber-root fibres consequently have cardinalities one and two.
-/
import CausalAlgebraicGeometry.CSpecChamberRoots
import CausalAlgebraicGeometry.ChamberGaloisD4

namespace CausalAlgebraicGeometry.CSpecChamberRootsCounterexample

open TopologicalSpace
open CausalAlgebra CausalPrimality CSpecActualSheaf
open CausalAlgebraicGeometry.ChamberGaloisBridge
open CausalAlgebraicGeometry.CSpecChamberRoots
open CausalAlgebraicGeometry.ChamberGaloisD4

/-- The two-element chain used by the counterexample. -/
abbrev chainTwo : CAlg ℚ :=
  fromFinitePoset (Fin 2) (fun i j => i.val ≤ j.val)
    (fun i => Nat.le_refl i.val)
    (fun _ _ hij hji => Fin.ext (Nat.le_antisymm hij hji))
    (fun _ _ _ hij hjk => Nat.le_trans hij hjk)

/-- The empty upset is the generic point of this two-point CSpec. -/
def emptyPrime : CSpec chainTwo :=
  ⟨∅, {
    proper := by
      change (∅ : Set (Fin 2)) ≠ Set.univ
      intro h
      have hzero : (0 : Fin 2) ∈ (∅ : Set (Fin 2)) :=
        h.symm ▸ Set.mem_univ _
      exact hzero
    upset := by simp [IsUpset]
    complement_convex := by simpa [chainTwo] using causallyConvex_univ chainTwo }⟩

/-- The upset `{1}` is the other causal prime. -/
def upperPrime : CSpec chainTwo :=
  ⟨{(1 : Fin 2)}, {
    proper := by
      change ({(1 : Fin 2)} : Set (Fin 2)) ≠ Set.univ
      intro h
      have hzero : (0 : Fin 2) ∈ ({(1 : Fin 2)} : Set (Fin 2)) :=
        h.symm ▸ Set.mem_univ _
      simp at hzero
    upset := by
      change ∀ a b : Fin 2, a ∈ ({1} : Set (Fin 2)) →
        a.val ≤ b.val → b ∈ ({1} : Set (Fin 2))
      intro a b ha hab
      simp only [Set.mem_singleton_iff] at ha ⊢
      subst a
      apply Fin.ext
      omega
    complement_convex := by
      intro a b γ ha hb haγ hγb
      change a ∉ ({1} : Set (Fin 2)) at ha
      change b ∉ ({1} : Set (Fin 2)) at hb
      change a.val ≤ γ.val at haγ
      change γ.val ≤ b.val at hγb
      change γ ∉ ({1} : Set (Fin 2))
      fin_cases a <;> fin_cases b <;> fin_cases γ <;> simp_all }⟩

/-- Every open containing `{1}` also contains the empty causal prime. -/
theorem emptyPrime_mem_of_upperPrime_mem
    (U : Opens (CSpecTop chainTwo)) (hupper : upperPrime ∈ U) :
    emptyPrime ∈ U := by
  have hopen := U.is_open'
  change TopologicalSpace.GenerateOpen
    (Set.range (basicOpenSet chainTwo)) U.1 at hopen
  have claim : ∀ V : Set (CSpec chainTwo),
      TopologicalSpace.GenerateOpen
        (Set.range (basicOpenSet chainTwo)) V →
      upperPrime ∈ V → emptyPrime ∈ V := by
    intro V hV
    induction hV with
    | basic s hs =>
        rcases hs with ⟨a, rfl⟩
        simp [basicOpenSet, emptyPrime]
    | univ => simp
    | inter s t hs ht ihs iht =>
        intro hmem
        exact ⟨ihs hmem.1, iht hmem.2⟩
    | sUnion S hS ih =>
        intro hmem
        rcases hmem with ⟨s, hs, hus⟩
        exact ⟨s, hs, ih s hs hus⟩
  exact claim U.1 hopen hupper

theorem emptyPrime_complement_card :
    (primeComplementFinset chainTwo emptyPrime).card = 2 := by
  classical
  have hfin : primeComplementFinset chainTwo emptyPrime = Finset.univ := by
    ext a
    rw [mem_primeComplementFinset_iff]
    simp [emptyPrime]
  rw [hfin]
  change Fintype.card chainTwo.Λ = 2
  rfl

theorem upperPrime_complement_card :
    (primeComplementFinset chainTwo upperPrime).card = 1 := by
  classical
  have hfin : primeComplementFinset chainTwo upperPrime = {(0 : Fin 2)} := by
    ext a
    rw [mem_primeComplementFinset_iff]
    simp only [upperPrime, Set.mem_singleton_iff, Finset.mem_singleton]
    fin_cases a
    · constructor
      · intro _
        rfl
      · intro _ h
        have hv := congrArg Fin.val h
        norm_num at hv
    · constructor
      · intro h
        exact (h rfl).elim
      · intro h
        have hv := congrArg Fin.val h
        norm_num at hv
  rw [hfin]
  simp

theorem qResidualChamberPolynomial_three_irreducible :
    Irreducible (qResidualChamberPolynomial 3) := by
  have hnat := qResidualChamberPolynomial_natDegree 3
  norm_num at hnat
  have hne : qResidualChamberPolynomial 3 ≠ 0 := by
    intro hzero
    rw [hzero] at hnat
    simp at hnat
  apply Polynomial.irreducible_of_degree_eq_one
  rw [Polynomial.degree_eq_natDegree hne, hnat]
  norm_num

theorem upperPrime_root_card :
    Fintype.card (localChamberRootFiber chainTwo upperPrime) = 1 := by
  have hsep : (qResidualChamberPolynomial 3).Separable :=
    PerfectField.separable_of_irreducible
      qResidualChamberPolynomial_three_irreducible
  have hdim : localChamberDimension chainTwo upperPrime = 3 := by
    rw [localChamberDimension, upperPrime_complement_card]
  change Fintype.card (ChamberRoot (localChamberDimension chainTwo upperPrime)) = 1
  rw [hdim]
  simpa using chamberRoot_card 3 hsep

theorem emptyPrime_root_card :
    Fintype.card (localChamberRootFiber chainTwo emptyPrime) = 2 := by
  have hsep : (qResidualChamberPolynomial 4).Separable :=
    PerfectField.separable_of_irreducible
      qResidualChamberPolynomial_four_irreducible
  have hdim : localChamberDimension chainTwo emptyPrime = 4 := by
    rw [localChamberDimension, emptyPrime_complement_card]
  change Fintype.card (ChamberRoot (localChamberDimension chainTwo emptyPrime)) = 2
  rw [hdim]
  simpa using chamberRoot_card 4 hsep

/-- The original, unstratified local-system target is false in general. -/
theorem not_chamberRootLocalSystemStatement_chainTwo :
    ¬ ChamberRootLocalSystemStatement chainTwo := by
  intro hlocal
  obtain ⟨U, hupper, hfibre⟩ := hlocal upperPrime
  have hempty : emptyPrime ∈ U := emptyPrime_mem_of_upperPrime_mem U hupper
  obtain ⟨e⟩ := hfibre ⟨emptyPrime, hempty⟩
  have hcard := Fintype.card_congr e
  rw [upperPrime_root_card, emptyPrime_root_card] at hcard
  omega

end CausalAlgebraicGeometry.CSpecChamberRootsCounterexample
