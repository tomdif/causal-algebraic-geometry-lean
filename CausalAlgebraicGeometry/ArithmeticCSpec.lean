/-
  ArithmeticCSpec.lean — CSpec of the divisibility lattice: the converse FAILS

  ArithmeticBridge.lean proves: every prime p | n gives a CSpec point of divCAlg n.
  This file proves: the converse is FALSE. CSpec(divCAlg n) has points that do NOT
  arise from any prime divisor.

  Concrete counterexample: for n = 12, the set {4, 6, 12} (all divisors of 12
  divisible by 4 or by 6) is a valid CSpec point — it is a proper upset whose
  complement {1, 2, 3} is causally convex — but it does NOT equal primeUpset(p)
  for any prime p | 12.

  This means: CSpec(div(n)) is STRICTLY LARGER than the set of prime divisors.
  The paper's analogy CSpec ~ Spec(Z/nZ) is correct as a "~" but cannot be
  upgraded to a bijection.

  All theorems are sorry-free.
-/
import CausalAlgebraicGeometry.ArithmeticBridge

namespace CausalAlgebraicGeometry.ArithmeticCSpec

open CausalAlgebra CausalPrimality ArithmeticBridge

/-! ## The non-prime CSpec point {4, 6, 12} in div(12) -/

/-- Helper: 12 > 0. -/
private theorem twelve_pos : (0 : ℕ) < 12 := by omega

/-- The divisibility causal algebra on divisors of 12. -/
private abbrev D12 := divCAlg 12 twelve_pos

/-- The type of divisors of 12. -/
private abbrev Div12 := { d : ℕ // d ∈ (12 : ℕ).divisors }

/-- The set of divisors of 12 that are divisible by 4 or by 6.
    Concretely: {4, 6, 12}. -/
def nonPrimeUpset : Set Div12 :=
  { d | 4 ∣ (d : ℕ) ∨ 6 ∣ (d : ℕ) }

/-- nonPrimeUpset is an upset: if (4 | a or 6 | a) and a | b, then (4 | b or 6 | b).
    FALSE in general! If 4 | a and a | b, then 4 | b. Similarly for 6. -/
theorem nonPrimeUpset_isUpset : IsUpset D12 nonPrimeUpset := by
  intro a b ha hab
  -- ha : 4 | a ∨ 6 | a, hab : a | b (in the divisibility order)
  cases ha with
  | inl h4 => exact Or.inl (dvd_trans h4 hab)
  | inr h6 => exact Or.inr (dvd_trans h6 hab)

/-- nonPrimeUpset is proper: 1 is a divisor of 12 and 1 ∉ nonPrimeUpset. -/
theorem nonPrimeUpset_proper : nonPrimeUpset ≠ Set.univ := by
  intro h
  have h1 : (1 : ℕ) ∈ (12 : ℕ).divisors := Nat.mem_divisors.mpr ⟨one_dvd 12, by omega⟩
  have hmem : (⟨1, h1⟩ : Div12) ∈ nonPrimeUpset := h ▸ Set.mem_univ _
  simp only [nonPrimeUpset, Set.mem_setOf_eq] at hmem
  -- hmem : 4 | 1 ∨ 6 | 1
  rcases hmem with h4 | h6
  · exact absurd (Nat.le_of_dvd Nat.one_pos h4) (by omega)
  · exact absurd (Nat.le_of_dvd Nat.one_pos h6) (by omega)

/-- The complement of nonPrimeUpset is causally convex.
    Complement = {d : d is a divisor of 12 with 4 ∤ d and 6 ∤ d} = {1, 2, 3}.
    For convexity: if a, b ∈ complement and a | c | b, then c ∈ complement.
    Since a | c | b and b ∈ {1,2,3}, we have c | b, so c ∈ {divisors of b}.
    For b ∈ {1,2,3}: divisors of b among divisors of 12 are subsets of {1,2,3},
    so c ∈ {1,2,3} ⊆ complement. -/
theorem nonPrimeUpset_complement_convex :
    IsCausallyConvex D12 nonPrimeUpsetᶜ := by
  intro a b c ha hb hac hcb
  -- ha : a ∉ nonPrimeUpset, hb : b ∉ nonPrimeUpset
  -- hac : a | c, hcb : c | b (divisibility order)
  -- Need: c ∉ nonPrimeUpset, i.e., 4 ∤ c ∧ 6 ∤ c
  simp only [Set.mem_compl_iff, nonPrimeUpset] at ha hb ⊢
  intro hc
  apply hb
  cases hc with
  | inl h4c => exact Or.inl (dvd_trans h4c hcb)
  | inr h6c => exact Or.inr (dvd_trans h6c hcb)

/-- **{4, 6, 12} is a CSpec point of div(12).** -/
theorem nonPrimeUpset_isCausallyPrime :
    IsCausallyPrime D12 nonPrimeUpset where
  proper := nonPrimeUpset_proper
  upset := nonPrimeUpset_isUpset
  complement_convex := nonPrimeUpset_complement_convex

/-! ## The non-prime CSpec point differs from all prime upsets -/

/-- nonPrimeUpset ≠ primeUpset 12 2.
    primeUpset(2) = {d : 2 | d} = {2, 4, 6, 12} (as divisors of 12).
    nonPrimeUpset = {d : 4 | d ∨ 6 | d} = {4, 6, 12}.
    They differ: 2 ∈ primeUpset(2) but 2 ∉ nonPrimeUpset. -/
theorem nonPrime_ne_primeUpset2 : nonPrimeUpset ≠ primeUpset 12 2 := by
  intro h
  have h2 : (2 : ℕ) ∈ (12 : ℕ).divisors := Nat.mem_divisors.mpr ⟨by omega, by omega⟩
  have hmem : (⟨2, h2⟩ : Div12) ∈ primeUpset 12 2 := by
    simp only [primeUpset, Set.mem_setOf_eq]; norm_num
  rw [← h] at hmem
  simp only [nonPrimeUpset, Set.mem_setOf_eq] at hmem
  rcases hmem with h4 | h6
  · exact absurd (Nat.le_of_dvd (by omega) h4) (by omega)
  · exact absurd (Nat.le_of_dvd (by omega) h6) (by omega)

/-- nonPrimeUpset ≠ primeUpset 12 3.
    primeUpset(3) = {d : 3 | d} = {3, 6, 12}.
    nonPrimeUpset = {4, 6, 12}.
    They differ: 3 ∈ primeUpset(3) but 3 ∉ nonPrimeUpset,
    and 4 ∈ nonPrimeUpset but 4 ∉ primeUpset(3). -/
theorem nonPrime_ne_primeUpset3 : nonPrimeUpset ≠ primeUpset 12 3 := by
  intro h
  have h3 : (3 : ℕ) ∈ (12 : ℕ).divisors := Nat.mem_divisors.mpr ⟨by omega, by omega⟩
  have hmem : (⟨3, h3⟩ : Div12) ∈ primeUpset 12 3 := by
    simp only [primeUpset, Set.mem_setOf_eq]; norm_num
  rw [← h] at hmem
  simp only [nonPrimeUpset, Set.mem_setOf_eq] at hmem
  rcases hmem with h4 | h6
  · exact absurd (Nat.le_of_dvd (by omega) h4) (by omega)
  · exact absurd (Nat.le_of_dvd (by omega) h6) (by omega)

/-! ## Main theorem: the converse of prime_gives_CSpec_point is FALSE -/

/-- **The converse of `prime_gives_CSpec_point` fails.**

    There exists a CSpec point of divCAlg 12 that is not equal to
    primeUpset(p) for any prime p dividing 12.

    Specifically, {4, 6, 12} (divisors divisible by 4 or 6) is a CSpec
    point that differs from primeUpset(2) = {2,4,6,12} and from
    primeUpset(3) = {3,6,12}.

    This means CSpec(div(n)) is strictly larger than {primeUpset(p) : p | n, p prime}.
    The analogy CSpec ~ Spec(Z/nZ) is genuine but not a bijection. -/
theorem converse_fails :
    ∃ S : Set Div12, IsCausallyPrime D12 S ∧
      (∀ p : ℕ, p.Prime → p ∣ 12 → S ≠ primeUpset 12 p) := by
  refine ⟨nonPrimeUpset, nonPrimeUpset_isCausallyPrime, fun p hp hpn hS => ?_⟩
  -- The only primes dividing 12 are 2 and 3
  have hle : p ≤ 12 := Nat.le_of_dvd (by omega) hpn
  have hge := hp.two_le
  -- Enumerate all values 2 ≤ p ≤ 12
  have hp2or3 : p = 2 ∨ p = 3 := by
    have hle : p ≤ 12 := Nat.le_of_dvd (by omega) hpn
    have hge := hp.two_le
    -- Enumerate all integers in [2, 12] and check prime + divides 12
    have : ∀ k : ℕ, 2 ≤ k → k ≤ 12 → k.Prime → k ∣ 12 → k = 2 ∨ k = 3 := by decide
    exact this p hge hle hp hpn
  cases hp2or3 with
  | inl h2 => subst h2; exact absurd hS nonPrime_ne_primeUpset2
  | inr h3 => subst h3; exact absurd hS nonPrime_ne_primeUpset3

/-! ## Interpretation

  The CSpec of a divisibility lattice has three kinds of points:

  1. **Prime upsets** {d : p | d} for each prime p | n — these correspond
     to the closed points of Spec(Z/nZ), established by `prime_gives_CSpec_point`.

  2. **Composite upsets** like {d : 4 | d ∨ 6 | d} — these are "thickened"
     points with no prime analog. They arise because the causal convexity
     condition on the complement is weaker than the prime ideal condition.

  3. **The empty set** — always a CSpec point (vacuously), analogous to
     the generic point (0) in Spec.

  The paper's comparison table correctly uses "~" (analogy) rather than
  "=" (bijection) for the CSpec-Spec correspondence.
-/

end CausalAlgebraicGeometry.ArithmeticCSpec
