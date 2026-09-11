import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite prime-valuation lattice and mode-permutation roots

The squarefree `PrimeBitLattice` is only the `{0,1}` sector of the finite
valuation lattice.  This owner records the finite free abelian lattice
`Fin k → ℤ`, its logarithmic energy and Mellin character, and the canonical
mode-permutation (`A`-type) root directions.  No arithmetic symmetry of the
unequal prime energies is asserted: permutations act on the abstract modes.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeValuationLatticeWeyl

abbrev Valuation (k : ℕ) := Fin k → ℤ

def valuationMonomial {k : ℕ} (p : Fin k → Nat.Primes)
    (ν : Valuation k) : ℚ :=
  ∏ i : Fin k, (p i : ℚ) ^ ν i

def valuationLogEnergy {k : ℕ} (p : Fin k → Nat.Primes)
    (ν : Valuation k) : ℝ :=
  ∑ i : Fin k, (ν i : ℝ) * Real.log (p i : ℝ)

def valuationMellinCharacter {k : ℕ} (p : Fin k → Nat.Primes)
    (s : ℂ) (ν : Valuation k) : ℂ :=
  Complex.exp (-s * (valuationLogEnergy p ν : ℂ))

theorem valuationMonomial_add {k : ℕ} (p : Fin k → Nat.Primes)
    (ν μ : Valuation k) :
    valuationMonomial p (ν + μ) =
      valuationMonomial p ν * valuationMonomial p μ := by
  unfold valuationMonomial
  simp only [Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [zpow_add₀]
  exact_mod_cast (Nat.Prime.ne_zero (p i).property)

theorem valuationLogEnergy_add {k : ℕ} (p : Fin k → Nat.Primes)
    (ν μ : Valuation k) :
    valuationLogEnergy p (ν + μ) =
      valuationLogEnergy p ν + valuationLogEnergy p μ := by
  unfold valuationLogEnergy
  simp only [Pi.add_apply, Int.cast_add, add_mul]
  rw [Finset.sum_add_distrib]

theorem valuationMellinCharacter_zero {k : ℕ}
    (p : Fin k → Nat.Primes) (s : ℂ) :
    valuationMellinCharacter p s 0 = 1 := by
  simp [valuationMellinCharacter, valuationLogEnergy]

theorem valuationMellinCharacter_add {k : ℕ}
    (p : Fin k → Nat.Primes) (s : ℂ) (ν μ : Valuation k) :
    valuationMellinCharacter p s (ν + μ) =
      valuationMellinCharacter p s ν * valuationMellinCharacter p s μ := by
  unfold valuationMellinCharacter
  rw [valuationLogEnergy_add, Complex.ofReal_add, mul_add,
    Complex.exp_add]

def primeModeRoot {k : ℕ} (i j : Fin k) : Valuation k :=
  fun n => if n = i then 1 else if n = j then -1 else 0

def modePermute {k : ℕ} (π : Equiv.Perm (Fin k))
    (ν : Valuation k) : Valuation k :=
  ν ∘ π.symm

theorem modePermute_one {k : ℕ} (ν : Valuation k) :
    modePermute (1 : Equiv.Perm (Fin k)) ν = ν := by
  funext n
  rfl

theorem modePermute_mul {k : ℕ} (π σ : Equiv.Perm (Fin k))
    (ν : Valuation k) :
    modePermute (π * σ) ν = modePermute π (modePermute σ ν) := by
  funext n
  rfl

theorem modePermute_zero {k : ℕ} (π : Equiv.Perm (Fin k)) :
    modePermute π (0 : Valuation k) = 0 := by
  funext n
  rfl

theorem modePermute_add {k : ℕ} (π : Equiv.Perm (Fin k))
    (ν μ : Valuation k) :
    modePermute π (ν + μ) = modePermute π ν + modePermute π μ := by
  funext n
  rfl

theorem modePermute_primeModeRoot {k : ℕ} (π : Equiv.Perm (Fin k))
    (i j : Fin k) :
    modePermute π (primeModeRoot i j) =
      primeModeRoot (π i) (π j) := by
  funext n
  by_cases hni : n = π i
  · subst hni
    simp [modePermute, primeModeRoot]
  · by_cases hnj : n = π j
    · subst n
      have hji : j ≠ i := by
        intro h
        apply hni
        exact congrArg π h
      simp [modePermute, primeModeRoot, hni, hji]
    · have hpi : π.symm n ≠ i := by
        intro h
        apply hni
        simpa using congrArg π h
      have hpj : π.symm n ≠ j := by
        intro h
        apply hnj
        simpa using congrArg π h
      simp [modePermute, primeModeRoot, hpi, hpj, hni, hnj]

end InfoGeometry.Arithmetic.PrimeValuationLatticeWeyl
