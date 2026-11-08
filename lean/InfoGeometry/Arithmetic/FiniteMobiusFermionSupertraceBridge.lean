import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
Finite arithmetic supertrace bridge.

The primary theorem is deliberately branch-free: it is the finite Boolean
occupation identity for an arbitrary commutative-ring weight.  Complex powers
and the finite cutoff sum `∑ n ≤ N, μ n n⁻ˢ` are separate readouts and are not
identified here.
-/

def finiteFermionSupertrace
    {ι R : Type*} [DecidableEq ι] [CommRing R]
    (modes : Finset ι) (q : ι → R) : R :=
  ∑ S ∈ modes.powerset, (-1 : R) ^ S.card * ∏ p ∈ S, q p

theorem finiteFermionSupertrace_eq_eulerProduct
    {ι R : Type*} [DecidableEq ι] [CommRing R]
    (modes : Finset ι) (q : ι → R) :
    finiteFermionSupertrace modes q = ∏ p ∈ modes, (1 - q p) := by
  simpa [finiteFermionSupertrace, PrimonFinite.STrF, PrimonFinite.parity,
    PrimonFinite.weight] using
    (PrimonFinite.STrF_eq_prod (modes := modes) (q := q))

def finiteArithmeticHamiltonian
    (energy : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, energy p

def finiteArithmeticParity (S : Finset ℕ) : ℤ :=
  (-1 : ℤ) ^ S.card

def primeSquarefreeProduct (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

def logarithmicHamiltonian (s : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, -s * Real.log (p : ℝ)

theorem finite_real_fermionic_supertrace
    (P : Finset ℕ) (s : ℝ) :
    (∏ p ∈ P, (1 - Real.exp (-s * Real.log (p : ℝ)))) =
      ∑ S ∈ P.powerset,
        (-1 : ℝ) ^ S.card * Real.exp (logarithmicHamiltonian s S) := by
  rw [← finiteFermionSupertrace_eq_eulerProduct P
    (fun p => Real.exp (-s * Real.log (p : ℝ)))]
  unfold finiteFermionSupertrace logarithmicHamiltonian
  refine Finset.sum_congr rfl ?_
  intro S hS
  rw [← Real.exp_sum]

def complexLogarithmicHamiltonian (s : ℂ) (S : Finset ℕ) : ℂ :=
  ∑ p ∈ S, -s * (Real.log (p : ℝ) : ℂ)

theorem finite_complex_fermionic_supertrace
    (P : Finset ℕ) (s : ℂ) :
    (∏ p ∈ P,
      (1 - Complex.exp (-s * (Real.log (p : ℝ) : ℂ)))) =
      ∑ S ∈ P.powerset,
        (-1 : ℂ) ^ S.card *
          Complex.exp (complexLogarithmicHamiltonian s S) := by
  rw [← finiteFermionSupertrace_eq_eulerProduct P
    (fun p => Complex.exp (-s * (Real.log (p : ℝ) : ℂ)))]
  unfold finiteFermionSupertrace complexLogarithmicHamiltonian
  refine Finset.sum_congr rfl ?_
  intro S hS
  rw [← Complex.exp_sum]

theorem mobius_subsetProduct_eq_finiteArithmeticParity
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    ArithmeticFunction.moebius (∏ p ∈ S, p) = finiteArithmeticParity S := by
  exact PrimeBitWittenIndex.mobius_prime_product_eq_parity S hprime

theorem finiteMobiusReadout_eq_supertrace_readout
    (P : PrimeRegister) (q : ℕ → ℝ) :
    (∑ S ∈ P.primes.powerset,
      ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℝ) *
        ∏ p ∈ S, q p) = finiteFermionSupertrace P.primes q := by
  classical
  unfold finiteFermionSupertrace
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
  have hμ :
      ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card :=
    PrimeBitWittenIndex.mobius_prime_product_eq_parity S
      (fun p hp => P.prime_mem p (hSub hp))
  rw [hμ]
  norm_num

theorem finiteMobiusReadout_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    (∑ S ∈ P.primes.powerset,
      ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℝ) *
        ∏ p ∈ S, q p) = ∏ p ∈ P.primes, (1 - q p) := by
  rw [finiteMobiusReadout_eq_supertrace_readout]
  exact finiteFermionSupertrace_eq_eulerProduct P.primes q

/-! Character weights are kept separate from the Möbius occupation sign. -/

def finiteCharacterSupertrace
    (P : PrimeRegister) (χ q : ℕ → ℂ) : ℂ :=
  ∑ S ∈ P.primes.powerset,
    (-1 : ℂ) ^ S.card * ∏ p ∈ S, (χ p * q p)

theorem finiteCharacterSupertrace_eq_eulerProduct
    (P : PrimeRegister) (χ q : ℕ → ℂ) :
    finiteCharacterSupertrace P χ q =
      ∏ p ∈ P.primes, (1 - χ p * q p) := by
  exact finiteFermionSupertrace_eq_eulerProduct P.primes
    (fun p => χ p * q p)

theorem finiteMobiusCharacterReadout_eq_supertrace
    (P : PrimeRegister) (χ q : ℕ → ℂ)
    (hχ_one : χ 1 = 1)
    (hχ_mul : ∀ a b : ℕ, χ (a * b) = χ a * χ b) :
    (∑ S ∈ P.primes.powerset,
      ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℂ) *
        χ (∏ p ∈ S, p) * ∏ p ∈ S, q p) =
      finiteCharacterSupertrace P χ q := by
  classical
  unfold finiteCharacterSupertrace
  have hχprod : ∀ S : Finset ℕ, χ (∏ p ∈ S, p) = ∏ p ∈ S, χ p := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hχ_one
    | @insert p S hp ih =>
        rw [Finset.prod_insert hp, hχ_mul, ih, Finset.prod_insert hp]
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
  have hμ :
      ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card :=
    PrimeBitWittenIndex.mobius_prime_product_eq_parity S
      (fun p hp => P.prime_mem p (hSub hp))
  rw [hμ, hχprod S]
  push_cast
  rw [Finset.prod_mul_distrib]
  ring

theorem finiteMobiusCharacterReadout_eq_eulerProduct
    (P : PrimeRegister) (χ q : ℕ → ℂ)
    (hχ_one : χ 1 = 1)
    (hχ_mul : ∀ a b : ℕ, χ (a * b) = χ a * χ b) :
    (∑ S ∈ P.primes.powerset,
      ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℂ) *
        χ (∏ p ∈ S, p) * ∏ p ∈ S, q p) =
      ∏ p ∈ P.primes, (1 - χ p * q p) := by
  rw [finiteMobiusCharacterReadout_eq_supertrace P χ q hχ_one hχ_mul]
  exact finiteCharacterSupertrace_eq_eulerProduct P χ q

end InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge
