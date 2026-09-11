import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.IndexTheorem
import InfoGeometry.Algebra.EulerLaurentDerivation

/-!
# Finite prime-bit parity as a genuine kernel index

The arithmetic owner supplies the finite signed subset sum.  This bridge
realizes its even and odd sectors as finite rational function spaces and
identifies that readout with the kernel index of the zero-differential
two-term complex.  It does not identify a divisor index with a Witten index
without this explicit finite complex.
-/

namespace InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge

open scoped BigOperators
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.IndexTheorem
open InfoGeometry.Algebra.EulerLaurentDerivation

/-- Even-cardinality occupied subsets of a finite prime register. -/
def evenPrimeSubsets (P : PrimeRegister) : Finset (Finset ℕ) :=
  P.primes.powerset.filter (fun S => Even S.card)

/-- Odd-cardinality occupied subsets of a finite prime register. -/
def oddPrimeSubsets (P : PrimeRegister) : Finset (Finset ℕ) :=
  P.primes.powerset.filter (fun S => Odd S.card)

abbrev evenPrimeCarrier (P : PrimeRegister) :=
  (↑(evenPrimeSubsets P) : Type) → ℚ

abbrev oddPrimeCarrier (P : PrimeRegister) :=
  (↑(oddPrimeSubsets P) : Type) → ℚ

/-- The signed subset sum is the difference of its even and odd cardinalities. -/
theorem finite_witten_index_eq_even_card_sub_odd_card (P : PrimeRegister) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) =
      (evenPrimeSubsets P).card - (oddPrimeSubsets P).card := by
  classical
  calc
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) =
        ∑ S ∈ P.primes.powerset,
          if Even S.card then (1 : ℤ) else -1 := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      rcases Nat.even_or_odd S.card with hEven | hOdd
      · rw [if_pos hEven, hEven.neg_one_pow]
      · rw [if_neg (Nat.not_even_iff_odd.mpr hOdd), hOdd.neg_one_pow]
    _ = (evenPrimeSubsets P).card - (oddPrimeSubsets P).card := by
      have hterm (S : Finset ℕ) :
          (if Even S.card then (1 : ℤ) else -1) =
            (if Even S.card then (1 : ℤ) else 0) -
              (if Odd S.card then (1 : ℤ) else 0) := by
        rcases Nat.even_or_odd S.card with hEven | hOdd
        · simp [hEven, Nat.not_odd_iff_even.mpr hEven]
        · simp [hOdd, Nat.not_even_iff_odd.mpr hOdd]
      calc
        (∑ S ∈ P.primes.powerset,
            if Even S.card then (1 : ℤ) else -1) =
            ∑ S ∈ P.primes.powerset,
              ((if Even S.card then (1 : ℤ) else 0) -
                (if Odd S.card then (1 : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hterm S
        _ = (evenPrimeSubsets P).card - (oddPrimeSubsets P).card := by
          rw [Finset.sum_sub_distrib]
          simp [evenPrimeSubsets, oddPrimeSubsets]

/-- The finite parity complex has one basis vector for each even/odd subset. -/
def primeRegisterParityComplex (P : PrimeRegister) :
    FiniteTwoTermComplex
      (K := ℚ)
      (Vp := evenPrimeCarrier P)
      (Vm := oddPrimeCarrier P) :=
  zeroFiniteTwoTermComplex

/-- Its genuine kernel index is the finite Witten parity sum. -/
theorem finite_kernel_index_prime_register_parity (P : PrimeRegister) :
    finiteKernelIndex (primeRegisterParityComplex P) =
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) := by
  change finiteKernelIndex (zeroFiniteTwoTermComplex
    (K := ℚ) (Vp := evenPrimeCarrier P) (Vm := oddPrimeCarrier P)) = _
  rw [finiteKernelIndex_zero]
  simp only [evenPrimeCarrier, oddPrimeCarrier,
    Module.finrank_fintype_fun_eq_card]
  simpa only [Fintype.card_coe] using
    (finite_witten_index_eq_even_card_sub_odd_card P).symm

/-! ## Concrete divisor-index bridge

The divisor index is kept as a finite signed sum.  Here the marked divisor
is the finite Boolean occupation packet itself, and its local charge is the
prime-bit parity.  This is an explicit correspondence theorem, not an
identification of arbitrary analytic divisors with a Witten index.
-/

/-- Signed local charge of a finite prime-bit occupation packet. -/
def primeRegisterParityCharge : Finset ℕ → ℤ :=
  fun S => (-1 : ℤ) ^ S.card

theorem prime_register_parity_divisorIndex_eq
    (P : PrimeRegister) :
    divisorIndex P.primes.powerset primeRegisterParityCharge =
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) := by
  rfl

theorem finite_kernel_index_prime_register_parity_eq_divisorIndex
    (P : PrimeRegister) :
    finiteKernelIndex (primeRegisterParityComplex P) =
      divisorIndex P.primes.powerset primeRegisterParityCharge := by
  rw [finite_kernel_index_prime_register_parity,
    prime_register_parity_divisorIndex_eq]

/-- For a nonempty register, the constructed finite complex has zero index. -/
theorem finite_kernel_index_prime_register_parity_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    finiteKernelIndex (primeRegisterParityComplex P) = 0 := by
  rw [finite_kernel_index_prime_register_parity]
  exact finite_witten_index_cancel P hP

end InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge
