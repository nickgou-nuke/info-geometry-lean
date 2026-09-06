import InfoGeometry.Arithmetic.PrimeEnergyNative
import InfoGeometry.Arithmetic.PrimonFockTraceFinite
import InfoGeometry.Arithmetic.PrimonFockLinearTrace

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonFockPrimeEnergy

open InfoGeometry.Arithmetic.PrimeEnergyNative
open InfoGeometry.Arithmetic.PrimonFockTraceFinite
open InfoGeometry.Arithmetic.PrimonFockLinearTrace

def primeEnergyProfile (n : ℕ) (p : Fin n → Nat.Primes) : Fin n → ℝ :=
  fun i => Real.log (p i : ℝ)

theorem primeEnergyProfile_nonneg
    (n : ℕ) (p : Fin n → Nat.Primes) (i : Fin n) :
    0 ≤ primeEnergyProfile n p i := by
  exact prime_log_nonneg (p i)

theorem fockEnergy_prime_nonneg
    (n : ℕ) (p : Fin n → Nat.Primes) (occ : FockState n) :
    0 ≤ fockEnergy n (primeEnergyProfile n p) occ := by
  apply fockEnergy_nonneg
  intro i
  exact primeEnergyProfile_nonneg n p i

theorem primeFockTrace_pos
    (n : ℕ) (p : Fin n → Nat.Primes) (β : ℝ) :
    0 < fockTraceExp n (primeEnergyProfile n p) β :=
  fockTraceExp_pos n (primeEnergyProfile n p) β

theorem primeFockTrace_ne_zero
    (n : ℕ) (p : Fin n → Nat.Primes) (β : ℝ) :
    fockTraceExp n (primeEnergyProfile n p) β ≠ 0 :=
  (primeFockTrace_pos n p β).ne'

theorem prime_hamiltonian_trace
    (n : ℕ) (p : Fin n → Nat.Primes) :
    LinearMap.trace ℂ (FockVec n)
        (fockHamiltonianLinear n (primeEnergyProfile n p)) =
      ∑ occ : FockState n,
        (fockEnergy n (primeEnergyProfile n p) occ : ℂ) := by
  exact trace_fockHamiltonianLinear n (primeEnergyProfile n p)

theorem prime_gibbs_trace_local_product
    (n : ℕ) (p : Fin n → Nat.Primes) (β : ℝ) :
    LinearMap.trace ℂ (FockVec n)
        (fockGibbsLinear n (primeEnergyProfile n p) β) =
      ∏ i : Fin n,
        (1 + (localBoltzmann (primeEnergyProfile n p i) β : ℂ)) := by
  exact trace_fockGibbsLinear_eq_local_product n
    (primeEnergyProfile n p) β

end InfoGeometry.Arithmetic.PrimonFockPrimeEnergy
