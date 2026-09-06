import InfoGeometry.Arithmetic.FiniteFockNative
import InfoGeometry.Arithmetic.FiniteFockParity
import InfoGeometry.Arithmetic.PrimeCutoffFiniteEuler
import InfoGeometry.Arithmetic.PrimeCutoffNative
import InfoGeometry.Arithmetic.PrimeEnergyNative

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCutoffFiniteFock

open InfoGeometry.Arithmetic.FiniteFockNative
open InfoGeometry.Arithmetic.FiniteFockParity
open InfoGeometry.Arithmetic.PrimeCutoffNative
open InfoGeometry.Arithmetic.PrimeEnergyNative

def primeEnergyProfile (M : ℕ) : PrimeCutoff M → ℝ :=
  fun p => Real.log (p : ℝ)

theorem primeEnergyProfile_nonneg (M : ℕ) (p : PrimeCutoff M) :
    0 ≤ primeEnergyProfile M p := by
  exact prime_log_nonneg p.1

theorem primeCutoff_gibbs_trace
    (M : ℕ) (β : ℝ) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (gibbsLinear (primeEnergyProfile M) β) =
      ∏ p : PrimeCutoff M,
        (1 + (localBoltzmann (primeEnergyProfile M p) β : ℂ)) := by
  exact trace_gibbsLinear_eq_product (primeEnergyProfile M) β

theorem primeCutoff_hamiltonian_trace
    (M : ℕ) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (hamiltonianLinear (primeEnergyProfile M)) =
      ∑ occ : State (PrimeCutoff M),
        (energy (primeEnergyProfile M) occ : ℂ) := by
  exact trace_hamiltonianLinear (primeEnergyProfile M)

theorem primeCutoff_hamiltonian_commute_totalNumber
    (M : ℕ) :
    (hamiltonianLinear (primeEnergyProfile M)).comp totalNumberLinear =
      totalNumberLinear.comp (hamiltonianLinear (primeEnergyProfile M)) := by
  exact hamiltonianLinear_commute_totalNumber (primeEnergyProfile M)

theorem primeCutoff_grandHamiltonian_commute_totalNumber
    (M : ℕ) (μ : ℝ) :
    (grandHamiltonianLinear (primeEnergyProfile M) μ).comp totalNumberLinear =
      totalNumberLinear.comp (grandHamiltonianLinear (primeEnergyProfile M) μ) := by
  exact grandHamiltonianLinear_commute_totalNumber (primeEnergyProfile M) μ

theorem primeCutoff_gibbs_trace_ne_zero
    (M : ℕ) (β : ℝ) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (gibbsLinear (primeEnergyProfile M) β) ≠ 0 := by
  exact trace_gibbsLinear_ne_zero (primeEnergyProfile M) β

theorem primeCutoff_grand_gibbs_trace
    (M : ℕ) (β μ : ℝ) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (grandGibbsLinear (primeEnergyProfile M) β μ) =
      ∏ p : PrimeCutoff M,
        (1 + (localBoltzmann (primeEnergyProfile M p - μ) β : ℂ)) := by
  exact trace_grandGibbsLinear_eq_product (primeEnergyProfile M) β μ

theorem primeCutoff_grand_gibbs_trace_ne_zero
    (M : ℕ) (β μ : ℝ) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (grandGibbsLinear (primeEnergyProfile M) β μ) ≠ 0 := by
  exact trace_grandGibbsLinear_ne_zero (primeEnergyProfile M) β μ

theorem primeCutoff_grand_gibbs_commute_totalNumber
    (M : ℕ) (β : ℝ) (μ : ℝ) :
    (grandGibbsLinear (primeEnergyProfile M) β μ).comp totalNumberLinear =
      totalNumberLinear.comp (grandGibbsLinear (primeEnergyProfile M) β μ) := by
  exact gibbsLinear_commute_totalNumber (fun p => primeEnergyProfile M p - μ) β

theorem primeCutoff_signed_gibbs_trace
    (M : ℕ) (β : ℝ) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (signedGibbsLinear (primeEnergyProfile M) β) =
      ∏ p : PrimeCutoff M,
        (1 - (localBoltzmann (primeEnergyProfile M p) β : ℂ)) := by
  exact trace_signedGibbsLinear_eq_product (primeEnergyProfile M) β

theorem primeCutoff_gibbs_mul_signed_eq_square
    (M : ℕ) (β : ℝ) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (gibbsLinear (primeEnergyProfile M) β) *
      LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (signedGibbsLinear (primeEnergyProfile M) β) =
      ∏ p : PrimeCutoff M,
        (1 - (localBoltzmann (primeEnergyProfile M p) β : ℂ) ^ 2) := by
  rw [primeCutoff_gibbs_trace, primeCutoff_signed_gibbs_trace]
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_congr
  intro p
  ring

theorem primeCutoff_signed_factor_ne_zero
    (M : ℕ) (β : ℝ) (hβ : β ≠ 0) (p : PrimeCutoff M) :
    1 - (localBoltzmann (primeEnergyProfile M p) β : ℂ) ≠ 0 := by
  intro h
  have hcomplex : (localBoltzmann (primeEnergyProfile M p) β : ℂ) = 1 := by
    exact (sub_eq_zero.mp h).symm
  have hreal : localBoltzmann (primeEnergyProfile M p) β = 1 := by
    exact_mod_cast hcomplex
  have hexp : -β * primeEnergyProfile M p = 0 := by
    exact (Real.exp_eq_one_iff _).mp hreal
  have hβ' : -β ≠ 0 := neg_ne_zero.mpr hβ
  have hp' : primeEnergyProfile M p ≠ 0 :=
    prime_log_ne_zero p.1
  exact (mul_ne_zero hβ' hp') hexp

theorem primeCutoff_signed_gibbs_trace_ne_zero
    (M : ℕ) (β : ℝ) (hβ : β ≠ 0) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (signedGibbsLinear (primeEnergyProfile M) β) ≠ 0 := by
  rw [primeCutoff_signed_gibbs_trace]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _hp
  exact primeCutoff_signed_factor_ne_zero M β hβ p

theorem primeCutoff_signed_gibbs_commute_totalNumber
    (M : ℕ) (β : ℝ) :
    (signedGibbsLinear (primeEnergyProfile M) β).comp totalNumberLinear =
      totalNumberLinear.comp (signedGibbsLinear (primeEnergyProfile M) β) := by
  exact signedGibbsLinear_commute_totalNumber (primeEnergyProfile M) β

theorem primeCutoff_signed_gibbs_commute_hamiltonian
    (M : ℕ) (β : ℝ) :
    (signedGibbsLinear (primeEnergyProfile M) β).comp
        (hamiltonianLinear (primeEnergyProfile M)) =
      (hamiltonianLinear (primeEnergyProfile M)).comp
        (signedGibbsLinear (primeEnergyProfile M) β) := by
  exact signedGibbsLinear_commute_hamiltonian (primeEnergyProfile M) β

theorem primeCutoff_signed_gibbs_trace_zero_at_zero
    (M : ℕ) (hM : 2 ≤ M) :
    LinearMap.trace ℂ (Vec (PrimeCutoff M))
        (signedGibbsLinear (primeEnergyProfile M) 0) = 0 := by
  letI : Nonempty (PrimeCutoff M) :=
    ⟨⟨⟨2, Nat.prime_two⟩, hM⟩⟩
  have h := trace_parityLinear_eq_zero (ι := PrimeCutoff M)
  simpa [signedGibbsLinear, gibbsLinear] using h

end InfoGeometry.Arithmetic.PrimeCutoffFiniteFock
