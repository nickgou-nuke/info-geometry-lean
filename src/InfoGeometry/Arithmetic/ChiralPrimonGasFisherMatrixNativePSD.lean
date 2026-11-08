import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.ChiralPrimonGasFisherMatrixBridge

/-!
# Native matrix packaging for the finite fermionic covariance readout

This owner packages the already-proved finite fermionic covariance quadratic
form as a genuine `Matrix (Fin 2) (Fin 2) ℝ`.  Its positive-semidefiniteness is
proved through Mathlib's Gram-matrix API and finite-sum closure.  No analytic
zeta identification or infinite-volume Fisher statement is made here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.ChiralPrimonGasFisherMatrixNativePSD

open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.ChiralPrimonGasVarianceBridge

/-- The two-component local energy/number sensitivity of a prime mode. -/
def localFermionSensitivity (p : ℕ) : Fin 2 → ℝ
  | 0 => primeEnergy p
  | 1 => 1

@[simp] theorem localFermionSensitivity_zero (p : ℕ) :
    localFermionSensitivity p 0 = primeEnergy p := rfl

@[simp] theorem localFermionSensitivity_one (p : ℕ) :
    localFermionSensitivity p 1 = 1 := rfl

/-- The finite sector covariance matrix in the `(energy, number)` basis. -/
def sectorCovarianceMatrix (G : PrimonGas) (beta nu : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  match i, j with
  | 0, 0 => (sector G beta nu).varEnergy
  | 0, 1 => (sector G beta nu).covEnergyNumber
  | 1, 0 => (sector G beta nu).covEnergyNumber
  | 1, 1 => (sector G beta nu).varNumber

theorem sectorCovarianceMatrix_eq_weightedGram_sum
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu : ℝ) :
    sectorCovarianceMatrix G beta nu =
      ∑ p ∈ G.register.primes,
        localNumberVariance Statistics.fermion beta nu p •
          Matrix.gram ℝ (localFermionSensitivity p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.sum_apply] <;>
    simp [sectorCovarianceMatrix, sector, hG, localFermionSensitivity,
      Matrix.gram, localEnergyVariance,
      localEnergyNumberCovariance, localNumberVariance] <;>
    apply Finset.sum_congr rfl <;>
    intro p hp <;>
    ring

private theorem weightedGram_sum_posSemidef
    (S : Finset ℕ) (beta nu : ℝ) :
    Matrix.PosSemidef
      (∑ p ∈ S,
        localNumberVariance Statistics.fermion beta nu p •
          Matrix.gram ℝ (localFermionSensitivity p)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Matrix.PosSemidef.zero]
  | @insert p S hp ih =>
      simp only [Finset.sum_insert hp]
      apply Matrix.PosSemidef.add
      · exact (Matrix.posSemidef_gram ℝ (localFermionSensitivity p)).smul
          (localNumberVariance_fermion_nonneg beta nu p)
      · exact ih

/-- The finite fermionic covariance matrix is positive semidefinite. -/
theorem sectorCovarianceMatrix_posSemidef
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu : ℝ) :
    Matrix.PosSemidef (sectorCovarianceMatrix G beta nu) := by
  rw [sectorCovarianceMatrix_eq_weightedGram_sum G hG beta nu]
  exact weightedGram_sum_posSemidef G.register.primes beta nu

end InfoGeometry.Arithmetic.ChiralPrimonGasFisherMatrixNativePSD
