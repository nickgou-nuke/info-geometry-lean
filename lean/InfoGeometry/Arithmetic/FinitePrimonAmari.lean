/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Thermodynamics.FiniteGibbsRelative
import InfoGeometry.Analytic.LogSumExp
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Finite primon Amari specialization

This file specializes the existing finite Cartan/Gibbs geometry to a finite
list of prime-labelled modes.  It intentionally proves only finite Fisher,
covariance, and Bregman identities; no infinite-dimensional or analytic
continuation statement is used.
-/

noncomputable section
open Classical

namespace InfoGeometry.Arithmetic.FinitePrimonAmari

open scoped BigOperators
open InfoGeometry.Thermodynamics.FiniteGibbsRelative
open InfoGeometry.Algebraic.CartanExponentialFamily
open InfoGeometry.Analytic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

structure PrimeEnergyModel (ι : Type*) where
  primeValue : ι → ℕ+
  logEnergy_nonconstant :
    ∃ i j : ι, Real.log (primeValue i : ℝ) ≠ Real.log (primeValue j : ℝ)

def logPrimeEnergy (M : PrimeEnergyModel ι) : ι → ℝ :=
  fun i => Real.log (M.primeValue i : ℝ)

noncomputable def primonFisherMatrix
    (M : PrimeEnergyModel ι) (θ : FiniteTemperature ι) :
  Matrix ι ι ℝ :=
  fun i j => fisherMetric θ
    (fun k => if k = i then logPrimeEnergy M k else 0)
    (fun k => if k = j then logPrimeEnergy M k else 0)

theorem primonFisherMatrix_apply
    (M : PrimeEnergyModel ι) (θ : FiniteTemperature ι) (i j : ι) :
    primonFisherMatrix M θ i j =
      fisherMetric θ
        (fun k => if k = i then logPrimeEnergy M k else 0)
        (fun k => if k = j then logPrimeEnergy M k else 0) := rfl

theorem primon_log_energy_fisher_covariance
    (θ : FiniteTemperature ι)
    (hZ : 0 < Z θ) (X Y : ι → ℝ) :
    fisherMetric θ X Y =
      expect θ (fun i => X i * Y i) - expect θ X * expect θ Y :=
  fisherMetric_eq_covariance θ X Y hZ

theorem primon_log_energy_fisher_nonneg
    (M : PrimeEnergyModel ι) (θ : FiniteTemperature ι)
    (hZ : 0 < Z θ) :
    0 ≤ fisherMetric θ (logPrimeEnergy M) (logPrimeEnergy M) :=
  fisherMetric_self_nonneg θ (logPrimeEnergy M) hZ

/-- Self-covariance is strictly positive for nonconstant observables. -/
theorem fisherCov_self_pos_of_exists_ne
    (θ : ι → ℝ) (X : ι → ℝ) (hZ : 0 < Z θ)
    (hne : ∃ i j, X i ≠ X j) :
    0 < fisherCov θ X X := by
  by_contra hnot
  have hzero : fisherCov θ X X = 0 :=
    le_antisymm (le_of_not_gt hnot) (fisherCov_self_nonneg θ X hZ)
  have hsq : ∀ i, (X i - expect θ X) = 0 := by
    intro i
    have hsum_nonneg : ∀ j (_ : j ∈ (Finset.univ : Finset ι)),
        0 ≤ prob θ j * (X j - expect θ X) * (X j - expect θ X) := by
      intro j _
      rw [mul_assoc]
      exact mul_nonneg (prob_nonneg θ hZ j) (mul_self_nonneg _)
    have hzero' : ∑ j, prob θ j * (X j - expect θ X) * (X j - expect θ X) = 0 := hzero
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hsum_nonneg).mp hzero' i (Finset.mem_univ i)
    have hprod : prob θ i * ((X i - expect θ X) * (X i - expect θ X)) = 0 := by
      simpa [mul_assoc] using hi
    have hsq0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (prob_pos θ hZ i))
    exact mul_self_eq_zero.mp hsq0
  obtain ⟨i, j, hij⟩ := hne
  have hi : X i = expect θ X := sub_eq_zero.mp (hsq i)
  have hj : X j = expect θ X := sub_eq_zero.mp (hsq j)
  exact hij (hi.trans hj.symm)

/-- Fisher metric self-pairing is strictly positive for nonconstant directions. -/
theorem fisherMetric_self_pos_of_nonconstant
    (θ : FiniteTemperature ι) (X : ι → ℝ) (hZ : 0 < Z θ)
    (hne : ∃ i j, X i ≠ X j) :
    0 < fisherMetric θ X X :=
  fisherCov_self_pos_of_exists_ne θ X hZ hne

theorem primon_log_energy_fisher_pos
    (M : PrimeEnergyModel ι) (θ : FiniteTemperature ι)
    (hZ : 0 < Z θ) :
    0 < fisherMetric θ (logPrimeEnergy M) (logPrimeEnergy M) := by
  exact fisherMetric_self_pos_of_nonconstant θ (logPrimeEnergy M) hZ
    M.logEnergy_nonconstant

/-- Directional second derivative of the Massieu potential is the Fisher quadratic form. -/
theorem deriv2_massieu_direction_at
    (θ : FiniteTemperature ι) (X : ι → ℝ) (t : ℝ) :
    deriv (fun s : ℝ =>
      deriv (fun r : ℝ =>
        massieuPotential (fun i => θ i + r * X i)) s) t =
      fisherMetric (fun i => θ i + t * X i) X X := by
  let w : ι → ℝ := fun i => Real.exp (θ i)
  have hw : ∀ i, 0 < w i := fun i => Real.exp_pos (θ i)
  have hslice : (fun r : ℝ => massieuPotential (fun i => θ i + r * X i)) =
      (fun r : ℝ => logSumExp w X r) := by
    funext r
    unfold massieuPotential massieu Phi Z logSumExp logSumExpPartition w
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Real.exp_add]
  rw [hslice]
  rw [logSumExp_secondDeriv_eq_variance w X hw t]
  rw [logSumExpVariance_eq_centered w X hw t]
  unfold fisherMetric fisherCov expect prob Z w
  have hpart : logSumExpPartition (fun i => Real.exp (θ i)) X t = ∑ i : ι, Real.exp (θ i + t * X i) := by
    unfold logSumExpPartition
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Real.exp_add]
  have hweight : (fun i => logSumExpWeight (fun i => Real.exp (θ i)) X t i) =
      (fun i => Real.exp (θ i + t * X i) / ∑ j : ι, Real.exp (θ j + t * X j)) := by
    funext i
    unfold logSumExpWeight
    rw [hpart]
    congr 1
    rw [← Real.exp_add]
  simp_rw [hweight, pow_two, mul_assoc]

theorem primon_massieu_second_variation
    (M : PrimeEnergyModel ι) (θ : FiniteTemperature ι) (t : ℝ)
    :
    deriv (fun s : ℝ =>
      deriv (fun r : ℝ =>
        massieuPotential (fun i => θ i + r * logPrimeEnergy M i)) s) t =
      fisherMetric (fun i => θ i + t * logPrimeEnergy M i)
        (logPrimeEnergy M) (logPrimeEnergy M) := by
  exact deriv2_massieu_direction_at θ (logPrimeEnergy M) t

theorem primon_kl_eq_massieu_bregman
    (θ η : FiniteTemperature ι) (hZ : 0 < Z θ) :
    relativeEntropy θ η = massieuBregman θ η :=
  relativeEntropy_eq_massieuBregman θ η hZ

end InfoGeometry.Arithmetic.FinitePrimonAmari
