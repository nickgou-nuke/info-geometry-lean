/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Thermodynamics.FiniteGibbsRelative

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

theorem primon_log_energy_fisher_pos
    (M : PrimeEnergyModel ι) (θ : FiniteTemperature ι)
    (hZ : 0 < Z θ) :
    0 < fisherMetric θ (logPrimeEnergy M) (logPrimeEnergy M) := by
  exact fisherMetric_self_pos_of_nonconstant θ (logPrimeEnergy M) hZ
    M.logEnergy_nonconstant

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
