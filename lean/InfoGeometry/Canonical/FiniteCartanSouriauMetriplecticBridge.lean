import InfoGeometry.Algebraic.CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SuperMetriplectic.Flow

/-!
# Finite Cartan--Souriau covariance as native Onsager data

The finite two-charge Gibbs family already carries a positive covariance
matrix.  This file realizes that matrix as the Onsager operator in the native
`OnsagerMetricData` carrier.  It does not identify this finite packet with an
analytic zeta Fisher metric or with a particular metriplectic dynamics.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteCartanSouriauMetriplecticBridge

open scoped BigOperators
open Finset

open InfoGeometry.Algebraic.CartanSouriauMassieu
open InfoGeometry.SuperMetriplectic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def euclideanPairingFin2 (x y : Fin 2 → ℝ) : ℝ :=
  dotProduct x y

theorem covariance_dotProduct_eq_centered_expectation
    (F : Family ι) (β x : Fin 2 → ℝ) :
    dotProduct x ((chargeCovarianceMatrix F β).mulVec x) =
      ∑ m : ι, probability F β m *
        (∑ a : Fin 2, x a * centeredCharge F β m a) ^ (2 : ℕ) := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  calc
    (∑ a : Fin 2, ∑ b : Fin 2,
        x a * (chargeCovarianceMatrix F β a b * x b)) =
        ∑ a : Fin 2, ∑ b : Fin 2,
          x a * chargeCovarianceMatrix F β a b * x b := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
    _ = ∑ m : ι, probability F β m *
        (∑ a : Fin 2, x a * centeredCharge F β m a) ^ (2 : ℕ) := by
          simpa [chargeCovarianceMatrix] using
            (chargeCovariance_quadratic_eq_expect_sq F β x)

noncomputable def finiteCartanOnsagerData
    (F : Family ι) (β : Fin 2 → ℝ) :
    OnsagerMetricData (Fin 2 → ℝ) where
  onsager := Matrix.toLin' (chargeCovarianceMatrix F β)
  pairing := euclideanPairingFin2
  metric_symmetric := by
    intro x y
    unfold euclideanPairingFin2
    change dotProduct x ((chargeCovarianceMatrix F β).mulVec y) =
      dotProduct y ((chargeCovarianceMatrix F β).mulVec x)
    have hC : (chargeCovarianceMatrix F β).transpose =
        chargeCovarianceMatrix F β := by
      ext a b
      exact chargeCovariance_symm F β b a
    calc
      dotProduct x ((chargeCovarianceMatrix F β).mulVec y) =
          Matrix.vecMul x (chargeCovarianceMatrix F β) ⬝ᵥ y := by
            exact Matrix.dotProduct_mulVec x _ y
      _ = ((chargeCovarianceMatrix F β).transpose.mulVec x) ⬝ᵥ y := by
            rw [Matrix.mulVec_transpose]
      _ = ((chargeCovarianceMatrix F β).mulVec x) ⬝ᵥ y := by
            rw [hC]
      _ = dotProduct y ((chargeCovarianceMatrix F β).mulVec x) := by
            exact dotProduct_comm _ _
  metric_nonnegative := by
    intro x
    rw [show (euclideanPairingFin2 x)
          ((Matrix.toLin' (chargeCovarianceMatrix F β)) x) =
        dotProduct x ((chargeCovarianceMatrix F β).mulVec x) by rfl]
    rw [covariance_dotProduct_eq_centered_expectation F β x]
    exact Finset.sum_nonneg fun m _ =>
      mul_nonneg (le_of_lt (probability_pos F β m)) (sq_nonneg _)
  pairing_zero_right := by
    intro x
    simp [euclideanPairingFin2]

theorem finiteCartanOnsagerData_quadratic_eq_covariance
    (F : Family ι) (β x : Fin 2 → ℝ) :
    (finiteCartanOnsagerData F β).quadratic x =
      ∑ a : Fin 2, ∑ b : Fin 2,
        x a * chargeCovariance F β a b * x b := by
  unfold OnsagerMetricData.quadratic finiteCartanOnsagerData
    euclideanPairingFin2 chargeCovarianceMatrix
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  ring

theorem finiteCartanOnsagerData_quadratic_eq_centered_expectation
    (F : Family ι) (β x : Fin 2 → ℝ) :
    (finiteCartanOnsagerData F β).quadratic x =
      ∑ m : ι, probability F β m *
        (∑ a : Fin 2, x a * centeredCharge F β m a) ^ (2 : ℕ) := by
  rw [finiteCartanOnsagerData_quadratic_eq_covariance]
  exact chargeCovariance_quadratic_eq_expect_sq F β x

theorem finiteCartanOnsagerData_quadratic_nonnegative
    (F : Family ι) (β x : Fin 2 → ℝ) :
    0 ≤ (finiteCartanOnsagerData F β).quadratic x := by
  exact (finiteCartanOnsagerData F β).quadratic_nonnegative x

/-! ## Native finite metriplectic realization

This packages the finite covariance Onsager operator into the generic
`MetriplecticFlow` carrier.  It is not an identification with an actual zeta
dynamical system.
-/

noncomputable def finiteCartanMetriplecticFlow
    (F : Family ι) (β x : Fin 2 → ℝ) :
    MetriplecticFlow (Fin 2 → ℝ) where
  metric := finiteCartanOnsagerData F β
  entropyForce := x
  energyForce := 0
  reversibleFlow := 0
  dissipativeFlow := (finiteCartanOnsagerData F β).onsager x
  totalFlow := (finiteCartanOnsagerData F β).onsager x
  entropyProduction := (finiteCartanOnsagerData F β).quadratic x
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := by simp
  energy_degeneracy := by simp
  entropyProduction_eq_quadratic := rfl

@[simp] theorem finiteCartanMetriplecticFlow_dissipativeFlow
    (F : Family ι) (β x : Fin 2 → ℝ) :
    (finiteCartanMetriplecticFlow F β x).dissipativeFlow =
      (finiteCartanOnsagerData F β).onsager x := rfl

@[simp] theorem finiteCartanMetriplecticFlow_totalFlow
    (F : Family ι) (β x : Fin 2 → ℝ) :
    (finiteCartanMetriplecticFlow F β x).totalFlow =
      (finiteCartanOnsagerData F β).onsager x := rfl

@[simp] theorem finiteCartanMetriplecticFlow_entropyProduction
    (F : Family ι) (β x : Fin 2 → ℝ) :
    (finiteCartanMetriplecticFlow F β x).entropyProduction =
      (finiteCartanOnsagerData F β).quadratic x := rfl

theorem finiteCartanMetriplecticFlow_entropyProduction_nonnegative
    (F : Family ι) (β x : Fin 2 → ℝ) :
    0 ≤ (finiteCartanMetriplecticFlow F β x).entropyProduction := by
  exact finiteCartanOnsagerData_quadratic_nonnegative F β x

theorem finiteCartanMetriplecticFlow_entropyProduction_eq_centered_expectation
    (F : Family ι) (β x : Fin 2 → ℝ) :
    (finiteCartanMetriplecticFlow F β x).entropyProduction =
      ∑ m : ι, probability F β m *
        (∑ a : Fin 2, x a * centeredCharge F β m a) ^ (2 : ℕ) := by
  exact finiteCartanOnsagerData_quadratic_eq_centered_expectation F β x

theorem finiteCartanMetriplecticFlow_entropyProduction_eq_zero_iff
    (F : Family ι) (hF : ChargesSeparateDirections F)
    (β x : Fin 2 → ℝ) :
    (finiteCartanMetriplecticFlow F β x).entropyProduction = 0 ↔ x = 0 := by
  rw [finiteCartanMetriplecticFlow_entropyProduction,
    finiteCartanOnsagerData_quadratic_eq_covariance]
  constructor
  · intro hzero
    by_contra hx
    have hpos := chargeCovariance_posDef_of_separatesDirections F hF β x hx
    linarith
  · intro hx
    subst x
    simp

theorem finiteCartanMetriplecticFlow_equilibrium_iff
    (F : Family ι) (hF : ChargesSeparateDirections F)
    (β x : Fin 2 → ℝ) :
    (finiteCartanMetriplecticFlow F β x).IsDissipativeEquilibrium ↔ x = 0 := by
  rw [MetriplecticFlow.equilibrium_iff_dissipativeFlow_eq_zero]
  constructor
  · intro heq
    apply (finiteCartanMetriplecticFlow_entropyProduction_eq_zero_iff F hF β x).mp
    rw [(finiteCartanMetriplecticFlow F β x).entropyProduction_eq_quadratic,
      heq]
    change dotProduct x 0 = 0
    simp
  · intro hx
    subst x
    simp [finiteCartanMetriplecticFlow]

end InfoGeometry.Canonical.FiniteCartanSouriauMetriplecticBridge
