import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SuperMetriplectic.Flow

/-!
# Actual zeta curvature as a finite metriplectic coefficient

This owner uses the already proved native Riemann-zeta/von-Mangoldt curvature
readout on the real half-plane `1 < β`.  It packages that scalar into the
generic finite `MetriplecticFlow` carrier.  It does not identify the scalar
with a Fisher metric, nor does it assert a zeta critical-line dynamical law.
-/

noncomputable section

namespace InfoGeometry.Dynamics.ActualZetaCurvatureMetriplecticBridge

open scoped LSeries.notation

open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
open InfoGeometry.SuperMetriplectic

noncomputable def actualZetaCurvatureLinearMap
    (β : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun := fun x => actualVonMangoldtCurvature β * x
  map_add' := by
    intro x y
    ring
  map_smul' := by
    intro a x
    simp [smul_eq_mul]
    ring

noncomputable def actualZetaCurvatureOnsagerData
    (β : ℝ) (hβ : 1 < β) : OnsagerMetricData ℝ where
  onsager := actualZetaCurvatureLinearMap β
  pairing := fun x y => x * y
  metric_symmetric := by
    intro x y
    change x * (actualVonMangoldtCurvature β * y) =
      y * (actualVonMangoldtCurvature β * x)
    ring
  metric_nonnegative := by
    intro x
    change 0 ≤ x * (actualVonMangoldtCurvature β * x)
    have hc := actualVonMangoldtCurvature_nonneg hβ
    nlinarith [sq_nonneg x]
  pairing_zero_right := by
    intro x
    simp

noncomputable def actualZetaCurvatureMetriplecticFlow
    (β x : ℝ) (hβ : 1 < β) : MetriplecticFlow ℝ where
  metric := actualZetaCurvatureOnsagerData β hβ
  entropyForce := x
  energyForce := 0
  reversibleFlow := 0
  dissipativeFlow := actualVonMangoldtCurvature β * x
  totalFlow := actualVonMangoldtCurvature β * x
  entropyProduction := actualVonMangoldtCurvature β * x ^ 2
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := by simp
  energy_degeneracy := by simp
  entropyProduction_eq_quadratic := by
    change actualVonMangoldtCurvature β * x ^ 2 =
      x * (actualVonMangoldtCurvature β * x)
    ring

@[simp] theorem actualZetaCurvatureMetriplecticFlow_dissipativeFlow
    (β x : ℝ) (hβ : 1 < β) :
    (actualZetaCurvatureMetriplecticFlow β x hβ).dissipativeFlow =
      actualVonMangoldtCurvature β * x := rfl

@[simp] theorem actualZetaCurvatureMetriplecticFlow_entropyProduction
    (β x : ℝ) (hβ : 1 < β) :
    (actualZetaCurvatureMetriplecticFlow β x hβ).entropyProduction =
      actualVonMangoldtCurvature β * x ^ 2 := rfl

theorem actualZetaCurvatureMetriplecticFlow_entropyProduction_nonnegative
    (β x : ℝ) (hβ : 1 < β) :
    0 ≤ (actualZetaCurvatureMetriplecticFlow β x hβ).entropyProduction := by
  exact (actualZetaCurvatureMetriplecticFlow β x hβ).entropyProduction_nonnegative

theorem actualZetaCurvatureMetriplecticFlow_entropyProduction_eq_double_logMul
    (β x : ℝ) (hβ : 1 < β) :
    (actualZetaCurvatureMetriplecticFlow β x hβ).entropyProduction =
      (LSeries
        (LSeries.logMul
          (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)))
        (β : ℂ)).re * x ^ 2 := by
  rw [actualZetaCurvatureMetriplecticFlow_entropyProduction,
    actualVonMangoldtCurvature_eq_double_logMul hβ]

theorem actualZetaCurvatureMetriplecticFlow_dissipativeFlow_eq_zero_iff
    (β x : ℝ) (hβ : 1 < β)
    (hcurv : 0 < actualVonMangoldtCurvature β) :
    (actualZetaCurvatureMetriplecticFlow β x hβ).dissipativeFlow = 0 ↔ x = 0 := by
  rw [actualZetaCurvatureMetriplecticFlow_dissipativeFlow]
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hcurv)
  · intro hx
    simp [hx]

end InfoGeometry.Dynamics.ActualZetaCurvatureMetriplecticBridge
