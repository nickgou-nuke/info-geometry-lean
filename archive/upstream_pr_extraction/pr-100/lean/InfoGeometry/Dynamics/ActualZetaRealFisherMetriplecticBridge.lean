import InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge
import InfoGeometry.SuperMetriplectic.Flow

/-!
# Actual real zeta Fisher coefficient as a metriplectic shadow

This owner packages the exact one-parameter Fisher coefficient of the real
zeta partition readout into the native `MetriplecticFlow` carrier.  It is a
scalar Fisher/Onsager realization on `1 < beta`; it is not asserted to be the
unique physical zeta dynamics, nor does it make a complex-plane positivity or
critical-line claim.
-/

noncomputable section

namespace InfoGeometry.Dynamics.ActualZetaRealFisherMetriplecticBridge

open scoped LSeries.notation

open InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge
open InfoGeometry.SuperMetriplectic

noncomputable def actualZetaRealFisherLinearMap
    (beta : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun := fun x => actualZetaRealFisherInformation beta * x
  map_add' := by
    intro x y
    ring
  map_smul' := by
    intro a x
    simp [smul_eq_mul]
    ring

noncomputable def actualZetaRealFisherOnsagerData
    (beta : ℝ) (hbeta : 1 < beta) : OnsagerMetricData ℝ where
  onsager := actualZetaRealFisherLinearMap beta
  pairing := fun x y => x * y
  metric_symmetric := by
    intro x y
    change x * (actualZetaRealFisherInformation beta * y) =
      y * (actualZetaRealFisherInformation beta * x)
    ring
  metric_nonnegative := by
    intro x
    change 0 <= x * (actualZetaRealFisherInformation beta * x)
    have hF := actualZetaRealFisherInformation_nonneg hbeta
    nlinarith [sq_nonneg x]
  pairing_zero_right := by
    intro x
    simp

noncomputable def actualZetaRealFisherMetriplecticFlow
    (beta x : ℝ) (hbeta : 1 < beta) : MetriplecticFlow ℝ where
  metric := actualZetaRealFisherOnsagerData beta hbeta
  entropyForce := x
  energyForce := 0
  reversibleFlow := 0
  dissipativeFlow := actualZetaRealFisherInformation beta * x
  totalFlow := actualZetaRealFisherInformation beta * x
  entropyProduction := actualZetaRealFisherInformation beta * x ^ 2
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := by simp
  energy_degeneracy := by simp
  entropyProduction_eq_quadratic := by
    change actualZetaRealFisherInformation beta * x ^ 2 =
      x * (actualZetaRealFisherInformation beta * x)
    ring

@[simp] theorem actualZetaRealFisherMetriplecticFlow_dissipativeFlow
    (beta x : ℝ) (hbeta : 1 < beta) :
    (actualZetaRealFisherMetriplecticFlow beta x hbeta).dissipativeFlow =
      actualZetaRealFisherInformation beta * x := rfl

@[simp] theorem actualZetaRealFisherMetriplecticFlow_entropyProduction
    (beta x : ℝ) (hbeta : 1 < beta) :
    (actualZetaRealFisherMetriplecticFlow beta x hbeta).entropyProduction =
      actualZetaRealFisherInformation beta * x ^ 2 := rfl

theorem actualZetaRealFisherMetriplecticFlow_entropyProduction_nonnegative
    (beta x : ℝ) (hbeta : 1 < beta) :
    0 <= (actualZetaRealFisherMetriplecticFlow beta x hbeta).entropyProduction := by
  exact (actualZetaRealFisherMetriplecticFlow beta x hbeta).entropyProduction_nonnegative

theorem actualZetaRealFisherMetriplecticFlow_entropyProduction_eq_logMul
    (beta x : ℝ) (hbeta : 1 < beta) :
    (actualZetaRealFisherMetriplecticFlow beta x hbeta).entropyProduction =
      (LSeries
        (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
        (beta : ℂ)).re * x ^ 2 := by
  rw [actualZetaRealFisherMetriplecticFlow_entropyProduction,
    actualZetaRealFisherInformation_eq_vonMangoldt_logMul_re hbeta]

theorem actualZetaRealFisherMetriplecticFlow_entropyProduction_zero_of_force_zero
    (beta x : ℝ) (hbeta : 1 < beta) (hx : x = 0) :
    (actualZetaRealFisherMetriplecticFlow beta x hbeta).entropyProduction = 0 := by
  rw [actualZetaRealFisherMetriplecticFlow_entropyProduction, hx]
  simp

theorem actualZetaRealFisherMetriplecticFlow_entropyProduction_zero_iff
    (beta x : ℝ) (hbeta : 1 < beta) :
    (actualZetaRealFisherMetriplecticFlow beta x hbeta).entropyProduction = 0 ↔
      x = 0 := by
  rw [actualZetaRealFisherMetriplecticFlow_entropyProduction]
  have hF : 0 < actualZetaRealFisherInformation beta :=
    actualZetaRealFisherInformation_pos hbeta
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hFzero | hxsq
    · exact False.elim ((ne_of_gt hF) hFzero)
    · exact (sq_eq_zero_iff).mp hxsq
  · intro hx
    simp [hx]

theorem actualZetaRealFisherMetriplecticFlow_dissipativeFlow_zero_iff
    (beta x : ℝ) (hbeta : 1 < beta) :
    (actualZetaRealFisherMetriplecticFlow beta x hbeta).dissipativeFlow = 0 ↔
      x = 0 := by
  rw [actualZetaRealFisherMetriplecticFlow_dissipativeFlow]
  have hF : 0 < actualZetaRealFisherInformation beta :=
    actualZetaRealFisherInformation_pos hbeta
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hFzero | hx
    · exact False.elim ((ne_of_gt hF) hFzero)
    · exact hx
  · intro hx
    simp [hx]

end InfoGeometry.Dynamics.ActualZetaRealFisherMetriplecticBridge
