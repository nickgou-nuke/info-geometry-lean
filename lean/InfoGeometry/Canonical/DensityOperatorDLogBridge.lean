import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.QuantumGeometry.DensityOperatorDLogHomomorphism

noncomputable section

namespace InfoGeometry.Canonical.DensityOperatorDLogBridge

open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.QuantumGeometry.DensityDLog
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The scalar density operator associated to a positive real unit. -/
noncomputable def scalarDensityOperator (u : ℝˣ) : EndH E :=
  (u : ℝ) • idEndH E

@[simp] theorem scalarDensityOperator_apply (u : ℝˣ)
    (v : DoubledSpace E) :
    scalarDensityOperator (E := E) u v = (u : ℝ) • v := by
  simp [scalarDensityOperator, idEndH]

@[simp] theorem scalarDensityOperator_one :
    scalarDensityOperator (E := E) (1 : ℝˣ) = idEndH E := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;> simp [scalarDensityOperator, idEndH]

@[simp] theorem scalarDensityOperator_mul (u v : ℝˣ) :
    scalarDensityOperator (E := E) (u * v)
      = scalarDensityOperator (E := E) u * scalarDensityOperator (E := E) v := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;> simp [scalarDensityOperator, idEndH, smul_smul]

@[simp] theorem scalarDensityOperator_inv_mul (u : ℝˣ) :
    scalarDensityOperator (E := E) (u⁻¹) * scalarDensityOperator (E := E) u =
      idEndH E := by
  rw [← scalarDensityOperator_mul, inv_mul_cancel, scalarDensityOperator_one]

@[simp] theorem scalarDensityOperator_mul_inv (u : ℝˣ) :
    scalarDensityOperator (E := E) u * scalarDensityOperator (E := E) (u⁻¹) =
      idEndH E := by
  rw [← scalarDensityOperator_mul, mul_inv_cancel, scalarDensityOperator_one]

/-- Operator-valued logarithmic derivative of a scalar density unit. -/
noncomputable def densityOperatorDLog
    (D : CommRingDerivation ℝ) (u : ℝˣ) : EndH E :=
  dlog D u • idEndH E

@[simp] theorem densityOperatorDLog_apply
    (D : CommRingDerivation ℝ) (u : ℝˣ) (v : DoubledSpace E) :
    densityOperatorDLog (E := E) D u v = dlog D u • v := by
  simp [densityOperatorDLog, idEndH]

@[simp] theorem densityOperatorDLog_one (D : CommRingDerivation ℝ) :
    densityOperatorDLog (E := E) D (1 : ℝˣ) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;> simp [densityOperatorDLog, idEndH]

/-- `dlog` is additive after passing from scalar density units to scalar density operators. -/
theorem densityOperatorDLog_mul
    (D : CommRingDerivation ℝ) (u v : ℝˣ) :
    densityOperatorDLog (E := E) D (u * v)
      = densityOperatorDLog (E := E) D u + densityOperatorDLog (E := E) D v := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;> simp [densityOperatorDLog, dlog_mul, add_smul, idEndH]

theorem densityOperatorDLog_inv
    (D : CommRingDerivation ℝ) (u : ℝˣ) :
    densityOperatorDLog (E := E) D (u⁻¹) =
      -densityOperatorDLog (E := E) D u := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [densityOperatorDLog, dlog_inv, idEndH]

/-- Bundled multiplicative-to-additive interpretation of `dlog` on scalar density operators. -/
def densityOperatorDLogHom
    (D : CommRingDerivation ℝ) : ℝˣ →* Multiplicative (EndH E) where
  toFun u := Multiplicative.ofAdd (densityOperatorDLog (E := E) D u)
  map_one' := by
    change Multiplicative.ofAdd (densityOperatorDLog (E := E) D 1) = Multiplicative.ofAdd 0
    rw [densityOperatorDLog_one]
  map_mul' u v := by
    change Multiplicative.ofAdd (densityOperatorDLog (E := E) D (u * v)) =
      Multiplicative.ofAdd (densityOperatorDLog (E := E) D u) *
        Multiplicative.ofAdd (densityOperatorDLog (E := E) D v)
    rw [densityOperatorDLog_mul]
    rfl

/-- The positive RN datum determines a canonical real unit. -/
noncomputable def rnDerivativeUnit
    (M : ModularRadonNikodymData E) : ℝˣ :=
  Units.mk0 M.rnDerivative M.rnDerivative_pos.ne'

@[simp] theorem rnDerivativeUnit_val
    (M : ModularRadonNikodymData E) :
    ((rnDerivativeUnit M : ℝˣ) : ℝ) = M.rnDerivative := rfl

/-- The modular operator attached to RN data is the scalar density operator defined by the RN unit. -/
@[simp] theorem modularOperator_eq_scalarDensityOperator_rnDerivativeUnit
    (M : ModularRadonNikodymData E) :
    M.modularOperator = scalarDensityOperator (E := E) (rnDerivativeUnit M) := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [ModularRadonNikodymData.modularOperator, scalarDensityOperator, rnDerivativeUnit, idEndH]

end InfoGeometry.Canonical.DensityOperatorDLogBridge

end noncomputable section
