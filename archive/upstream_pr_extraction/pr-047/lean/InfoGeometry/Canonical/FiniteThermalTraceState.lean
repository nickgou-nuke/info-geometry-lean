import InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
import InfoGeometry.OperatorAlgebra.SpinUnruhCalibration
import InfoGeometry.Prequantum.AlgebraicGNSState

/-!
# Finite thermal trace state

This owner records the part of the finite thermal construction that is
available without a spectral theorem: the normalized matrix trace on the
noncommutative matrix stages.  The inverse temperature is calibrated by the
Unruh relation, while positivity and normalization are proved from the native
matrix-trace lemmas.  No Gibbs exponential or KMS strip is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteThermalTraceState

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.OperatorAlgebra.SpinUnruhCalibration
open InfoGeometry.Meta.MarkovJonesInduction
open InfoGeometry.Prequantum.AlgebraicGNSState

abbrev MatrixState := MatrixStage

def inverseTemperature (acceleration : ℝ) : ℝ :=
  unruhBeta acceleration

theorem inverseTemperature_eq (acceleration : ℝ) :
    inverseTemperature acceleration = 2 * Real.pi / acceleration :=
  rfl

def finiteState (n : ℕ) : RealAlgebraicState (MatrixState n) :=
  matrixTraceRealAlgebraicState n

@[simp] theorem finiteState_one (n : ℕ) :
    (finiteState n).eval 1 = 1 := by
  exact (finiteState n).eval_one

theorem finiteState_positive (n : ℕ) (A : MatrixState n) :
    0 ≤ (finiteState n).eval (star A * A) := by
  exact (finiteState n).positive A

theorem finiteState_star (n : ℕ) (A : MatrixState n) :
    (finiteState n).eval (star A) = (finiteState n).eval A := by
  change (matrixTraceFunctional n (star A)).re =
    (matrixTraceFunctional n A).re
  rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
  have htrace : Matrix.trace (star A) = star (Matrix.trace A) := by
    rw [← Matrix.trace_conjTranspose]
    rfl
  rw [htrace]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hcoef : (1 / (2 ^ n : ℂ)).im = 0 := by
    have hcast : (1 / (2 ^ n : ℂ)) = ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.ofReal_im]
  rw [hcoef]
  ring

theorem finiteState_cyclic (n : ℕ) (A B : MatrixState n) :
    (finiteState n).eval (A * B) = (finiteState n).eval (B * A) := by
  change (matrixTraceFunctional n (A * B)).re =
    (matrixTraceFunctional n (B * A)).re
  rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply,
    Matrix.trace_mul_comm]

theorem finiteState_commutator_zero (n : ℕ) (A B : MatrixState n) :
    (finiteState n).eval (A * B - B * A) = 0 := by
  change (finiteState n).toLinearMap (A * B - B * A) = 0
  rw [map_sub]
  have hcyc := finiteState_cyclic n A B
  change (finiteState n).toLinearMap (A * B) =
    (finiteState n).toLinearMap (B * A) at hcyc
  rw [hcyc]
  exact sub_self _

theorem finiteState_stage_compatibility (n : ℕ) (A : MatrixState n) :
    (finiteState (n + 1)).eval (concreteStep n A) =
      (finiteState n).eval A := by
  change (matrixTraceRealAlgebraicState (n + 1)).eval (concreteStep n A) =
    (matrixTraceRealAlgebraicState n).eval A
  exact congrArg Complex.re (concrete_trace_compatible n A)

theorem finiteState_unruh_inverse_temperature
    (acceleration : ℝ) :
    inverseTemperature acceleration = 2 * Real.pi / acceleration := by
  rfl

theorem finiteState_unruh_temperature
    (acceleration : ℝ) (hacc : acceleration ≠ 0) :
    (inverseTemperature acceleration)⁻¹ =
      unruhTemperature acceleration := by
  unfold inverseTemperature unruhBeta unruhTemperature
  field_simp [hacc, Real.pi_ne_zero]

end InfoGeometry.Canonical.FiniteThermalTraceState
