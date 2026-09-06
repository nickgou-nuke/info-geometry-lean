import Mathlib.Tactic
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

noncomputable section

namespace InfoGeometry.Canonical.TomitaMatrixClosability

/-!
# Tomita matrix involution and trace inner-product preservation

For finite matrix stages, the adjoint involution is involutive, reverses the
trace inner product, and preserves its quadratic norm.
-/

/-- Stage `n` trace inner product. -/
def matrixTraceInnerProduct (n : ℕ) (A B : MatrixStage n) : ℂ :=
  matrixTraceState n (star A * B)

/-- Tomita modular involution on a finite matrix stage. -/
def tomitaInvolution (n : ℕ) (A : MatrixStage n) : MatrixStage n :=
  star A

theorem tomitaInvolution_involutive (n : ℕ) (A : MatrixStage n) :
    tomitaInvolution n (tomitaInvolution n A) = A := by
  dsimp [tomitaInvolution]
  exact star_star A

theorem tomitaInvolution_anti_isometry (n : ℕ) (A B : MatrixStage n) :
    matrixTraceInnerProduct n (tomitaInvolution n A) (tomitaInvolution n B) =
    matrixTraceInnerProduct n B A := by
  dsimp [matrixTraceInnerProduct, tomitaInvolution]
  rw [star_star, matrixTraceState_apply, matrixTraceState_apply,
    Matrix.trace_mul_comm A (star B)]

theorem tomitaInvolution_norm_preservation (n : ℕ) (A : MatrixStage n) :
    matrixTraceInnerProduct n (tomitaInvolution n A) (tomitaInvolution n A) =
    matrixTraceInnerProduct n A A := by
  exact tomitaInvolution_anti_isometry n A A

end InfoGeometry.Canonical.TomitaMatrixClosability
