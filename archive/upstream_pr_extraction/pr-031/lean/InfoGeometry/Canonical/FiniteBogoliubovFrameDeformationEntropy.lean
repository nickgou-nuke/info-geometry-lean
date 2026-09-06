import InfoGeometry.Canonical.MatrixDetExpTraceJacobi
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Finite Bogoliubov frame-deformation entropy

This file owns the finite complex-matrix continuous-functional-calculus layer
of frame deformation.  The multiplicative datum is an invertible
current-over-reference frame.  Its positive polar distortion is `|E|`, and its
additive deformation generator is `-log |E|`.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy

open scoped Matrix MatrixOrder Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ
local notation "Frame" => Matrix.GeneralLinearGroup n ℂ

/-- Vacuum and current unnormalized finite complex frames. -/
structure FramePair where
  vacuum : Frame
  current : Frame

namespace FramePair

/-- Current-over-vacuum relative frame as a unit. -/
def relativeFrame (F : FramePair (n := n)) : Frame :=
  F.current * F.vacuum⁻¹

/-- Matrix underlying the current-over-vacuum relative frame. -/
def relativeVielbein (F : FramePair (n := n)) : Mat :=
  F.relativeFrame

theorem relativeVielbein_isUnit (F : FramePair (n := n)) :
    IsUnit F.relativeVielbein := by
  exact Units.isUnit F.relativeFrame

/-- Positive polar distortion `|E|` of the relative frame. -/
def polarVolumeOperator (F : FramePair (n := n)) : Mat :=
  CFC.abs F.relativeVielbein

/-- The polar distortion squares to the Gram operator `E† E`. -/
theorem polarVolumeOperator_sq (F : FramePair (n := n)) :
    F.polarVolumeOperator * F.polarVolumeOperator =
      star F.relativeVielbein * F.relativeVielbein := by
  exact CFC.abs_mul_abs F.relativeVielbein

/-- The polar distortion of an invertible relative frame is invertible. -/
theorem polarVolumeOperator_isUnit (F : FramePair (n := n)) :
    IsUnit F.polarVolumeOperator := by
  rw [← isUnit_mul_self_iff]
  rw [F.polarVolumeOperator_sq]
  exact (F.relativeVielbein_isUnit.star).mul F.relativeVielbein_isUnit

/-- The polar distortion of an invertible relative frame is strictly positive. -/
theorem polarVolumeOperator_isStrictlyPositive (F : FramePair (n := n)) :
    IsStrictlyPositive F.polarVolumeOperator :=
  F.polarVolumeOperator_isUnit.isStrictlyPositive
    (CFC.abs_nonneg F.relativeVielbein)

/-- Primitive finite frame-deformation surprisal `K = -log |E|`. -/
def deformationSurprisalOperator (F : FramePair (n := n)) : Mat :=
  -CFC.log F.polarVolumeOperator

/-- The finite deformation surprisal is self-adjoint. -/
theorem deformationSurprisalOperator_isSelfAdjoint
    (F : FramePair (n := n)) :
    IsSelfAdjoint F.deformationSurprisalOperator := by
  exact IsSelfAdjoint.log.neg

/-- Exponentiating the negative surprisal recovers the polar distortion. -/
theorem exp_neg_deformationSurprisalOperator
    (F : FramePair (n := n)) :
    NormedSpace.exp (-F.deformationSurprisalOperator) =
      F.polarVolumeOperator := by
  rw [deformationSurprisalOperator, neg_neg]
  exact CFC.exp_log F.polarVolumeOperator
    F.polarVolumeOperator_isStrictlyPositive

end FramePair

/--
For every strictly positive complex matrix, the real trace of its CFC
logarithm is the logarithm of the norm of its determinant.
-/
theorem trace_log_eq_log_norm_det_of_isStrictlyPositive
    (A : Mat) (hA : IsStrictlyPositive A) :
    (Matrix.trace (CFC.log A)).re = Real.log ‖A.det‖ := by
  have hexp : NormedSpace.exp (CFC.log A) = A :=
    CFC.exp_log A hA
  have hdet :
      A.det = NormedSpace.exp (Matrix.trace (CFC.log A)) := by
    calc
      A.det = (NormedSpace.exp (CFC.log A)).det :=
        congrArg Matrix.det hexp.symm
      _ = NormedSpace.exp (Matrix.trace (CFC.log A)) :=
        Matrix.det_exp_eq_exp_trace (CFC.log A)
  calc
    (Matrix.trace (CFC.log A)).re
        = Real.log (Real.exp (Matrix.trace (CFC.log A)).re) := by
            rw [Real.log_exp]
    _ = Real.log ‖NormedSpace.exp (Matrix.trace (CFC.log A))‖ := by
          rw [← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
    _ = Real.log ‖A.det‖ := by rw [← hdet]

/-- The polar distortion and the original relative frame have equal determinant norm. -/
theorem norm_det_polarVolumeOperator
    (F : FramePair (n := n)) :
    ‖F.polarVolumeOperator.det‖ = ‖F.relativeVielbein.det‖ := by
  have hdet :
      F.polarVolumeOperator.det * F.polarVolumeOperator.det =
        star F.relativeVielbein.det * F.relativeVielbein.det := by
    have hstar :
        (star F.relativeVielbein).det = star F.relativeVielbein.det := by
      change F.relativeVielbein.conjTranspose.det =
        star F.relativeVielbein.det
      exact Matrix.det_conjTranspose F.relativeVielbein
    calc
      F.polarVolumeOperator.det * F.polarVolumeOperator.det =
          (F.polarVolumeOperator * F.polarVolumeOperator).det := by
            rw [Matrix.det_mul]
      _ = (star F.relativeVielbein * F.relativeVielbein).det := by
            rw [F.polarVolumeOperator_sq]
      _ = star F.relativeVielbein.det * F.relativeVielbein.det := by
            rw [Matrix.det_mul, hstar]
  have hnorm := congrArg norm hdet
  rw [norm_mul, norm_mul, norm_star] at hnorm
  nlinarith [norm_nonneg F.polarVolumeOperator.det,
    norm_nonneg F.relativeVielbein.det]

/-- Trace readout of `K = -log |E|` through the polar determinant. -/
theorem trace_deformationSurprisalOperator_eq_neg_log_norm_det_polar
    (F : FramePair (n := n)) :
    (Matrix.trace F.deformationSurprisalOperator).re =
      -Real.log ‖F.polarVolumeOperator.det‖ := by
  rw [FramePair.deformationSurprisalOperator, Matrix.trace_neg,
    Complex.neg_re]
  exact congrArg Neg.neg
    (trace_log_eq_log_norm_det_of_isStrictlyPositive
      F.polarVolumeOperator F.polarVolumeOperator_isStrictlyPositive)

/-- Total finite deformation surprisal is the negative log-volume of the relative frame. -/
theorem trace_deformationSurprisalOperator
    (F : FramePair (n := n)) :
    (Matrix.trace F.deformationSurprisalOperator).re =
      -Real.log ‖F.relativeVielbein.det‖ := by
  rw [trace_deformationSurprisalOperator_eq_neg_log_norm_det_polar,
    norm_det_polarVolumeOperator]

end InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy
