import InfoGeometry.Lie.SplitOctonionEllNativeClosedFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect
import InfoGeometry.Physics.Algebra.LinearTripotentTrifactor

/-!
# Active/support grading of the native ell flow

This owner separates the signed tripotent grading `T` from the binary
active/defect involution `Gamma = 2 T² - I`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllNativeSupportGrading

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Physics.Algebra

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-- Active support `Q = T²`. -/
def ellActiveSupport : EndCZ := ellGrading * ellGrading

/-- Active/defect involution `Gamma = 2Q - I`. -/
def ellActiveDefectInvolution : EndCZ :=
  (2 : ℝ) • ellActiveSupport - 1

theorem ellActiveSupport_eq_nativeDrazinProjector :
    ellActiveSupport = ellNativeDrazinProjector := rfl

theorem ellActiveSupport_eq_flowPlus_add_flowMinus :
    ellActiveSupport = flowPlus + flowMinus := by
  rw [ellActiveSupport_eq_nativeDrazinProjector]
  exact ellNativeDrazinProjector_eq_flowPlus_add_flowMinus

theorem one_sub_ellActiveSupport_eq_flowZero :
    1 - ellActiveSupport = flowZero := rfl

theorem ellActiveSupport_idempotent :
    ellActiveSupport * ellActiveSupport = ellActiveSupport := by
  have hT : ellGrading * ellGrading * ellGrading = ellGrading := by
    simpa [pow_three] using ellGrading_tripotent
  unfold ellActiveSupport
  calc
    (ellGrading * ellGrading) * (ellGrading * ellGrading) =
        (ellGrading * ellGrading * ellGrading) * ellGrading := by
          simp only [mul_assoc]
    _ = ellGrading * ellGrading := by rw [hT]

/-- `Gamma` is an involution on the complete carrier. -/
theorem ellActiveDefectInvolution_sq :
    ellActiveDefectInvolution * ellActiveDefectInvolution = 1 := by
  unfold ellActiveDefectInvolution
  rw [two_smul]
  noncomm_ring [ellActiveSupport_idempotent]

/-- The positive projector range is exactly the `+1` eigenspace. -/
theorem flowPlus_range_eq_eigenspace :
    LinearMap.range flowPlus = Module.End.eigenspace ellGrading 1 := by
  change LinearMap.range (endProjPos ellGrading) = _
  exact endProjPos_range_eq_eigenspace ellGrading ellGrading_tripotent

/-- The negative projector range is exactly the `-1` eigenspace. -/
theorem flowMinus_range_eq_eigenspace :
    LinearMap.range flowMinus = Module.End.eigenspace ellGrading (-1) := by
  change LinearMap.range (endProjNeg ellGrading) = _
  exact endProjNeg_range_eq_eigenspace ellGrading ellGrading_tripotent

/-- The zero projector range is exactly the Drazin/stationary kernel. -/
theorem flowZero_range_eq_stationary_ker :
    LinearMap.range flowZero = LinearMap.ker ellGrading :=
  flow_zero_range_eq_ker

/-- `Gamma` acts as `-1` on the Drazin defect sector. -/
theorem ellActiveDefectInvolution_on_flowZero (X : CZ) :
    ellActiveDefectInvolution (flowZero X) = -flowZero X := by
  have hQ0 : ellActiveSupport * flowZero = 0 := by
    unfold ellActiveSupport
    rw [mul_assoc, flow_zero_annihilated, mul_zero]
  have h := congrArg (fun F : EndCZ => F X) hQ0
  change ellActiveSupport (flowZero X) = 0 at h
  change (2 : ℝ) • ellActiveSupport (flowZero X) - flowZero X =
    -flowZero X
  rw [h]
  module

/-- `Gamma` acts as `+1` on the full active support. -/
theorem ellActiveDefectInvolution_on_activeSupport (X : CZ) :
    ellActiveDefectInvolution (ellActiveSupport X) =
      ellActiveSupport X := by
  have hQQ := congrArg (fun F : EndCZ => F X) ellActiveSupport_idempotent
  change ellActiveSupport (ellActiveSupport X) = ellActiveSupport X at hQQ
  change (2 : ℝ) • ellActiveSupport (ellActiveSupport X) -
      ellActiveSupport X = ellActiveSupport X
  rw [hQQ]
  module

end InfoGeometry.Lie.SplitOctonionEllNativeSupportGrading
