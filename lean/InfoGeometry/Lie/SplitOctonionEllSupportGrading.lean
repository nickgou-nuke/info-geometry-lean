import InfoGeometry.Lie.SplitOctonionEllNativeClosedFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect
import InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
import InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
import InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
import InfoGeometry.Lie.SplitOctonionEllPolarization
import InfoGeometry.Physics.Algebra.LinearTripotentTrifactor

/-!
# Active-support grading of the native split-octonion ell flow

For the concrete off-diagonal `lUnit` operator `T = ellGrading`, this owner
separates the signed tripotent grading from the active/defect involution:

* `T` has weights `-1, 0, +1`;
* `Q = T²` is the native Drazin support;
* `Γ = 2Q - I` distinguishes active and stationary/defect sectors.

It also specializes the reusable endomorphism-level trifactor theorems to
identify the ranges of `P₊` and `P₋` with the actual eigenspaces of `T`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllSupportGrading

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllNativeClosedFlow
open InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect
open InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Physics.Algebra
open InfoGeometry.Singular.Drazin

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-- The active-support operator `Qₗ = Tₗ²`. -/
def ellActiveSupport : EndCZ := ellGrading * ellGrading

/-- The active/defect involution `Γₗ = 2Tₗ² - I`. -/
def ellActiveDefectInvolution : EndCZ :=
  (2 : ℝ) • ellActiveSupport - 1

/-- The active support is exactly the native Drazin projector. -/
theorem ellActiveSupport_eq_drazinProjector :
    ellActiveSupport =
      Drazin_Projector ellGrading ellGrading 1
        ellGrading_isDrazinInverse := by
  rfl

/-- The active support is the sum of the positive and negative trifactor
projectors used by the closed flow. -/
theorem ellActiveSupport_eq_flowPlus_add_flowMinus :
    ellActiveSupport = flowPlus + flowMinus := by
  unfold ellActiveSupport flowPlus flowMinus
  exact (projPos_add_projNeg (T := ellGrading)).symm

/-- The complement of active support is precisely the stationary projector. -/
theorem one_sub_ellActiveSupport_eq_flowZero :
    1 - ellActiveSupport = flowZero := by
  rfl

/-- `Qₗ` is a genuine projector. -/
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

/-- The range of the positive closed-flow projector is exactly the `+1`
eigenspace of the native ell grading. -/
theorem flowPlus_range_eq_eigenspace :
    LinearMap.range flowPlus = Module.End.eigenspace ellGrading 1 := by
  have hEq : flowPlus = endProjPos ellGrading := by rfl
  rw [hEq]
  exact endProjPos_range_eq_eigenspace ellGrading ellGrading_tripotent

/-- The range of the negative closed-flow projector is exactly the `-1`
eigenspace of the native ell grading. -/
theorem flowMinus_range_eq_eigenspace :
    LinearMap.range flowMinus = Module.End.eigenspace ellGrading (-1) := by
  have hEq : flowMinus = endProjNeg ellGrading := by rfl
  rw [hEq]
  exact endProjNeg_range_eq_eigenspace ellGrading ellGrading_tripotent

/-- The active/defect grading is an involution on the full canonical carrier. -/
theorem ellActiveDefectInvolution_sq :
    ellActiveDefectInvolution * ellActiveDefectInvolution = 1 := by
  unfold ellActiveDefectInvolution
  rw [two_smul]
  noncomm_ring [ellActiveSupport_idempotent]

/-- `Γₗ` acts by `-1` on the stationary/Drazin-defect sector. -/
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

/-- `Γₗ` acts by `+1` on the positive active sector. -/
theorem ellActiveDefectInvolution_on_flowPlus (X : CZ) :
    ellActiveDefectInvolution (flowPlus X) = flowPlus X := by
  have hT : ellGrading * ellGrading * ellGrading = ellGrading := by
    simpa [pow_three] using ellGrading_tripotent
  have hQp : ellActiveSupport * flowPlus = flowPlus := by
    unfold ellActiveSupport flowPlus
    change (ellGrading * ellGrading) * projPos ellGrading =
      projPos ellGrading
    rw [mul_assoc, mul_projPos hT, mul_projPos hT]
  have h := congrArg (fun F : EndCZ => F X) hQp
  change ellActiveSupport (flowPlus X) = flowPlus X at h
  change (2 : ℝ) • ellActiveSupport (flowPlus X) - flowPlus X =
    flowPlus X
  rw [h]
  module

/-- `Γₗ` acts by `+1` on the negative active sector. -/
theorem ellActiveDefectInvolution_on_flowMinus (X : CZ) :
    ellActiveDefectInvolution (flowMinus X) = flowMinus X := by
  have hT : ellGrading * ellGrading * ellGrading = ellGrading := by
    simpa [pow_three] using ellGrading_tripotent
  have hQm : ellActiveSupport * flowMinus = flowMinus := by
    unfold ellActiveSupport flowMinus
    change (ellGrading * ellGrading) * projNeg ellGrading =
      projNeg ellGrading
    rw [mul_assoc, mul_projNeg hT, mul_neg, mul_projNeg hT, neg_neg]
  have h := congrArg (fun F : EndCZ => F X) hQm
  change ellActiveSupport (flowMinus X) = flowMinus X at h
  change (2 : ℝ) • ellActiveSupport (flowMinus X) - flowMinus X =
    flowMinus X
  rw [h]
  module

end InfoGeometry.Lie.SplitOctonionEllSupportGrading
