import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CertifiedInverseKernel

namespace InfoGeometry.Canonical.ChiralCartanCore

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def chiralGrading (CI : ConformalInference E) : E →L[ℝ] E :=
  let P_R := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
  let P_L := IsMoorePenroseInverse.leftProjector CI.A CI.A_MP
  P_R - P_L

/-- The chiral grading is exactly twice the certified inverse-kernel dilation gap. -/
theorem chiralGrading_eq_two_smul_dilationGap (CI : ConformalInference E) :
    chiralGrading CI =
      (2 : ℝ) •
        (InverseKernel.dilationGap
          { A := CI.A, A_D := CI.A_D, A_MP := CI.A_MP }) := by
  ext x
  simp [chiralGrading, InverseKernel.dilationGap]

def IsCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = chiralGrading CI * X

def IsNonCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = - (chiralGrading CI * X)

end InfoGeometry.Canonical.ChiralCartanCore
