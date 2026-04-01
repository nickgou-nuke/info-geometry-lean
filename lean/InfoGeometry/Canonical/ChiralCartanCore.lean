import InfoGeometry.Canonical.ConformalUnification

namespace InfoGeometry.Canonical.ChiralCartanCore

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def chiralGrading (CI : ConformalInference E) : E →L[ℝ] E :=
  let P_R := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
  let P_L := IsMoorePenroseInverse.leftProjector CI.A CI.A_MP
  P_R - P_L

def IsCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = chiralGrading CI * X

def IsNonCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = - (chiralGrading CI * X)

end InfoGeometry.Canonical.ChiralCartanCore
