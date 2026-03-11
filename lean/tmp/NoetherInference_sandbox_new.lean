import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.DoubledAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint

open InfoGeometry.Krein

namespace InfoGeometry.Krein.NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def neutralityEquiv : KreinEquiv (DoubledSpace E) (NeutralSpace E) :=
  (rotation45KreinEquiv (E := E)).symm.toKreinEquiv.trans (rotation45KreinEquiv (E := E)).toKreinEquiv

noncomputable def neutralLift (A : DoubledSpace E →L[ℝ] DoubledSpace E) : NeutralSpace E →L[ℝ] NeutralSpace E :=
  (neutralityEquiv.conjContinuousLinearEquiv : _).toContinuousLinearMap.conj A

lemma neutralLift_kreinAdjoint (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    neutralLift (Krein.doubledKreinAdjoint A) = KreinSpace.kreinAdjoint (neutralLift A) := by
  have h := (neutralityEquiv.conjKreinEquiv : _).symm
  simp [neutralLift, KreinSpace.kreinAdjoint, h]

end InfoGeometry.Krein.NeutralSpace
