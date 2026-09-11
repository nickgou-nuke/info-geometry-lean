import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# InfoGeometry.KK.RealSplitKreinCompactOperator

Concrete compact-operator bridge lemmas for the primitive bounded real
split-Krein cycle.
-/

namespace InfoGeometry.KK

open InfoGeometry.Krein

open scoped InnerProductSpace

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

lemma superComm_eps_isCompactOperator
    (X : RealSplitKreinKasparovCycle A B H) :
    IsCompactOperator
      ((KreinGradedModule.superComm (H := H) X.F X.cl11.eps) : H → H) := by
  simpa [IsCompactEnd] using X.superComm_eps_compact

lemma superComm_J_isCompactOperator
    (X : RealSplitKreinKasparovCycle A B H) :
    IsCompactOperator
      ((KreinGradedModule.superComm (H := H) X.F X.cl11.J) : H → H) := by
  simpa [IsCompactEnd] using X.superComm_J_compact

lemma superComm_pi_isCompactOperator
    (X : RealSplitKreinKasparovCycle A B H) (a : A) :
    IsCompactOperator
      ((KreinGradedModule.superComm (H := H) X.F (X.π a)) : H → H) := by
  simpa [IsCompactEnd] using X.superComm_pi_compact a

lemma comm_isCompactOperator
    (X : RealSplitKreinKasparovCycle A B H) (a : A) :
    IsCompactOperator ((X.F * X.π a - X.π a * X.F : H →L[ℝ] H) : H → H) := by
  simpa [IsCompactEnd] using X.comm_compact a

end InfoGeometry.KK
