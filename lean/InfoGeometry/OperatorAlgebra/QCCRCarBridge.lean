import InfoGeometry.OperatorAlgebra.QCCRSupergrading
import Mathlib

noncomputable section

namespace QCCRCarBridge

open InfoGeometry.OperatorAlgebra.QCCRCore
open InfoGeometry.OperatorAlgebra.QCCRSupergrading

/-!
# QCCR-CAR bridge

Connects the q-CCR algebra to the CAR (Clifford) algebra at q = -1.
-/

/--
At q = -1, the q-superbracket is the anticommutator and the algebra
satisfies the CAR (canonical anticommutation relations) of the Clifford
algebra Cl(0, N).
-/
theorem q_neg_one_is_clifford_car {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op] [Algebra ℝ Op]
    (A : QCCRAlgebra N Op) (hq_neg1 : A.q = -1) (i j : Fin N) :
    star (A.a i) * (A.a j) + (A.a j) * star (A.a i) = if i = j then (1 : Op) else 0 :=
  QCCRAlgebra.q_neg_one_is_car N Op A hq_neg1 i j

end QCCRCarBridge
