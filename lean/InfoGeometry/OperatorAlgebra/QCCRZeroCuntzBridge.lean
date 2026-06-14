import InfoGeometry.OperatorAlgebra.QCCRCore
import InfoGeometry.Canonical.CuntzUHFAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra.QCCRZeroCuntzBridge

open InfoGeometry.OperatorAlgebra.QCCRCore
open InfoGeometry.Canonical.CuntzUHFAlgebra

/-!
# QCCR-Cuntz bridge at q = 0

At q = 0, the q-CCR algebra collapses to the Cuntz–Toeplitz isometry
relations, matching the Cuntz UHF algebra structure.
-/

/-- At q = 0, the generators are Cuntz–Toeplitz isometries. -/
theorem q_zero_is_cuntz_isometry {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op] [Algebra ℝ Op]
    (A : QCCRAlgebra N Op) (hq0 : A.q = 0) (i j : Fin N) :
    star (A.a i) * (A.a j) = if i = j then (1 : Op) else 0 :=
  QCCRAlgebra.q_zero_is_cuntz N Op A hq0 i j

end InfoGeometry.OperatorAlgebra.QCCRZeroCuntzBridge
