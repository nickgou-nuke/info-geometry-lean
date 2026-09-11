import InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Sl2EndpointCompensation

noncomputable section

/-!
# Concrete `sl₂` endpoint bridge in the Cuntz matrix-unit sector

The ambient carrier is `CuntzAlg 3`; this is a bracket calculation in its
native matrix-unit subspace, not an asserted embedding of all `Mat₂(ℝ)`.
-/

namespace InfoGeometry.Algebra.CuntzSl2EndpointBridge

open InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzMatrixUnits

noncomputable section

abbrev Cuntz3 := CuntzAlg 3

def ePlusC : Cuntz3 := hop 0 1
def eMinusC : Cuntz3 := hop 1 0
def hCartanC : Cuntz3 := hop 0 0 - hop 1 1

theorem ePlusC_sq : ePlusC * ePlusC = 0 := by
  change E 3 0 1 * E 3 0 1 = 0
  exact matrix_unit_sq_off_diag 3 0 1 (by decide)

theorem eMinusC_sq : eMinusC * eMinusC = 0 := by
  change E 3 1 0 * E 3 1 0 = 0
  exact matrix_unit_sq_off_diag 3 1 0 (by decide)

theorem endpoint_compensation_cuntz :
    CuntzMatrixUnitFiveGradingBridge.commutator ePlusC eMinusC = hCartanC := by
  rw [CuntzMatrixUnitFiveGradingBridge.commutator, ePlusC, eMinusC, hCartanC]
  change E 3 0 1 * E 3 1 0 - E 3 1 0 * E 3 0 1 =
    E 3 0 0 - E 3 1 1
  rw [matrix_unit_mul, matrix_unit_mul]
  simp

end
end InfoGeometry.Algebra.CuntzSl2EndpointBridge
