import InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.OperatorAlgebra.ModularTwinZornRepresentation
import InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn
import InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation
import InfoGeometry.OperatorAlgebra.TwoBoundaryWeakValueZorn
import InfoGeometry.Quantum.ComplexKramersAntiunitary

/-! Verified capstone packet for the current operator-Zorn owners.  Historical
SL₂C and Krein-module layers remain separate because their old APIs are absent. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.OperatorZornTwinFormalism

open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
open InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation
open InfoGeometry.Quantum.ComplexKramersAntiunitary

variable {A : Type*} [Ring A] [StarRing A]

def fourPlusFourToNative (x : TwinFourOperatorVector (A := A)) := toZorn x

theorem fourPlusFour_roundtrip (x : TwinFourOperatorVector (A := A)) :
    ofZorn (fourPlusFourToNative x) = x := ofZorn_toZorn x

theorem native_self_cross_obstruction (u : Fin 3 → A) :
    operatorCross u u = 0 ↔
      u 1 * u 2 = u 2 * u 1 ∧ u 2 * u 0 = u 0 * u 2 ∧
        u 0 * u 1 = u 1 * u 0 :=
  operatorCross_self_eq_zero_iff u

section Associative
variable [StarRing A]

theorem associative_peirce_packet :
    ePlus (A := A) * ePlus = ePlus ∧
      eMinus (A := A) * eMinus = eMinus ∧
      ePlus (A := A) * eMinus = 0 ∧
      eMinus (A := A) * ePlus = 0 ∧
      grading (A := A) * grading = 1 ∧
      sheetExchange (A := A) * sheetExchange = 1 := by
  exact ⟨ePlus_sq, eMinus_sq, ePlus_mul_eMinus, eMinus_mul_ePlus,
    grading_sq, sheetExchange_sq⟩

theorem kramers_square_minus_one (v : H2) :
    timeReversal (timeReversal v) = -v := timeReversal_sq v

end Associative
end InfoGeometry.OperatorAlgebra.OperatorZornTwinFormalism
