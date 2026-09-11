import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Eight-coordinate chiral operator packet

The packet records the two diagonal null channels and the two three-component
chiral rails.  It is a carrier/readout owner only: no parity assignment and no
superbracket closure is inferred from the coordinate shape.
-/

namespace InfoGeometry.Algebra.ZornChiralOperatorPacket

open InfoGeometry.Algebra

variable {A : Type*}

structure ChiralOperatorData where
  uPlusOp : A
  uMinusOp : A
  sigmaPlus : Fin 3 → A
  sigmaMinus : Fin 3 → A

def coordinate (Q : ChiralOperatorData (A := A)) : Fin 8 → A
  | 0 => Q.uPlusOp
  | 1 => Q.uMinusOp
  | 2 => Q.sigmaPlus 0
  | 3 => Q.sigmaPlus 1
  | 4 => Q.sigmaPlus 2
  | 5 => Q.sigmaMinus 0
  | 6 => Q.sigmaMinus 1
  | 7 => Q.sigmaMinus 2

@[simp] theorem coordinate_zero (Q : ChiralOperatorData (A := A)) :
    coordinate Q 0 = Q.uPlusOp := rfl

@[simp] theorem coordinate_one (Q : ChiralOperatorData (A := A)) :
    coordinate Q 1 = Q.uMinusOp := rfl

theorem coordinate_injective :
    Function.Injective (coordinate (A := A)) := by
  intro Q R h
  cases Q with
  | mk qplus qminus qσplus qσminus =>
    cases R with
    | mk rplus rminus rσplus rσminus =>
      congr
      · exact congrFun h 0
      · exact congrFun h 1
      · funext i
        fin_cases i
        · exact congrFun h 2
        · exact congrFun h 3
        · exact congrFun h 4
      · funext i
        fin_cases i
        · exact congrFun h 5
        · exact congrFun h 6
        · exact congrFun h 7

def toZornMatrix [CommRing A] (Q : ChiralOperatorData (A := A)) : ZornMatrix A where
  a := Q.uPlusOp
  v := Q.sigmaPlus
  w := Q.sigmaMinus
  b := Q.uMinusOp

@[simp] theorem toZornMatrix_a [CommRing A] (Q : ChiralOperatorData (A := A)) :
    (toZornMatrix Q).a = Q.uPlusOp := rfl

@[simp] theorem toZornMatrix_b [CommRing A] (Q : ChiralOperatorData (A := A)) :
    (toZornMatrix Q).b = Q.uMinusOp := rfl

@[simp] theorem toZornMatrix_v [CommRing A] (Q : ChiralOperatorData (A := A)) :
    (toZornMatrix Q).v = Q.sigmaPlus := rfl

@[simp] theorem toZornMatrix_w [CommRing A] (Q : ChiralOperatorData (A := A)) :
    (toZornMatrix Q).w = Q.sigmaMinus := rfl

end InfoGeometry.Algebra.ZornChiralOperatorPacket
