import InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Weyl soldering for the existing operator-valued four-vector carrier.
The result is a matrix-valued coordinate map; no Lorentz representation or
commutative determinant is inferred for a general coefficient ring. -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn

open InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) A

def imagUnit : A := algebraMap ℂ A Complex.I

def lightPlus (x : FourOperatorVector (A := A)) : A := x.scalar + x.spatial 2
def lightMinus (x : FourOperatorVector (A := A)) : A := x.scalar - x.spatial 2

def transversePlus (x : FourOperatorVector (A := A)) : A :=
  x.spatial 0 - imagUnit * x.spatial 1

def transverseMinus (x : FourOperatorVector (A := A)) : A :=
  x.spatial 0 + imagUnit * x.spatial 1

def weylSoldering (x : FourOperatorVector (A := A)) : Matrix2 (A := A) :=
  !![lightPlus x, transversePlus x; transverseMinus x, lightMinus x]

theorem weylSoldering_apply (x : FourOperatorVector (A := A)) :
    weylSoldering x =
      !![lightPlus x, transversePlus x; transverseMinus x, lightMinus x] := rfl

theorem weylSoldering_coordinates (x : FourOperatorVector (A := A)) :
    (weylSoldering x) 0 0 = lightPlus x ∧
    (weylSoldering x) 1 1 = lightMinus x ∧
    (weylSoldering x) 0 1 = transversePlus x ∧
    (weylSoldering x) 1 0 = transverseMinus x := by
  change (weylSoldering x) 0 0 = _ ∧ _
  simp [weylSoldering]

theorem lightPlus_add_lightMinus (x : FourOperatorVector (A := A)) :
    lightPlus x + lightMinus x = 2 * x.scalar := by
  simp [lightPlus, lightMinus]
  noncomm_ring

end InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn

end
