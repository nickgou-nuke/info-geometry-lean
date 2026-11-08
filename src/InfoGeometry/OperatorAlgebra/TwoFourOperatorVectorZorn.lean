import InfoGeometry.Physics.OperatorZornMatrixAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-! The `4+4` coordinate presentation of the existing associative Zorn shell. -/
namespace InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix
open InfoGeometry.Canonical

variable {A : Type*} [Ring A] [StarRing A]

structure FourOperatorVector where
  scalar : A
  spatial : OperatorVector A

structure TwinFourOperatorVector where
  plus : FourOperatorVector (A := A)
  minus : FourOperatorVector (A := A)

def toZorn (x : TwinFourOperatorVector (A := A)) : InfoGeometry.Canonical.OperatorZornMatrix A :=
  InfoGeometry.Canonical.operatorZornCoordinates x.plus.scalar x.minus.scalar
    x.plus.spatial x.minus.spatial

def ofZorn (z : InfoGeometry.Canonical.OperatorZornMatrix A) : TwinFourOperatorVector (A := A) :=
  ⟨⟨z.n_plus, z.sigma_plus⟩,
   ⟨z.n_minus, z.sigma_minus⟩⟩

@[simp] theorem ofZorn_toZorn (x : TwinFourOperatorVector (A := A)) :
    ofZorn (toZorn x) = x := by
  cases x
  rfl

@[simp] theorem toZorn_ofZorn (z : InfoGeometry.Canonical.OperatorZornMatrix A) :
    toZorn (ofZorn z) = z := by
  cases z
  rfl

def addFour (x y : FourOperatorVector (A := A)) : FourOperatorVector (A := A) :=
  ⟨x.scalar + y.scalar, x.spatial + y.spatial⟩

def plusPart (x : TwinFourOperatorVector (A := A)) : TwinFourOperatorVector (A := A) :=
  ⟨x.plus, ⟨0, 0⟩⟩

def minusPart (x : TwinFourOperatorVector (A := A)) : TwinFourOperatorVector (A := A) :=
  ⟨⟨0, 0⟩, x.minus⟩

theorem plusPart_add_minusPart (x : TwinFourOperatorVector (A := A)) :
    (plusPart x).plus.scalar + (minusPart x).plus.scalar = x.plus.scalar ∧
    (plusPart x).minus.scalar + (minusPart x).minus.scalar = x.minus.scalar := by
  simp [plusPart, minusPart]

def sheetFlip (x : TwinFourOperatorVector (A := A)) : TwinFourOperatorVector (A := A) :=
  ⟨x.minus, x.plus⟩

@[simp] theorem sheetFlip_involutive (x : TwinFourOperatorVector (A := A)) :
    sheetFlip (sheetFlip x) = x := by
  cases x
  rfl

theorem toZorn_sheetFlip (x : TwinFourOperatorVector (A := A)) :
    (toZorn (sheetFlip x)).n_plus = (toZorn x).n_minus ∧
    (toZorn (sheetFlip x)).n_minus = (toZorn x).n_plus := by
  cases x
  constructor <;> rfl

end InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
