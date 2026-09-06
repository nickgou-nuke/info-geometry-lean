import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Canonical.ZornOperatorGradeReversalContract
import InfoGeometry.Physics.OperatorZornMatrixAlgebra
import InfoGeometry.Physics.OperatorZornSoldering

/-!
# Two four-operator vectors in the Zorn carrier

A classical Zorn split-octonion coordinate has two four-dimensional Peirce
halves

`(a,u) | (v,b)`, with `a,b` scalar and `u,v` three-vectors.

This file lifts that coordinate statement to an arbitrary operator ring `A`.
It keeps two products separate:

* `toNativeZorn` lands in the non-associative operator-valued Zorn calculus;
* `toAssociativeZorn` first solders each three-operator rail to one operator
  and then lands in the transported ordinary `2 x 2` matrix algebra.

For noncommuting coefficients, `operatorCross U U` is generally nonzero, so
nilpotency of a native chiral rail is a theorem under a commutation condition,
not a formal consequence of the scalar split-octonion mnemonic.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn

open InfoGeometry.Canonical

variable {A : Type*} [Ring A]

/-- One operator-valued four-vector in scalar-plus-three-vector form. -/
@[ext]
structure FourOperatorVector (A : Type*) [Ring A] where
  scalar : A
  spatial : Fin 3 -> A

/-- The two four-operator-vector halves of a Zorn coordinate. -/
@[ext]
structure TwinFourOperatorVector (A : Type*) [Ring A] where
  plus : FourOperatorVector A
  minus : FourOperatorVector A

/-- Zero four-operator vector. -/
def zeroFour : FourOperatorVector A :=
  ⟨0, fun _ => 0⟩

/-- Addition used to state the Peirce reconstruction without installing a
second algebra structure. -/
def addFour (x y : FourOperatorVector A) : FourOperatorVector A :=
  ⟨x.scalar + y.scalar, x.spatial + y.spatial⟩

/-- Negation used by the Cartan grading. -/
def negFour (x : FourOperatorVector A) : FourOperatorVector A :=
  ⟨-x.scalar, -x.spatial⟩

/-- Componentwise addition of twin four-vectors. -/
def addTwin (x y : TwinFourOperatorVector A) : TwinFourOperatorVector A :=
  ⟨addFour x.plus y.plus, addFour x.minus y.minus⟩

/-- Componentwise negation of twin four-vectors. -/
def negTwin (x : TwinFourOperatorVector A) : TwinFourOperatorVector A :=
  ⟨negFour x.plus, negFour x.minus⟩

/-- Native non-associative operator-Zorn coordinate. -/
def toNativeZorn (x : TwinFourOperatorVector A) :
    InfoGeometry.Canonical.OperatorZornMatrix A :=
  operatorZornCoordinates
    x.plus.scalar x.minus.scalar x.plus.spatial x.minus.spatial

/-- Recover the two four-vector halves from a native operator-Zorn element. -/
def ofNativeZorn (z : InfoGeometry.Canonical.OperatorZornMatrix A) :
    TwinFourOperatorVector A :=
  ⟨⟨z.n_plus, z.sigma_plus⟩, ⟨z.n_minus, z.sigma_minus⟩⟩

/-- The `4+4` presentation is exactly equivalent to the native four-field
operator-Zorn carrier. -/
def equivNativeZorn :
    TwinFourOperatorVector A ≃ InfoGeometry.Canonical.OperatorZornMatrix A where
  toFun := toNativeZorn
  invFun := ofNativeZorn
  left_inv x := by
    cases x with
    | mk p m =>
      cases p
      cases m
      rfl
  right_inv z := by
    cases z
    rfl

@[simp] theorem ofNativeZorn_toNativeZorn
    (x : TwinFourOperatorVector A) :
    ofNativeZorn (toNativeZorn x) = x :=
  (equivNativeZorn (A := A)).left_inv x

@[simp] theorem toNativeZorn_ofNativeZorn
    (z : InfoGeometry.Canonical.OperatorZornMatrix A) :
    toNativeZorn (ofNativeZorn z) = z :=
  (equivNativeZorn (A := A)).right_inv z

/-- Positive Peirce half: retain `(a,u)` and erase `(v,b)`. -/
def plusPeirce (x : TwinFourOperatorVector A) : TwinFourOperatorVector A :=
  ⟨x.plus, zeroFour⟩

/-- Negative Peirce half: retain `(v,b)` and erase `(a,u)`. -/
def minusPeirce (x : TwinFourOperatorVector A) : TwinFourOperatorVector A :=
  ⟨zeroFour, x.minus⟩

/-- Exact reconstruction from the two four-dimensional Peirce halves. -/
theorem plusPeirce_add_minusPeirce
    (x : TwinFourOperatorVector A) :
    addTwin (plusPeirce x) (minusPeirce x) = x := by
  ext i <;> simp [addTwin, addFour, plusPeirce, minusPeirce, zeroFour]

/-- Exchange the two four-operator-vector sheets. -/
def sheetFlip (x : TwinFourOperatorVector A) : TwinFourOperatorVector A :=
  ⟨x.minus, x.plus⟩

@[simp] theorem sheetFlip_involutive
    (x : TwinFourOperatorVector A) :
    sheetFlip (sheetFlip x) = x := by
  cases x
  rfl

/-- The `4+4` sheet flip is exactly the already-owned native Zorn flip. -/
@[simp] theorem toNativeZorn_sheetFlip
    (x : TwinFourOperatorVector A) :
    toNativeZorn (sheetFlip x) = zornFlipOperator (toNativeZorn x) := by
  rfl

/-- Cartan involution: diagonal scalar coordinates are even and both
three-operator rails are odd. -/
def cartanInvolution (x : TwinFourOperatorVector A) :
    TwinFourOperatorVector A :=
  ⟨⟨x.plus.scalar, -x.plus.spatial⟩,
    ⟨x.minus.scalar, -x.minus.spatial⟩⟩

@[simp] theorem cartanInvolution_involutive
    (x : TwinFourOperatorVector A) :
    cartanInvolution (cartanInvolution x) = x := by
  ext i <;> simp [cartanInvolution]

/-- Diagonal/even part. -/
def diagonalPart (x : TwinFourOperatorVector A) :
    TwinFourOperatorVector A :=
  ⟨⟨x.plus.scalar, fun _ => 0⟩,
    ⟨x.minus.scalar, fun _ => 0⟩⟩

/-- Off-diagonal/odd part. -/
def offDiagonalPart (x : TwinFourOperatorVector A) :
    TwinFourOperatorVector A :=
  ⟨⟨0, x.plus.spatial⟩, ⟨0, x.minus.spatial⟩⟩

/-- Exact Cartan decomposition into diagonal and off-diagonal sectors. -/
theorem diagonal_add_offDiagonal
    (x : TwinFourOperatorVector A) :
    addTwin (diagonalPart x) (offDiagonalPart x) = x := by
  ext i <;> simp [addTwin, addFour, diagonalPart, offDiagonalPart]

@[simp] theorem cartanInvolution_diagonalPart
    (x : TwinFourOperatorVector A) :
    cartanInvolution (diagonalPart x) = diagonalPart x := by
  ext i <;> simp [cartanInvolution, diagonalPart]

@[simp] theorem cartanInvolution_offDiagonalPart
    (x : TwinFourOperatorVector A) :
    cartanInvolution (offDiagonalPart x) =
      negTwin (offDiagonalPart x) := by
  ext i <;> simp [cartanInvolution, offDiagonalPart, negTwin, negFour]

/-- Pure off-diagonal twin vector. -/
def pureOffDiagonal
    (u v : Fin 3 -> A) : TwinFourOperatorVector A :=
  ⟨⟨0, u⟩, ⟨0, v⟩⟩

@[simp] theorem toNativeZorn_pureOffDiagonal
    (u v : Fin 3 -> A) :
    toNativeZorn (pureOffDiagonal u v) = chiralOperatorZorn u v := by
  rfl

/-- Exact square of a fully noncommutative chiral Zorn coordinate.  The two
self-cross terms are the obstruction to a scalar-octonion-style diagonal
square. -/
theorem native_pureOffDiagonal_square
    (u v : Fin 3 -> A) :
    operatorZornMul (toNativeZorn (pureOffDiagonal u v))
        (toNativeZorn (pureOffDiagonal u v)) =
      operatorZornCoordinates
        (operatorDot u v)
        (operatorDot v u)
        (-operatorCross v v)
        (operatorCross u u) := by
  exact operatorZornMul_chiralOperatorZorn u v

/-- A native upper chiral rail squares into the opposite rail through its
operator commutator cross product. -/
theorem native_upper_square (u : Fin 3 -> A) :
    operatorZornMul (sigmaPlus u) (sigmaPlus u) =
      sigmaMinus (operatorCross u u) := by
  exact sigmaPlus_mul_sigmaPlus u u

/-- A native lower chiral rail has the dual square. -/
theorem native_lower_square (v : Fin 3 -> A) :
    operatorZornMul (sigmaMinus v) (sigmaMinus v) =
      sigmaPlus (-operatorCross v v) := by
  exact sigmaMinus_mul_sigmaMinus v v

/-- Native upper nilpotency follows exactly when its three operator
components commute pairwise. -/
theorem native_upper_square_zero_of_pairwise_commute
    (u : Fin 3 -> A)
    (h12 : u 1 * u 2 = u 2 * u 1)
    (h20 : u 2 * u 0 = u 0 * u 2)
    (h01 : u 0 * u 1 = u 1 * u 0) :
    operatorZornMul (sigmaPlus u) (sigmaPlus u) = 0 := by
  have hcross : operatorCross u u = 0 :=
    (operatorCross_self_eq_zero_iff u).2 ⟨h12, h20, h01⟩
  rw [native_upper_square, hcross]
  rfl

/-- Native lower nilpotency follows under the same pairwise-commutation
criterion. -/
theorem native_lower_square_zero_of_pairwise_commute
    (v : Fin 3 -> A)
    (h12 : v 1 * v 2 = v 2 * v 1)
    (h20 : v 2 * v 0 = v 0 * v 2)
    (h01 : v 0 * v 1 = v 1 * v 0) :
    operatorZornMul (sigmaMinus v) (sigmaMinus v) = 0 := by
  have hcross : operatorCross v v = 0 :=
    (operatorCross_self_eq_zero_iff v).2 ⟨h12, h20, h01⟩
  rw [native_lower_square, hcross]
  rfl

section AssociativeSoldering

variable [StarRing A]

/-- Solder the two spatial rails to two operator entries and retain both
scalar operators on the diagonal. -/
def toAssociativeZorn
    (S : InfoGeometry.Physics.ChiralSigmaSoldering A A)
    (x : TwinFourOperatorVector A) :
    InfoGeometry.Physics.OperatorZornMatrix A where
  n_plus_op := x.plus.scalar
  n_minus_op := x.minus.scalar
  sigma_plus_op := S.plus x.plus.spatial
  sigma_minus_op := S.minus x.minus.spatial

/-- Matrix display of the soldered associative shell. -/
theorem toAssociativeZorn_toMatrix
    (S : InfoGeometry.Physics.ChiralSigmaSoldering A A)
    (x : TwinFourOperatorVector A) :
    InfoGeometry.Physics.OperatorZornMatrix.toMatrix
        (toAssociativeZorn S x) =
      !![x.plus.scalar, S.plus x.plus.spatial;
         S.minus x.minus.spatial, x.minus.scalar] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end AssociativeSoldering

end InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
