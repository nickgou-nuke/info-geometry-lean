import InfoGeometry.Physics.NCG.NoncommutativeChiralZornAlgebra
import InfoGeometry.Physics.Octonion.ChiralZornAlgebra
import InfoGeometry.Canonical.ChiralZornCasimirChannels

/-!
# Native bridge for the eight-slot chiral Zorn carrier

`ChiralZornMatrix A` and `NCZornElement A` have the same eight slots:
two diagonal coefficients and two three-component chiral vectors.  The
coefficient type is left arbitrary, so it may be a matrix algebra such as
`Matrix (Fin 2) (Fin 2) ℂ`.

This is only a coordinate/product bridge.  It does not identify this carrier
with the scalar canonical `Zorn`, the Witt/CAR carrier, or an abstract
five-grading.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralZornNCZornBridge

open InfoGeometry.Physics.NCG
open InfoGeometry.Physics.Octonion

variable {R A : Type*} [Ring R] [Ring A]

theorem nc_ext {X Y : NCZornElement A}
    (hnp : X.n_plus = Y.n_plus)
    (hnm : X.n_minus = Y.n_minus)
    (hsp : X.sigma_plus = Y.sigma_plus)
    (hsm : X.sigma_minus = Y.sigma_minus) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- The identity-on-coordinates map from the chiral split-octonion carrier to
the native noncommutative operator carrier. -/
def toNC (X : ChiralZornMatrix A) : NCZornElement A where
  n_plus := X.n_plus
  n_minus := X.n_minus
  sigma_plus := X.sigma_plus
  sigma_minus := X.sigma_minus

/-- The inverse identity-on-coordinates map. -/
def ofNC (X : NCZornElement A) : ChiralZornMatrix A where
  n_plus := X.n_plus
  n_minus := X.n_minus
  sigma_plus := X.sigma_plus
  sigma_minus := X.sigma_minus

@[simp] theorem of_to (X : ChiralZornMatrix A) :
    ofNC (toNC X) = X := by
  cases X
  rfl

@[simp] theorem to_of (X : NCZornElement A) :
    toNC (ofNC X) = X := by
  cases X
  rfl

/-- The coordinate equivalence between the chiral Zorn carrier and its native
noncommutative presentation.  This is bundled as an ordinary equivalence,
not as a ring equivalence: the Zorn product is allowed to be
nonassociative. -/
def chiralZornEquivNC : ChiralZornMatrix A ≃ NCZornElement A where
  toFun := toNC
  invFun := ofNC
  left_inv := of_to
  right_inv := to_of

@[simp] theorem chiralZornEquivNC_apply (X : ChiralZornMatrix A) :
    chiralZornEquivNC X = toNC X := rfl

@[simp] theorem chiralZornEquivNC_symm_apply (X : NCZornElement A) :
    chiralZornEquivNC.symm X = ofNC X := rfl

/-- The chiral split-octonion product is the same eight-slot product as the
native NC-Zorn product.  Only commutativity of addition is used to reorder the
two summands in the diagonal and lower chiral entries. -/
theorem toNC_mul (X Y : ChiralZornMatrix A) :
    toNC (X * Y) =
      NCZornElement.mul (toNC X) (toNC Y) := by
  apply nc_ext
  · rfl
  · exact add_comm _ _
  · funext c
    fin_cases c <;>
      rfl
  · funext c
    change (ChiralZornMatrix.mul X Y).sigma_minus c = _
    fin_cases c <;>
      simp [toNC, ChiralZornMatrix.mul, NCZornElement.mul,
        colorCross, nextColor, prevColor, NCZornElement.zornCross]
      <;> abel

/-- Multiplication is transported by the coordinate equivalence.  This is a
plain compatibility theorem rather than a `RingHom`, since the carrier's
Zorn multiplication is not asserted to be associative. -/
theorem chiralZornEquivNC_mul (X Y : ChiralZornMatrix A) :
    chiralZornEquivNC (X * Y) =
      NCZornElement.mul (chiralZornEquivNC X) (chiralZornEquivNC Y) := by
  exact toNC_mul X Y

theorem toNC_add (X Y : ChiralZornMatrix A) :
    toNC (X + Y) = toNC X + toNC Y := by
  cases X
  cases Y
  rfl

theorem toNC_neg (X : ChiralZornMatrix A) :
    toNC (-X) = -toNC X := by
  cases X
  rfl

theorem toNC_sub (X Y : ChiralZornMatrix A) :
    toNC (X - Y) = toNC X + -toNC Y := by
  calc
    toNC (X - Y) = toNC (X + -Y) := by rw [sub_eq_add_neg]
    _ = toNC X + toNC (-Y) := toNC_add X (-Y)
    _ = toNC X + -toNC Y := by rw [toNC_neg]

theorem toNC_commutator (X Y : ChiralZornMatrix A) :
    toNC (X * Y - Y * X) =
      NCZornElement.mul (toNC X) (toNC Y) +
        -NCZornElement.mul (toNC Y) (toNC X) := by
  rw [toNC_sub, toNC_mul, toNC_mul]

theorem toNC_anticommutator (X Y : ChiralZornMatrix A) :
    toNC (X * Y + Y * X) =
      NCZornElement.mul (toNC X) (toNC Y) +
        NCZornElement.mul (toNC Y) (toNC X) := by
  rw [toNC_add, toNC_mul, toNC_mul]

theorem toNC_associator (X Y Z : ChiralZornMatrix A) :
    toNC ((X * Y) * Z - X * (Y * Z)) =
      NCZornElement.mul (NCZornElement.mul (toNC X) (toNC Y)) (toNC Z) +
        -
        NCZornElement.mul (toNC X)
          (NCZornElement.mul (toNC Y) (toNC Z)) := by
  rw [toNC_sub]
  simp only [toNC_mul]

/-- The operatorial instance used by the symmetry calculations: each chiral
component is itself a `2 × 2` matrix, giving eight matrix-valued slots. -/
abbrev MatrixTwoOperator := Matrix (Fin 2) (Fin 2) ℂ

abbrev MatrixTwoOperatorVector := Fin 3 → MatrixTwoOperator

theorem toNC_matrixTwo_mul
    (X Y : ChiralZornMatrix MatrixTwoOperator) :
    toNC (X * Y) =
      NCZornElement.mul (toNC X) (toNC Y) :=
  toNC_mul X Y

theorem matrixTwo_sigma_plus_commutator_hodge
    (U V : MatrixTwoOperatorVector) :
    operatorCommutator (sigmaPlus U) (sigmaPlus V) =
      sigmaMinus (operatorHodgeDual2 (operatorBivectorChannel U V)) := by
  exact same_chiral_plus_commutator_hodge_bivector_channel U V

theorem matrixTwo_sigma_minus_commutator_hodge
    (U V : MatrixTwoOperatorVector) :
    operatorCommutator (sigmaMinus U) (sigmaMinus V) =
      sigmaPlus (-(operatorHodgeDual2 (operatorBivectorChannel U V))) := by
  exact same_chiral_minus_commutator_hodge_bivector_channel U V

theorem matrixTwo_sigma_mixed_anticommutator
    (U V : MatrixTwoOperatorVector) :
    operatorAnticommutator (sigmaPlus U) (sigmaMinus V) =
      operatorAdd (nPlus (operatorDot U V)) (nMinus (operatorDot V U)) := by
  exact mixed_chiral_anticommutator_channel U V

theorem matrixTwo_sigma_mixed_commutator
    (U V : MatrixTwoOperatorVector) :
    operatorCommutator (sigmaPlus U) (sigmaMinus V) =
      operatorSubChannel (nPlus (operatorDot U V)) (nMinus (operatorDot V U)) := by
  exact mixed_chiral_commutator_channel U V

end InfoGeometry.Canonical.ChiralZornNCZornBridge

end
