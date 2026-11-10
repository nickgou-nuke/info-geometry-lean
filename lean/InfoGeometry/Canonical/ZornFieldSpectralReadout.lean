import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornPotentialDifferentialReadout
import Mathlib.Tactic

/-!
# Spectral scalar readout for off-diagonal Zorn fields

The Zorn product is non-associative, so an element does not acquire an
ordinary characteristic polynomial merely from its vector-matrix notation.
This owner records the valid quadratic readout: the square of a pure
off-diagonal element is a diagonal scalar.  An eigenvalue statement requires
an additional associative representation and is deliberately kept separate.
-/

namespace InfoGeometry.Canonical.ZornFieldSpectralReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout

variable {R : Type*} [Ring R]

local notation "Vec3" => ZornVec3 R
local notation "ZM" => ZornVectorMatrix R

/-- Over any non-commutative ring `[Ring R]`, the square of a pure off-diagonal Zorn
field decomposes into the diagonal `(dot u v, dot v u)` and the internal commutator
cross-product anomaly `offDiagonal (-cross v v) (cross u u)`. -/
theorem offDiagonal_square_noncomm (u v : Vec3) :
    mul (offDiagonal u v) (offDiagonal u v) =
      add
        (diagonal (dot u v) (dot v u))
        (offDiagonal (fun i => -cross v v i) (cross u u)) :=
  ZornVectorMatrix.offDiagonal_mul_self_noncomm u v

theorem offDiagonal_square_norm_readout (u v : Vec3) :
    ZornVectorMatrix.norm (offDiagonal u v) = -(dot u v) := by
  simp [ZornVectorMatrix.norm, offDiagonal]

/-! The Maxwell-shaped off-diagonal field uses the existing differential readout over `[Ring R]`. -/
def gaugeFixedField (P : PotentialDifferentialData (R := R)) : ZM :=
  ⟨0, upperFieldReadout P, fun i => -(upperFieldReadout P i), 0⟩

theorem gaugeFixedField_eq_offDiagonal (P : PotentialDifferentialData (R := R)) :
    gaugeFixedField P =
      offDiagonal (upperFieldReadout P)
        (fun i => -(upperFieldReadout P i)) :=
  rfl

/-- Over any non-commutative ring `[Ring R]`, the square of the gauge-fixed Zorn field
splits into the symmetric diagonal `-dot F F` and the self-cross commutator anomaly
`offDiagonal (-cross F F) (cross F F)`. -/
theorem gaugeFixedField_square_noncomm (P : PotentialDifferentialData (R := R)) :
    mul (gaugeFixedField P) (gaugeFixedField P) =
      add
        (scalar (-dot (upperFieldReadout P) (upperFieldReadout P)))
        (offDiagonal
          (fun i => -cross (upperFieldReadout P) (upperFieldReadout P) i)
          (cross (upperFieldReadout P) (upperFieldReadout P))) := by
  rw [gaugeFixedField_eq_offDiagonal, offDiagonal_mul_offDiagonal]
  have hd1 : dot (upperFieldReadout P) (fun i => -(upperFieldReadout P i)) =
      -dot (upperFieldReadout P) (upperFieldReadout P) :=
    ZornVec3.dot_neg_right _ _
  have hd2 : dot (fun i => -(upperFieldReadout P i)) (upperFieldReadout P) =
      -dot (upperFieldReadout P) (upperFieldReadout P) :=
    ZornVec3.dot_neg_left _ _
  have hc : cross (fun i => -(upperFieldReadout P i)) (fun i => -(upperFieldReadout P i)) =
      cross (upperFieldReadout P) (upperFieldReadout P) := by
    ext i
    fin_cases i <;>
      dsimp [ZornVec3.cross] <;>
      noncomm_ring
  rw [hd1, hd2, hc]
  rfl

/-! The quadratic Zorn readout of a pure off-diagonal element over a commutative ring. -/
theorem offDiagonal_mul_self_eq_scalar_dot {R : Type*} [CommRing R] (u v : ZornVec3 R) :
    mul (offDiagonal u v) (offDiagonal u v) =
      scalar (dot u v) := by
  ext i
  · simp [mul, scalar, offDiagonal, ZornVec3.dot]
  · fin_cases i <;>
      simp [mul, scalar, offDiagonal, ZornVec3.cross_self]
  · fin_cases i <;>
      simp [mul, scalar, offDiagonal, ZornVec3.cross_self]
  · simp [mul, scalar, offDiagonal, ZornVec3.dot]
    simp [mul_comm]

/-! The invariant attached to the conventional electric/magnetic blocks. -/
theorem electricMagnetic_offDiagonal_square {R : Type*} [CommRing R] (electric magnetic : ZornVec3 R) :
    mul
        (offDiagonal
          (fun i => -(electric i + magnetic i))
          (fun i => electric i - magnetic i))
        (offDiagonal
          (fun i => -(electric i + magnetic i))
          (fun i => electric i - magnetic i)) =
      scalar (dot magnetic magnetic - dot electric electric) := by
  rw [offDiagonal_mul_self_eq_scalar_dot]
  congr 1
  simp [ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem gaugeFixedField_square_eq_scalar_neg_dot {R : Type*} [CommRing R]
    (P : PotentialDifferentialData (R := R)) :
    mul (gaugeFixedField P) (gaugeFixedField P) =
      scalar (-dot (upperFieldReadout P) (upperFieldReadout P)) := by
  rw [gaugeFixedField_eq_offDiagonal,
    offDiagonal_mul_self_eq_scalar_dot]
  exact congrArg scalar (ZornVec3.dot_neg_right
    (upperFieldReadout P) (upperFieldReadout P))

end InfoGeometry.Canonical.ZornFieldSpectralReadout
