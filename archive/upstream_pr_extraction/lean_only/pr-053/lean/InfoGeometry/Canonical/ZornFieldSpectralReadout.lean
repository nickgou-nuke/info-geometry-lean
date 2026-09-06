import InfoGeometry.Algebra.ZornVectorMatrix
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

variable {R : Type*} [CommRing R]

local notation "Vec3" => ZornVec3 R
local notation "ZM" => ZornVectorMatrix R

/-! The quadratic Zorn readout of a pure off-diagonal element. -/
theorem offDiagonal_mul_self_eq_scalar_dot (u v : Vec3) :
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

theorem offDiagonal_square_norm_readout (u v : Vec3) :
    ZornVectorMatrix.norm (offDiagonal u v) = -(dot u v) := by
  simp [ZornVectorMatrix.norm, offDiagonal]

/-! The invariant attached to the conventional electric/magnetic blocks. -/
theorem electricMagnetic_offDiagonal_square (electric magnetic : Vec3) :
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

/-! The Maxwell-shaped off-diagonal field uses the existing differential readout. -/
def gaugeFixedField (P : PotentialDifferentialData (R := R)) : ZM :=
  ⟨0, upperFieldReadout P, fun i => -(upperFieldReadout P i), 0⟩

theorem gaugeFixedField_eq_offDiagonal (P : PotentialDifferentialData (R := R)) :
    gaugeFixedField P =
      offDiagonal (upperFieldReadout P)
        (fun i => -(upperFieldReadout P i)) :=
  rfl

theorem gaugeFixedField_square_eq_scalar_neg_dot (P : PotentialDifferentialData (R := R)) :
    mul (gaugeFixedField P) (gaugeFixedField P) =
      scalar (-dot (upperFieldReadout P) (upperFieldReadout P)) := by
  rw [gaugeFixedField_eq_offDiagonal,
    offDiagonal_mul_self_eq_scalar_dot]
  exact congrArg scalar (ZornVec3.dot_neg_right
    (upperFieldReadout P) (upperFieldReadout P))

end InfoGeometry.Canonical.ZornFieldSpectralReadout
