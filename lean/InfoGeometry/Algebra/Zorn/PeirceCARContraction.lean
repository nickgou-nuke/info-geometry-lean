import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Peirce contraction in the canonical Zorn carrier

This file records the exact binary identities behind the upper and lower
Peirce sectors.  The carrier is the repository's explicit, non-associative
Zorn product; no associative CAR structure is installed on it.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

open InfoGeometry.Algebra

abbrev ZornReal := ZornVectorMatrix ℝ
abbrev Vec3Real := ZornVec3 ℝ

def peircePlus : ZornReal := E11
def peirceMinus : ZornReal := E22
def peirceUpper (u : Vec3Real) : ZornReal := offDiagonal u 0
def peirceLower (v : Vec3Real) : ZornReal := offDiagonal 0 v

@[simp] theorem peircePlus_sq : mul peircePlus peircePlus = peircePlus := by
  exact E11_mul_E11

@[simp] theorem peirceMinus_sq : mul peirceMinus peirceMinus = peirceMinus := by
  exact E22_mul_E22

theorem peirce_complementary : peircePlus + peirceMinus = one := by
  change add E11 E22 = one
  ext i <;> simp [E11, E22, one, add]

@[simp] theorem peircePlus_mul_minus :
    mul peircePlus peirceMinus = zero := by
  exact E11_mul_E22

@[simp] theorem peirceMinus_mul_plus :
    mul peirceMinus peircePlus = zero := by
  exact E22_mul_E11

@[simp] theorem peirceUpper_sq (u : Vec3Real) :
    mul (peirceUpper u) (peirceUpper u) = zero := by
  simpa [peirceUpper, offDiagonal, diagonal, add, zero] using
    (offDiagonal_mul_offDiagonal u (fun _ => 0) u (fun _ => 0))

@[simp] theorem peirceLower_sq (v : Vec3Real) :
    mul (peirceLower v) (peirceLower v) = zero := by
  simpa [peirceLower, offDiagonal, diagonal, add, zero] using
    (offDiagonal_mul_offDiagonal (fun _ => 0) v (fun _ => 0) v)

theorem peirceUpper_mul_lower (u v : Vec3Real) :
    mul (peirceUpper u) (peirceLower v) =
      diagonal (ZornVec3.dot u v) 0 := by
  simpa [peirceUpper, peirceLower, diagonal, add, offDiagonal] using
    (offDiagonal_mul_offDiagonal u (fun _ => 0) (fun _ => 0) v)

theorem peirceLower_mul_upper (v u : Vec3Real) :
    mul (peirceLower v) (peirceUpper u) =
      diagonal 0 (ZornVec3.dot v u) := by
  simpa [peirceLower, peirceUpper, diagonal, add, offDiagonal] using
    (offDiagonal_mul_offDiagonal (fun _ => 0) v u (fun _ => 0))

theorem peirce_CAR_contraction (u v : Vec3Real) :
    mul (peirceUpper u) (peirceLower v) +
        mul (peirceLower v) (peirceUpper u) =
      scalar (ZornVec3.dot u v) := by
  rw [peirceUpper_mul_lower, peirceLower_mul_upper]
  rw [ZornVec3.dot_comm v u]
  change add (diagonal (ZornVec3.dot u v) 0)
      (diagonal 0 (ZornVec3.dot u v)) = scalar (ZornVec3.dot u v)
  ext i <;> simp [add, diagonal, scalar]

theorem peirce_upper_CAR_zero (u v : Vec3Real) :
    mul (peirceUpper u) (peirceUpper v) +
        mul (peirceUpper v) (peirceUpper u) = 0 := by
  rw [peirceUpper, peirceUpper, offDiagonal_mul_offDiagonal]
  rw [offDiagonal_mul_offDiagonal]
  have h := ZornVec3.cross_anti u v
  rw [h]
  change add _ _ = zero
  ext i <;> simp [add, diagonal, offDiagonal, zero, ZornVec3.dot,
    ZornVec3.cross]

theorem peirce_lower_CAR_zero (u v : Vec3Real) :
    mul (peirceLower u) (peirceLower v) +
        mul (peirceLower v) (peirceLower u) = 0 := by
  rw [peirceLower, peirceLower, offDiagonal_mul_offDiagonal]
  rw [offDiagonal_mul_offDiagonal]
  have h := ZornVec3.cross_anti u v
  rw [h]
  change add _ _ = zero
  ext i <;> simp [add, diagonal, offDiagonal, zero, ZornVec3.dot,
    ZornVec3.cross]

theorem peirce_ambient_nonassociative :
    mul (mul (U 0 : ZornReal) (U 1)) (U 2) ≠
      mul (U 0) (mul (U 1) (U 2)) :=
  nonassociative_witness

end InfoGeometry.Algebra.ZornVectorMatrix
