/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Clifford.KleinBottleLoxodromicTwistCPTBridge
import InfoGeometry.Canonical.KleinBottleTwistedCommutantBridge

/-!
# Klein glide holonomy as a twisted commutant

Conjugation by the Klein parity generator `e1` is an involutive ring
automorphism of `M₂(R)`. The generator itself is therefore an α-twisted
intertwiner, and the Klein glide `e1 (B X Bᵀ) e1` is the α-conjugate congruence
that produces the glide. The orientation double cover restores the ordinary
commutant, matching the existing `glide_reflection_sq_dilation`.
-/
namespace InfoGeometry.Canonical.KleinGlideTwistedCommutantBridge

open Matrix
open InfoGeometry.Clifford.Coquaternion.Coquaternion
open InfoGeometry.Clifford.KleinBottleLoxodromicTwist
open InfoGeometry.Canonical.KleinBottleTwistedCommutant

variable {R : Type*} [CommRing R]

/-- The Klein parity generator in M₂(R). -/
abbrev kE (R : Type*) [Ring R] : Mat2 R := InfoGeometry.Clifford.KleinBottleLoxodromicTwist.e1

theorem kE_sq : (kE R : Mat2 R) * kE R = 1 :=
  InfoGeometry.Clifford.KleinBottleLoxodromicTwist.e1_sq_one

/-- Klein holonomy automorphism: conjugation by the parity reflection `e1`. -/
def kleinConjAut : RingAut (Mat2 R) where
  toFun X := (kE R) * X * kE R
  invFun X := (kE R) * X * kE R
  left_inv X := by
    change (kE R) * ((kE R) * X * kE R) * kE R = X
    calc
      (kE R) * ((kE R) * X * kE R) * kE R = ((kE R) * kE R) * X * ((kE R) * kE R) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [kE_sq, one_mul, mul_one]
  right_inv X := by
    change (kE R) * ((kE R) * X * kE R) * kE R = X
    calc
      (kE R) * ((kE R) * X * kE R) * kE R = ((kE R) * kE R) * X * ((kE R) * kE R) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [kE_sq, one_mul, mul_one]
  map_add' X Y := by
    change (kE R) * (X + Y) * kE R = (kE R) * X * kE R + (kE R) * Y * kE R
    noncomm_ring
  map_mul' X Y := by
    change (kE R) * (X * Y) * kE R = ((kE R) * X * kE R) * ((kE R) * Y * kE R)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (kE R) (kE R), kE_sq, one_mul]

/-- The Klein holonomy is an involution. -/
def kleinInvolution : KleinInvolution (Mat2 R) where
  toRingAut := kleinConjAut
  involutive X := by
    exact kleinConjAut.left_inv X

/-- The parity generator is an α-twisted intertwiner. -/
theorem e1_isTwistedCommutant :
    IsTwistedCommutant (RingHom.id (Mat2 R)) kleinConjAut (kE R) := by
  intro a
  change (kE R) * a = ((kE R) * a * kE R) * kE R
  simp only [Matrix.mul_assoc]
  rw [kE_sq, mul_one]

/-- The glide is the α-conjugate of the lattice congruence `X ↦ B X Bᵀ`. -/
theorem kleinGlide_eq_kleinConjAut (B X : Mat2 R) :
    kleinGlide B X = kleinConjAut (B * X * Bᵀ) := rfl

/-- The reflection generator is a unit of order two, so it implements the
    Klein automorphism by conjugation in the sense of the existing API. -/
def e1Unit : (Mat2 R)ˣ where
  val := kE R
  inv := kE R
  val_inv := kE_sq (R := R)
  inv_val := kE_sq (R := R)

theorem e1Unit_conjugates (a : Mat2 R) :
    ((e1Unit : (Mat2 R)ˣ) : Mat2 R) * a * ((e1Unit⁻¹ : (Mat2 R)ˣ) : Mat2 R) =
      kleinConjAut a := by
  change (kE R) * a * kE R = (kE R) * a * kE R
  rfl

/-- The double cover is untwisted: the square of the glide generator lies in
    the ordinary commutant, and the two-fold glide doubles the boost. -/
theorem klein_glide_double_cover (c s : R) (X : Mat2 R) :
    IsCommutant (RingHom.id (Mat2 R)) ((kE R) * kE R) ∧
      kleinGlide (boostX c s) (kleinGlide (boostX c s) X) =
        boostX (c * c + s * s) (c * s + s * c) * X *
          (boostX (c * c + s * s) (c * s + s * c))ᵀ := by
  refine ⟨klein_glide_square_in_commutant (RingHom.id (Mat2 R)) (kE R)
      kleinInvolution e1_isTwistedCommutant, ?_⟩
  exact glide_reflection_sq_noncomm c s X

end InfoGeometry.Canonical.KleinGlideTwistedCommutantBridge
