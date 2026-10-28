/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceGrading
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Complex.Order

/-!
# Peirce commutators and Hermitian charges

The existing directed corners and parity projection are used throughout. The
commutator is skew-adjoint under the star hypotheses. Multiplication by `I`
produces the second Hermitian charge. No commutation of the input with the
projection, invertibility of the corners, or positive definiteness is assumed.
-/

namespace InfoGeometry.Core.PeirceStarCharges

open PeirceDecomposition PeirceGrading

section Ring

variable {A : Type*} [Ring A]

theorem commutator_eq_corners (p x : A) :
    ⁅p, x⁆ = component10 p x - component01 p x := by
  change p * x - x * p = _
  simp only [component10, component01, complementIdempotent]
  noncomm_ring

theorem odd_square {p : A} (hp : IsIdempotentElem p) (x : A) :
    (odd p x) ^ 2 =
      component10 p x * component01 p x + component01 p x * component10 p x := by
  rw [odd_apply]
  change (component10 p x + component01 p x) ^ 2 = _
  have hu : (component10 p x) ^ 2 = 0 := (corners_sq_zero hp x).1
  have hv : (component01 p x) ^ 2 = 0 := (corners_sq_zero hp x).2
  calc
    _ = (component10 p x) ^ 2 +
        (component10 p x * component01 p x + component01 p x * component10 p x) +
        (component01 p x) ^ 2 := by noncomm_ring
    _ = _ := by rw [hu, hv]; simp

theorem commutator_square {p : A} (hp : IsIdempotentElem p) (x : A) :
    ⁅p, x⁆ ^ 2 = -(odd p x) ^ 2 := by
  rw [commutator_eq_corners, odd_square hp]
  have hu : (component10 p x) ^ 2 = 0 := (corners_sq_zero hp x).1
  have hv : (component01 p x) ^ 2 = 0 := (corners_sq_zero hp x).2
  calc
    _ = (component10 p x) ^ 2 + (component01 p x) ^ 2 -
        (component10 p x * component01 p x + component01 p x * component10 p x) := by
      noncomm_ring
    _ = _ := by rw [hu, hv]; simp

theorem commutator_odd_anticommute {p : A} (hp : IsIdempotentElem p) (x : A) :
    ⁅p, x⁆ * odd p x + odd p x * ⁅p, x⁆ = 0 := by
  rw [commutator_eq_corners, odd_apply]
  change (component10 p x - component01 p x) *
      (component10 p x + component01 p x) +
    (component10 p x + component01 p x) *
      (component10 p x - component01 p x) = 0
  have hu : (component10 p x) ^ 2 = 0 := (corners_sq_zero hp x).1
  have hv : (component01 p x) ^ 2 = 0 := (corners_sq_zero hp x).2
  calc
    _ = 2 • ((component10 p x) ^ 2 - (component01 p x) ^ 2) := by
      simp only [two_nsmul]
      noncomm_ring
    _ = 0 := by rw [hu, hv]; simp

theorem commutator_add_odd (p x : A) :
    ⁅p, x⁆ + odd p x = 2 • component10 p x := by
  rw [commutator_eq_corners, odd_apply, two_nsmul]
  change (component10 p x - component01 p x) +
    (component10 p x + component01 p x) = _
  abel

theorem commutator_add_odd_square_zero {p : A} (hp : IsIdempotentElem p) (x : A) :
    (⁅p, x⁆ + odd p x) ^ 2 = 0 := by
  rw [commutator_add_odd, two_nsmul]
  have hu : (component10 p x) ^ 2 = 0 := (corners_sq_zero hp x).1
  calc
    _ = 4 • (component10 p x) ^ 2 := by noncomm_ring
    _ = 0 := by rw [hu, smul_zero]

theorem reflection_mul_odd {p : A} (hp : IsIdempotentElem p) (x : A) :
    reflection p * odd p x = ⁅p, x⁆ := by
  rw [(odd_reconstruction hp x).1, ← mul_assoc, reflection_sq hp, one_mul]
  rfl

/-- Noncommutation is exactly nonvanishing of the existing odd projection. -/
theorem odd_eq_zero_iff_commute {p : A} (hp : IsIdempotentElem p) (x : A) :
    odd p x = 0 ↔ Commute p x := by
  constructor
  · intro hz
    have h := reflection_mul_odd hp x
    rw [hz, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  · intro hc
    rw [(odd_reconstruction hp x).1, hc.eq, sub_self, mul_zero]

end Ring

section Star

variable {A : Type*} [Ring A] [StarRing A] {p x : A}

theorem star_corner (hp : IsSelfAdjoint p) (hx : IsSelfAdjoint x) :
    star (component10 p x) = component01 p x := by
  simp only [component10, component01, complementIdempotent, star_mul,
    star_sub, star_one, hp.star_eq, hx.star_eq, mul_assoc]

theorem commutator_mem_skewAdjoint (hp : IsSelfAdjoint p) (hx : IsSelfAdjoint x) :
    ⁅p, x⁆ ∈ skewAdjoint A := by
  change star (p * x - x * p) = -(p * x - x * p)
  simp only [star_sub, star_mul, hp.star_eq, hx.star_eq]
  abel

theorem odd_isSelfAdjoint (hp : IsSelfAdjoint p) (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (odd p x) := by
  change star (odd p x) = odd p x
  simp only [odd_apply, star_add, star_mul, star_sub, star_one,
    hp.star_eq, hx.star_eq]
  noncomm_ring

/-- The common square is the sum of the two opposite corner Gram products. -/
theorem odd_square_eq_gram (hp : IsStarProjection p) (hx : IsSelfAdjoint x) :
    (odd p x) ^ 2 =
      component10 p x * star (component10 p x) +
        star (component10 p x) * component10 p x := by
  rw [star_corner hp.isSelfAdjoint hx, odd_square hp.isIdempotentElem]

end Star

section ComplexMatrices

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p x : Matrix n n ℂ}

theorem imaginary_commutator_isHermitian
    (hp : IsSelfAdjoint p) (hx : IsSelfAdjoint x) :
    (Complex.I • ⁅p, x⁆).IsHermitian := by
  apply IsSelfAdjoint.isHermitian
  exact isSelfAdjoint_smul_of_mem_skewAdjoint
    (show Complex.I ∈ skewAdjoint ℂ from Complex.conj_I)
    (commutator_mem_skewAdjoint hp hx)

theorem imaginary_commutator_square (hp : IsIdempotentElem p) (x : Matrix n n ℂ) :
    (Complex.I • ⁅p, x⁆) ^ 2 = (odd p x) ^ 2 := by
  calc
    _ = (Complex.I * Complex.I) • (⁅p, x⁆ * ⁅p, x⁆) := by
      simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = -(⁅p, x⁆ ^ 2) := by rw [Complex.I_mul_I, neg_one_smul, pow_two]
    _ = (odd p x) ^ 2 := by rw [commutator_square hp, neg_neg]

theorem odd_imaginary_commutator_anticommute (hp : IsIdempotentElem p) (x : Matrix n n ℂ) :
    odd p x * (Complex.I • ⁅p, x⁆) + (Complex.I • ⁅p, x⁆) * odd p x = 0 := by
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [← smul_add, add_comm, commutator_odd_anticommute hp, smul_zero]

theorem odd_square_posSemidef (hp : IsStarProjection p) (hx : IsSelfAdjoint x) :
    ((odd p x) ^ 2).PosSemidef := by
  rw [odd_square_eq_gram hp hx]
  exact (Matrix.posSemidef_self_mul_conjTranspose (component10 p x)).add
    (Matrix.posSemidef_conjTranspose_mul_self (component10 p x))

theorem imaginary_commutator_square_posSemidef
    (hp : IsStarProjection p) (hx : IsSelfAdjoint x) :
    ((Complex.I • ⁅p, x⁆) ^ 2).PosSemidef := by
  rw [imaginary_commutator_square hp.isIdempotentElem]
  exact odd_square_posSemidef hp hx

/-- The positive square has exactly the same zero modes as the odd charge. -/
theorem odd_square_kernel (hp : IsSelfAdjoint p) (hx : IsSelfAdjoint x) :
    LinearMap.ker ((odd p x) ^ 2).mulVecLin = LinearMap.ker (odd p x).mulVecLin := by
  have hs : (odd p x).conjTranspose = odd p x := (odd_isSelfAdjoint hp hx).isHermitian
  simpa only [hs, pow_two] using
    Matrix.ker_mulVecLin_conjTranspose_mul_self (odd p x)

end ComplexMatrices

end InfoGeometry.Core.PeirceStarCharges
