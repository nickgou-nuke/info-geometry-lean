/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CattoGurseySplitBasis
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Moment-curve baryons on the existing signed Zorn carrier

The repository's `ZornVec3 R = Fin 3 → R` dot and cross products agree with
Mathlib's native operations. Their scalar triple product is consequently a
native determinant. On the moment curve `(1,t,t²)`, that determinant is the
native three-node Vandermonde determinant.

The actual Zorn multiplication remains nonassociative. In the existing signed
convention, the left triple is `-Δ • uStarZero` and the right triple is
`-Δ • uZero`; their difference is `Δ • (uZero - uStarZero)`. Over an integral
domain, collision of two distinct nodes characterizes vanishing of either
triple and equality of its two parenthesizations. No embedding into the
associative `6|21` matrix algebra or physical confinement theorem is asserted.
-/

namespace InfoGeometry.Canonical.GunaydinGursey

open InfoGeometry.Algebra
open ZornVectorMatrix
open scoped Matrix

variable {R : Type*} [CommRing R]

/-- The owned vector pairing is Mathlib's native dot product. -/
theorem zornVec3_dot_eq_dotProduct (x y : ZornVec3 R) :
    ZornVec3.dot x y = dotProduct x y := rfl

/-- Compatibility of the owned coordinate cross product with Mathlib's
bilinear cross product, on the same carrier. -/
theorem zornVec3_cross_eq_crossProduct (x y : ZornVec3 R) :
    ZornVec3.cross x y = crossProduct x y := by
  ext i
  fin_cases i <;> simp [ZornVec3.cross, cross_apply]

/-- The generic signed-basis baryon coefficient is a native row determinant. -/
theorem zornVec3_triple_eq_det_rows (x y z : ZornVec3 R) :
    ZornVec3.dot x (ZornVec3.cross y z) = Matrix.det ![x, y, z] := by
  rw [zornVec3_dot_eq_dotProduct, zornVec3_cross_eq_crossProduct]
  exact triple_product_eq_det x y z

/-- The spectral moment curve in the existing color-vector carrier. -/
def momentCurve (t : R) : ZornVec3 R := ![1, t, t ^ 2]

/-- Three ordered moment-curve vectors form exactly the native Vandermonde
matrix, with nodes as rows and powers as columns. -/
theorem momentCurve_rows_eq_vandermonde (t : Fin 3 → R) :
    ![momentCurve (t 0), momentCurve (t 1), momentCurve (t 2)] =
      Matrix.vandermonde t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [momentCurve, Matrix.vandermonde]

/-- The diquark cross product already contains the first collision factor. -/
theorem momentCurve_cross_factorization (x y : R) :
    ZornVec3.cross (momentCurve x) (momentCurve y) =
      (y - x) • ![x * y, -(x + y), 1] := by
  ext i
  fin_cases i <;> simp [ZornVec3.cross, momentCurve, smul_eq_mul] <;> ring

/-- The baryon coefficient on the moment curve is the native Vandermonde
determinant, without identifying the two Zorn parenthesizations. -/
theorem momentCurve_triple_eq_vandermonde (t : Fin 3 → R) :
    ZornVec3.dot (momentCurve (t 0))
        (ZornVec3.cross (momentCurve (t 1)) (momentCurve (t 2))) =
      Matrix.det (Matrix.vandermonde t) := by
  rw [zornVec3_triple_eq_det_rows, momentCurve_rows_eq_vandermonde t]

/-- Exact three-node separation factor, with the original order retained. -/
theorem momentCurve_triple_eq_separation (t : Fin 3 → R) :
    ZornVec3.dot (momentCurve (t 0))
        (ZornVec3.cross (momentCurve (t 1)) (momentCurve (t 2))) =
      (t 1 - t 0) * (t 2 - t 0) * (t 2 - t 1) := by
  rw [momentCurve_triple_eq_vandermonde t, Matrix.det_fin_three]
  simp only [Matrix.vandermonde_apply]
  norm_num
  ring

/-- Specialization of the existing nonassociative baryon theorem. The same
negative determinant multiplies two different, ordered singlet endpoints. -/
theorem momentCurve_baryon_parenthesizations (t : Fin 3 → R) :
    mul (mul (offDiagonal 0 (momentCurve (t 0)))
        (offDiagonal 0 (momentCurve (t 1))))
        (offDiagonal 0 (momentCurve (t 2))) =
      smul (-Matrix.det (Matrix.vandermonde t)) uStarZero ∧
    mul (offDiagonal 0 (momentCurve (t 0)))
        (mul (offDiagonal 0 (momentCurve (t 1)))
          (offDiagonal 0 (momentCurve (t 2)))) =
      smul (-Matrix.det (Matrix.vandermonde t)) uZero := by
  simpa only [momentCurve_triple_eq_vandermonde t] using
    baryon_parenthesizations (momentCurve (t 0)) (momentCurve (t 1)) (momentCurve (t 2))

/-- The exact reassociation defect is the Vandermonde determinant times the
signed difference of the two existing singlet projectors. -/
theorem momentCurve_associator (t : Fin 3 → R) :
    associator (offDiagonal 0 (momentCurve (t 0)))
        (offDiagonal 0 (momentCurve (t 1)))
        (offDiagonal 0 (momentCurve (t 2))) =
      Matrix.det (Matrix.vandermonde t) • (uZero - uStarZero) := by
  have h := momentCurve_baryon_parenthesizations t
  unfold associator
  rw [h.1, h.2]
  change sub (smul (-Matrix.det (Matrix.vandermonde t)) uStarZero)
      (smul (-Matrix.det (Matrix.vandermonde t)) uZero) =
    smul (Matrix.det (Matrix.vandermonde t)) (sub uZero uStarZero)
  ext i <;> simp [smul, sub, add, neg, uZero, uStarZero, E11, E22]

private theorem smul_uStarZero_eq_zero_iff (c : R) :
    smul c (uStarZero : ZornVectorMatrix R) = 0 ↔ c = 0 := by
  constructor
  · intro h
    have ha := congrArg ZornVectorMatrix.a h
    change c * 1 = 0 at ha
    simpa only [_root_.mul_one] using ha
  · intro h
    rw [h]
    exact ZornVectorMatrix.zero_smul _

private theorem smul_uZero_eq_zero_iff (c : R) :
    smul c (uZero : ZornVectorMatrix R) = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hb := congrArg ZornVectorMatrix.b h
    change c * 1 = 0 at hb
    simpa only [_root_.mul_one] using hb
  · intro h
    rw [h]
    exact ZornVectorMatrix.zero_smul _

private theorem smul_singlets_eq_iff (c : R) :
    smul c (uStarZero : ZornVectorMatrix R) = smul c uZero ↔ c = 0 := by
  constructor
  · intro h
    have ha := congrArg ZornVectorMatrix.a h
    change c * 1 = c * 0 at ha
    simpa using ha
  · intro h
    rw [h, ZornVectorMatrix.zero_smul, ZornVectorMatrix.zero_smul]

section Domain

variable [IsDomain R]

/-- Collision characterizes vanishing of the actual left-associated product. -/
theorem momentCurve_baryon_left_eq_zero_iff_collision (t : Fin 3 → R) :
    mul (mul (offDiagonal 0 (momentCurve (t 0)))
        (offDiagonal 0 (momentCurve (t 1))))
        (offDiagonal 0 (momentCurve (t 2))) = 0 ↔
      ∃ i j : Fin 3, t i = t j ∧ i ≠ j := by
  rw [(momentCurve_baryon_parenthesizations t).1, smul_uStarZero_eq_zero_iff,
    _root_.neg_eq_zero, Matrix.det_vandermonde_eq_zero_iff]

/-- Collision characterizes vanishing of the actual right-associated product. -/
theorem momentCurve_baryon_right_eq_zero_iff_collision (t : Fin 3 → R) :
    mul (offDiagonal 0 (momentCurve (t 0)))
        (mul (offDiagonal 0 (momentCurve (t 1)))
          (offDiagonal 0 (momentCurve (t 2)))) = 0 ↔
      ∃ i j : Fin 3, t i = t j ∧ i ≠ j := by
  rw [(momentCurve_baryon_parenthesizations t).2, smul_uZero_eq_zero_iff,
    _root_.neg_eq_zero, Matrix.det_vandermonde_eq_zero_iff]

/-- Reassociation preserves this triple precisely on the collision locus. -/
theorem momentCurve_parenthesizations_eq_iff_collision (t : Fin 3 → R) :
    mul (mul (offDiagonal 0 (momentCurve (t 0)))
        (offDiagonal 0 (momentCurve (t 1))))
        (offDiagonal 0 (momentCurve (t 2))) =
      mul (offDiagonal 0 (momentCurve (t 0)))
        (mul (offDiagonal 0 (momentCurve (t 1)))
          (offDiagonal 0 (momentCurve (t 2)))) ↔
      ∃ i j : Fin 3, t i = t j ∧ i ≠ j := by
  rw [(momentCurve_baryon_parenthesizations t).1,
    (momentCurve_baryon_parenthesizations t).2, smul_singlets_eq_iff,
    _root_.neg_eq_zero, Matrix.det_vandermonde_eq_zero_iff]

end Domain

end InfoGeometry.Canonical.GunaydinGursey
