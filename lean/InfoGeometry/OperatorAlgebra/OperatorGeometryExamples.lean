/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Star.StarProjection
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Quantum.KrausAmplificationCP

/-!
# Noncommuting witnesses for projection geometry and Kraus channels

The projections and Kraus operators below have nonzero off-diagonal entries.
The examples use the existing Peirce projections and Kraus map on the full
complex matrix algebra. Off-diagonal extraction fails positivity, and a
complete noncommuting Kraus family need not define an algebra homomorphism.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorGeometryExamples

open Matrix
open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Quantum.Choi
open scoped ComplexOrder

local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

/-- A nondiagonal rank-one orthogonal projection. -/
def P : Mat := !![1 / 5, 2 / 5; 2 / 5, 4 / 5]

/-- A second nondiagonal rank-one orthogonal projection. -/
def Q : Mat := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

theorem P_isStarProjection : IsStarProjection P := by
  constructor
  · change P * P = P
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Matrix.mul_apply, Fin.sum_univ_two]
  · change star P = P
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Matrix.star_apply]

theorem Q_isStarProjection : IsStarProjection Q := by
  constructor
  · change Q * Q = Q
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q, Matrix.mul_apply, Fin.sum_univ_two]
  · change star Q = Q
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q, Matrix.star_apply]

theorem projection_commutator_entry :
    (P * Q - Q * P) 0 1 = (-3 / 10 : ℂ) := by
  norm_num [P, Q, Matrix.mul_apply, Fin.sum_univ_two]

theorem projections_not_commute : ¬ Commute P Q := by
  intro h
  have hz : (P * Q - Q * P) 0 1 = 0 := by rw [h.eq, sub_self]; rfl
  rw [projection_commutator_entry] at hz
  norm_num at hz

theorem oddPart_P_Q :
    oddPart P Q = !![6 / 25, 9 / 50; 9 / 50, -6 / 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oddPart, component10, component01, complementIdempotent,
      P, Q, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem Q_posSemidef : Q.PosSemidef := by
  have hQQ : Qᴴ * Q = Q := by
    change star Q * Q = Q
    rw [Q_isStarProjection.isSelfAdjoint.star_eq]
    exact Q_isStarProjection.isIdempotentElem
  simpa only [hQQ] using Matrix.posSemidef_conjTranspose_mul_self Q

/-- An orthogonal projection of the operator vector space need not preserve
the positive-semidefinite cone of matrices. -/
theorem oddPart_Q_not_posSemidef : ¬ (oddPart P Q).PosSemidef := by
  intro h
  have hdiag := h.diag_nonneg (i := (1 : Fin 2))
  rw [oddPart_P_Q] at hdiag
  have hre := (Complex.nonneg_iff.mp hdiag).1
  norm_num at hre

/-- A finite complete Kraus family whose two operators do not commute. -/
def V : Fin 2 → Mat :=
  ![!![0, 3 / 5; 3 / 5, 0], !![12 / 25, 16 / 25; 16 / 25, -12 / 25]]

theorem V_complete : (∑ i : Fin 2, star (V i) * V i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [V, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofNat,
      Fin.sum_univ_two]

theorem kraus_commutator_entry :
    (V 0 * V 1 - V 1 * V 0) 0 1 = (-72 / 125 : ℂ) := by
  norm_num [V, Matrix.mul_apply, Fin.sum_univ_two]

theorem kraus_operators_not_commute : ¬ Commute (V 0) (V 1) := by
  intro h
  have hz : (V 0 * V 1 - V 1 * V 0) 0 1 = 0 := by rw [h.eq, sub_self]; rfl
  rw [kraus_commutator_entry] at hz
  norm_num at hz

theorem image_commutator_entry :
    (krausMap V P * krausMap V Q - krausMap V Q * krausMap V P) 0 1 =
      (31323 / 156250 : ℂ) := by
  norm_num [krausMap, V, P, Q, Matrix.mul_apply, Matrix.star_apply,
    Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail,
    Complex.conj_ofNat, Fin.sum_univ_two]

theorem kraus_images_not_commute : ¬ Commute (krausMap V P) (krausMap V Q) := by
  intro h
  have hz : (krausMap V P * krausMap V Q - krausMap V Q * krausMap V P) 0 1 = 0 := by
    rw [h.eq, sub_self]; rfl
  rw [image_commutator_entry] at hz
  norm_num at hz

theorem multiplicativity_defect_entry :
    (krausMap V (P * Q) - krausMap V P * krausMap V Q) 0 0 =
      (5184 / 78125 : ℂ) := by
  norm_num [krausMap, V, P, Q, Matrix.mul_apply, Matrix.star_apply,
    Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail,
    Complex.conj_ofNat, Fin.sum_univ_two]

theorem krausMap_not_multiplicative :
    krausMap V (P * Q) ≠ krausMap V P * krausMap V Q := by
  intro h
  have hz : (krausMap V (P * Q) - krausMap V P * krausMap V Q) 0 0 = 0 := by
    rw [h, sub_self]; rfl
  rw [multiplicativity_defect_entry] at hz
  norm_num at hz

/-- The counterexample above is genuinely about multi-Kraus mixing: a single
Kraus operator satisfying `Uᴴ U = 1` gives a multiplicative map.  This states
the correct positive boundary without claiming every complete Kraus channel
is an algebra homomorphism. -/
theorem single_isometric_kraus_multiplicative (U : Mat)
    (hU : star U * U = 1) (X Y : Mat) :
    krausMap (fun _ : Unit => U) (X * Y) =
      krausMap (fun _ : Unit => U) X * krausMap (fun _ : Unit => U) Y := by
  have hsingle (Z : Mat) : krausMap (fun _ : Unit => U) Z = U * Z * star U := by
    simp [krausMap]
  rw [hsingle (X * Y), hsingle X, hsingle Y]
  calc
    U * (X * Y) * star U = U * X * (Y * star U) := by noncomm_ring
    _ = U * X * (star U * U) * (Y * star U) := by rw [hU]; simp
    _ = (U * X * star U) * (U * Y * star U) := by noncomm_ring

end InfoGeometry.OperatorAlgebra.OperatorGeometryExamples

end
