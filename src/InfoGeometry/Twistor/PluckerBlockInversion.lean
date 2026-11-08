/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerInfinityChart
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Block exchange and inversion in the Plücker graph chart

Exchanging the two two-dimensional blocks of a four-vector induces an
involution on its exterior-square coordinates.  This exchanges origin and
infinity and induces matrix inversion wherever the matrix is invertible.
The block exchange and the infinity-twistor functional are distinct objects.
-/

namespace InfoGeometry.Twistor.PluckerBlockInversion

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.PluckerInfinityChart
open InfoGeometry.Canonical.MatrixTwoNoncommutativity

section Ring

variable {R : Type*} [CommRing R]

/-- Exchange the upper and lower two-dimensional blocks. -/
def blockSwapVec (Z : Vec4 R) : Vec4 R := ⟨Z.x2, Z.x3, Z.x0, Z.x1⟩

/-- Exterior-square coordinate action of `blockSwapVec`. -/
def blockSwapPlucker (P : Plucker6 R) : Plucker6 R :=
  ⟨P.p23, -P.p02, -P.p12, -P.p03, -P.p13, P.p01⟩

theorem blockSwapPlucker_pluckerLine (Z W : Vec4 R) :
    blockSwapPlucker (pluckerLine Z W) =
      pluckerLine (blockSwapVec Z) (blockSwapVec W) := by
  apply Plucker6.ext <;> simp [blockSwapPlucker, blockSwapVec, pluckerLine]

omit [CommRing R] in
@[simp] theorem blockSwapVec_involutive (Z : Vec4 R) :
    blockSwapVec (blockSwapVec Z) = Z := by cases Z; rfl

@[simp] theorem blockSwapPlucker_involutive (P : Plucker6 R) :
    blockSwapPlucker (blockSwapPlucker P) = P := by
  cases P
  simp [blockSwapPlucker]

@[simp] theorem blockSwapPlucker_p23 (P : Plucker6 R) :
    (blockSwapPlucker P).p23 = P.p01 := rfl

theorem blockSwapPlucker_scale (l : R) (P : Plucker6 R) :
    blockSwapPlucker (scale l P) = scale l (blockSwapPlucker P) := by
  apply Plucker6.ext <;> simp [blockSwapPlucker, scale]

@[simp] theorem kleinQ_blockSwapPlucker (P : Plucker6 R) :
    kleinQ (blockSwapPlucker P) = kleinQ P := by
  simp [kleinQ, blockSwapPlucker]
  ring

theorem kleinPolar_blockSwapPlucker (P Q : Plucker6 R) :
    kleinPolar (blockSwapPlucker P) (blockSwapPlucker Q) = kleinPolar P Q := by
  simp [kleinPolar, blockSwapPlucker]
  ring

/-- The decomposable upper spinor plane, opposite the finite chart origin. -/
def infinityPlucker : Plucker6 R :=
  pluckerLine ⟨1, 0, 0, 0⟩ ⟨0, 1, 0, 0⟩

theorem infinityPlucker_coordinates :
    infinityPlucker (R := R) = ⟨1, 0, 0, 0, 0, 0⟩ := by
  apply Plucker6.ext <;> simp [infinityPlucker, pluckerLine]

/-- The finite-chart covector is the Klein-polar dual of the infinity plane. -/
@[simp] theorem kleinPolar_infinityPlucker (P : Plucker6 R) :
    kleinPolar P infinityPlucker = P.p23 := by
  simp [kleinPolar, infinityPlucker_coordinates]

@[simp] theorem kleinQ_infinityPlucker : kleinQ (infinityPlucker (R := R)) = 0 :=
  kleinQ_pluckerLine _ _

@[simp] theorem infinityPlucker_p23 : (infinityPlucker (R := R)).p23 = 0 := by
  rw [infinityPlucker_coordinates]

theorem blockSwapPlucker_origin :
    blockSwapPlucker (graphPlucker (0 : Matrix (Fin 2) (Fin 2) R)) =
      infinityPlucker := by
  apply Plucker6.ext <;>
    simp [blockSwapPlucker, graphPlucker_coordinates, infinityPlucker_coordinates]

theorem blockSwapPlucker_infinity :
    blockSwapPlucker (infinityPlucker (R := R)) = graphPlucker 0 := by
  rw [← blockSwapPlucker_origin, blockSwapPlucker_involutive]

/-- Both the graph chart and block inversion retain the order distinction
of the existing noncommuting matrix units on the same source carrier. -/
theorem blockSwapPlucker_retains_matrix_product_order [Nontrivial R] :
    blockSwapPlucker (graphPlucker (upperUnit (R := R) * lowerUnit)) ≠
      blockSwapPlucker (graphPlucker (lowerUnit * upperUnit)) := by
  intro h
  apply matrix_two_noncommutative (R := R)
  apply graphPlucker_injective
  simpa only [blockSwapPlucker_involutive] using congrArg blockSwapPlucker h

end Ring

section Field

variable {R : Type*} [Field R]

/-- The homogeneous scale introduced by inversion is exactly the determinant. -/
theorem blockSwapPlucker_graphPlucker (X : Matrix (Fin 2) (Fin 2) R)
    (hX : X.det ≠ 0) :
    blockSwapPlucker (graphPlucker X) = scale X.det (graphPlucker X⁻¹) := by
  apply Plucker6.ext
  · simp [blockSwapPlucker, graphPlucker_coordinates, scale,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hX]
  all_goals
    simp [blockSwapPlucker, graphPlucker_coordinates, scale,
      Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two] <;>
      field_simp [hX]

/-- The determinant interval has conformal weight minus one in each endpoint. -/
theorem det_inv_sub_inv (X Y : Matrix (Fin 2) (Fin 2) R)
    (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    (X⁻¹ - Y⁻¹).det = (X - Y).det / (X.det * Y.det) := by
  have h := kleinPolar_blockSwapPlucker (graphPlucker X) (graphPlucker Y)
  rw [blockSwapPlucker_graphPlucker X hX, blockSwapPlucker_graphPlucker Y hY,
    kleinPolar_scale_left, kleinPolar_scale_right, kleinPolar_graphPlucker,
    kleinPolar_graphPlucker] at h
  apply (eq_div_iff (mul_ne_zero hX hY)).2
  calc
    (X⁻¹ - Y⁻¹).det * (X.det * Y.det) =
        X.det * (Y.det * (X⁻¹ - Y⁻¹).det) := by ring
    _ = (X - Y).det := h

end Field

end InfoGeometry.Twistor.PluckerBlockInversion
