/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.QuaternionCayley
import InfoGeometry.Clifford.SplitAtomDoubling
import InfoGeometry.Geometry.AssociativeGaugeConnection

/-!
# Quaternion frame from the existing sign-twisted doubling

The carrier is `M₂(M₂(A))` over an arbitrary ring. The two negative-square
generators are the existing outer negative generator and the sign-twisted
inner negative generator. This imports the established doubling maps rather
than introducing a second Clifford presentation.

The frame gives exact quaternion relations and an explicit constant-connection
curvature. Actual factor conjugation uses an invertible `2`. All frame and
curvature statements retain their indicated matrix carrier; no compact Lie
classification, universal Clifford equivalence, or analytic limit is claimed.
-/

namespace InfoGeometry.Clifford.SplitQuaternionCurvature

open SplitAtomDoubling
open InfoGeometry.Algebra.QuaternionCayley
open InfoGeometry.Geometry.AssociativeGaugeConnection

variable {A : Type*} [Ring A]

abbrev Double (A : Type*) := Block2 (Block2 A)

/-- The outer negative-square generator, in the repository's sign convention. -/
def axisI : Double A := negative

/-- The old negative-square generator acquires the existing Klein sign twist. -/
def axisJ : Double A := twisted (negative : Block2 A)

/-- The ordered product fixes the orientation of the quaternion frame. -/
def axisK : Double A := axisI * axisJ

@[simp] theorem axisI_square : (axisI : Double A) * axisI = -1 :=
  negative_square

@[simp] theorem axisJ_square : (axisJ : Double A) * axisJ = -1 := by
  rw [axisJ, twisted_mul, negative_square]
  change repeatedHom (-1 : Block2 A) = -1
  simp

theorem axisJ_mul_axisI : (axisJ : Double A) * axisI = -axisK := by
  apply eq_neg_iff_add_eq_zero.mpr
  exact twisted_negative_anticommutator (negative : Block2 A)

@[simp] theorem axisK_square : (axisK : Double A) * axisK = -1 :=
  product_square axisI axisJ axisI_square axisJ_square axisJ_mul_axisI

@[simp] theorem axisJ_mul_axisK : (axisJ : Double A) * axisK = axisI :=
  second_mul_product axisI axisJ axisJ_square axisJ_mul_axisI

@[simp] theorem axisK_mul_axisI : (axisK : Double A) * axisI = axisJ :=
  product_mul_first axisI axisJ axisI_square axisJ_mul_axisI

@[simp] theorem axisI_mul_axisK : (axisI : Double A) * axisK = -axisJ :=
  first_mul_product axisI axisJ axisI_square

@[simp] theorem axisK_mul_axisJ : (axisK : Double A) * axisJ = -axisI :=
  product_mul_second axisI axisJ axisJ_square

theorem commutator_ij :
    (axisI : Double A) * axisJ - axisJ * axisI = 2 * axisK := by
  rw [axisJ_mul_axisI]
  change axisK - -axisK = 2 * axisK
  noncomm_ring

theorem commutator_jk :
    (axisJ : Double A) * axisK - axisK * axisJ = 2 * axisI := by
  rw [axisJ_mul_axisK, axisK_mul_axisJ]
  noncomm_ring

theorem commutator_ki :
    (axisK : Double A) * axisI - axisI * axisK = 2 * axisJ := by
  rw [axisK_mul_axisI, axisI_mul_axisK]
  noncomm_ring

theorem axis_factor_commutator :
    (1 + (axisI : Double A)) * (1 + axisJ) -
      (1 + axisJ) * (1 + axisI) = 2 * axisK :=
  factor_commutator axisI axisJ axisJ_mul_axisI

theorem axis_factor_sandwich :
    (1 + (axisI : Double A)) * axisJ * (1 - axisI) = 2 * axisK :=
  factor_sandwich axisI axisJ axisI_square axisJ_mul_axisI

/-- Noncommutation is proved whenever the coefficient ring has `2 ≠ 0`. -/
theorem axis_factors_not_commute (h2 : (2 : A) ≠ 0) :
    ¬ Commute (1 + (axisI : Double A)) (1 + axisJ) := by
  rw [factors_commute_iff axisI axisJ axisI_square axisJ_square axisJ_mul_axisI]
  intro h
  have hentry := congrArg (fun M : Double A => M 0 0 0 0) h
  exact h2 (by simpa [Matrix.ofNat_apply] using hentry)

theorem axis_factor_conjugate [Invertible (2 : Double A)] :
    (factorUnit (axisI : Double A) axisI_square : Double A) * axisJ *
      (↑(factorUnit (axisI : Double A) axisI_square)⁻¹ : Double A) = axisK :=
  factorUnit_conjugate axisI axisJ axisI_square axisJ_mul_axisI

/-- Vanishing frame derivatives are explicit; they are not assumed for arbitrary
derivations of the whole matrix algebra. -/
theorem frame_curvature (D E : Module.End ℤ (Double A))
    (hD : D axisJ = 0) (hE : E axisI = 0) :
    curvature D E axisI axisJ = 2 * axisK := by
  simp only [curvature, hD, hE, sub_zero, zero_add]
  exact commutator_ij

theorem constant_frame_curvature :
    curvature (0 : Module.End ℤ (Double A)) 0 axisI axisJ = 2 * axisK :=
  frame_curvature 0 0 rfl rfl

/-- The quaternion curvature acts on the full noncommutative matrix carrier. -/
theorem constant_frame_curvature_action (X : Double A) :
    covariantDerivative (0 : Module.End ℤ (Double A)) axisI
        (covariantDerivative (R := ℤ) 0 axisJ X) -
      covariantDerivative (R := ℤ) 0 axisJ (covariantDerivative (R := ℤ) 0 axisI X) =
        (2 * axisK) * X := by
  rw [curvature_action (0 : Module.End ℤ (Double A)) 0
    (by intro x y; simp) (by intro x y; simp)
    (by intro x; rfl), constant_frame_curvature]

/-- Existing finite gauge covariance transports this concrete curvature. -/
theorem gauge_frame_curvature (u : (Double A)ˣ) :
    curvature (0 : Module.End ℤ (Double A)) 0
      (gaugePotential (R := ℤ) 0 axisI u) (gaugePotential (R := ℤ) 0 axisJ u) =
        conjugate u (2 * axisK) := by
  rw [curvature_gauge_covariant (0 : Module.End ℤ (Double A)) 0 (by intro x y; simp)
    (by intro x y; simp) (by intro x; rfl), constant_frame_curvature]

end InfoGeometry.Clifford.SplitQuaternionCurvature
