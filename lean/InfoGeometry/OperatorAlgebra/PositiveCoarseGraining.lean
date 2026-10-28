/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive operator coarse-graining

The exact elimination underlying Dimock's account of Balaban's block
renormalization is a rectangular, weighted Schur complement. Both precision
operators are arbitrary positive definite matrices; no operators are assumed
to commute. The coarse weight is itself matrix-valued.

The inverse formula below specializes Mathlib's Woodbury theorem. Positivity
establishes every inverse hypothesis, including positivity of the resulting
coarse precision. This is finite operator algebra, without an assertion about
polymer expansions or continuum limits.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PositiveCoarseGraining

open Matrix
open scoped ComplexOrder

variable {𝕜 n m : Type*} [RCLike 𝕜]
variable [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Fine precision after imposing a matrix-weighted coarse observation. -/
def finePrecision (A : Matrix n n 𝕜) (R : Matrix m m 𝕜)
    (Q : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  A + Qᴴ * R * Q

/-- Coarse covariance: observation covariance plus transported fine covariance. -/
def coarseCovariance (A : Matrix n n 𝕜) (R : Matrix m m 𝕜)
    (Q : Matrix m n 𝕜) : Matrix m m 𝕜 :=
  R⁻¹ + Q * A⁻¹ * Qᴴ

/-- The effective precision obtained by eliminating the fine variables. -/
def coarsePrecision (A : Matrix n n 𝕜) (R : Matrix m m 𝕜)
    (Q : Matrix m n 𝕜) : Matrix m m 𝕜 :=
  R - R * Q * (finePrecision A R Q)⁻¹ * Qᴴ * R

/-- The fine state that solves the normal equation for a coarse state. -/
def harmonicExtension (A : Matrix n n 𝕜) (R : Matrix m m 𝕜)
    (Q : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  (finePrecision A R Q)⁻¹ * Qᴴ * R

variable {A : Matrix n n 𝕜} {R : Matrix m m 𝕜} (Q : Matrix m n 𝕜)

omit [DecidableEq n] [DecidableEq m] in
theorem finePrecision_posDef (hA : A.PosDef) (hR : R.PosDef) :
    (finePrecision A R Q).PosDef :=
  hA.add_posSemidef (hR.posSemidef.conjTranspose_mul_mul_same Q)

theorem coarseCovariance_posDef (hA : A.PosDef) (hR : R.PosDef) :
    (coarseCovariance A R Q).PosDef :=
  hR.inv.add_posSemidef (hA.inv.posSemidef.mul_mul_conjTranspose_same Q)

/-- Woodbury with the covariance operators as its two invertible inputs. -/
theorem coarseCovariance_inv (hA : A.PosDef) (hR : R.PosDef) :
    (coarseCovariance A R Q)⁻¹ = coarsePrecision A R Q := by
  let := hA.isUnit.invertible
  let := hR.isUnit.invertible
  have hH := finePrecision_posDef Q hA hR
  have hInv : IsUnit (A⁻¹⁻¹ + Qᴴ * R⁻¹⁻¹ * Q) := by
    simpa only [Matrix.inv_inv_of_invertible, finePrecision] using hH.isUnit
  simpa only [coarseCovariance, coarsePrecision, finePrecision,
    Matrix.inv_inv_of_invertible, Matrix.mul_assoc] using
    Matrix.add_mul_mul_inv_eq_sub R⁻¹ Q A⁻¹ Qᴴ hR.inv.isUnit hA.inv.isUnit hInv

theorem coarsePrecision_posDef (hA : A.PosDef) (hR : R.PosDef) :
    (coarsePrecision A R Q).PosDef := by
  rw [← coarseCovariance_inv Q hA hR]
  exact (coarseCovariance_posDef Q hA hR).inv

/-- Exact covariance transport, valid without any commutation hypothesis. -/
theorem coarsePrecision_inv (hA : A.PosDef) (hR : R.PosDef) :
    (coarsePrecision A R Q)⁻¹ = R⁻¹ + Q * A⁻¹ * Qᴴ := by
  let := (coarseCovariance_posDef Q hA hR).isUnit.invertible
  rw [← coarseCovariance_inv Q hA hR, Matrix.inv_inv_of_invertible]
  rfl

/-- The dual Woodbury formula for the conditioned fine covariance. -/
theorem finePrecision_inv (hA : A.PosDef) (hR : R.PosDef) :
    (finePrecision A R Q)⁻¹ =
      A⁻¹ - A⁻¹ * Qᴴ * coarsePrecision A R Q * Q * A⁻¹ := by
  have hC := coarseCovariance_posDef Q hA hR
  change (A + Qᴴ * R * Q)⁻¹ = _
  rw [Matrix.add_mul_mul_inv_eq_sub A Qᴴ R Q hA.isUnit hR.isUnit hC.isUnit]
  rw [show (R⁻¹ + Q * A⁻¹ * Qᴴ)⁻¹ = coarsePrecision A R Q from
    coarseCovariance_inv Q hA hR]

omit [DecidableEq m] in
/-- The actual matrix normal equation for harmonic extension. -/
theorem finePrecision_mul_harmonicExtension (hA : A.PosDef) (hR : R.PosDef) :
    finePrecision A R Q * harmonicExtension A R Q = Qᴴ * R := by
  let := (finePrecision_posDef Q hA hR).isUnit.invertible
  simp only [harmonicExtension, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
    Matrix.one_mul]

omit [DecidableEq m] in
/-- Adjoint normal equation; the order of the factors is reversed by the adjoint. -/
theorem harmonicExtension_adjoint_mul_finePrecision (hA : A.PosDef) (hR : R.PosDef) :
    (harmonicExtension A R Q)ᴴ * finePrecision A R Q = R * Q := by
  have h := congrArg Matrix.conjTranspose (finePrecision_mul_harmonicExtension Q hA hR)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hR.isHermitian.eq, (finePrecision_posDef Q hA hR).isHermitian.eq] using h

omit [DecidableEq m] in
/-- The Schur complement can also be read directly from the response map. -/
theorem coarsePrecision_eq_sub_response :
    coarsePrecision A R Q = R - R * Q * harmonicExtension A R Q := by
  simp only [coarsePrecision, harmonicExtension, Matrix.mul_assoc]

end InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
