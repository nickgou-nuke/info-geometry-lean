import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# 8-dimensional scalar-scaling Jacobian for Zorn coordinates

A concrete Zorn cell has eight scalar coordinates.  Uniform scalar scaling on
these coordinates is represented by the diagonal `8×8` matrix with scalar `u`
on every diagonal entry.  Its determinant is `u^8`.
-/

namespace InfoGeometry.Algebra.Zorn

/-- The `8×8` coordinate matrix for uniform scalar scaling on Zorn coordinates. -/
def scalarJacobianMatrix8 {R : Type*} [CommRing R] (u : R) : Matrix (Fin 8) (Fin 8) R :=
  Matrix.diagonal (fun _ : Fin 8 => u)

/-- The coordinate-volume Jacobian of uniform scalar scaling on eight Zorn coordinates. -/
def scalarJacobian8 {R : Type*} [CommRing R] (u : R) : R :=
  Matrix.det (scalarJacobianMatrix8 u)

/-- The determinant of the `8×8` scalar-scaling matrix is `u^8`. -/
theorem det_scalarJacobianMatrix8 {R : Type*} [CommRing R] (u : R) :
    Matrix.det (scalarJacobianMatrix8 u) = u ^ 8 := by
  simp [scalarJacobianMatrix8, Matrix.det_diagonal]

/-- Readback form: the scalar coordinate-volume Jacobian is `u^8`. -/
theorem scalarJacobian8_eq_pow {R : Type*} [CommRing R] (u : R) :
    scalarJacobian8 u = u ^ 8 :=
  det_scalarJacobianMatrix8 u

/-- For a unit scale, the eight-coordinate scalar Jacobian is nonzero. -/
theorem scalarJacobian8_ne_zero_of_unit {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (u : Rˣ) :
    scalarJacobian8 (u : R) ≠ 0 := by
  rw [scalarJacobian8_eq_pow]
  exact pow_ne_zero 8 (Units.ne_zero u)

end InfoGeometry.Algebra.Zorn
