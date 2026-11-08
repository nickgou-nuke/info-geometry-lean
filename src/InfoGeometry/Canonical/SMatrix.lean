import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.SMatrix

open Complex

/-- A 2x2 Transfer Matrix. -/
structure TransferMatrix where
  m11 : ℂ
  m12 : ℂ
  m21 : ℂ
  m22 : ℂ

/-- A Transfer Matrix belonging to SL(2, ℂ), conserving pseudo-unitary volume. -/
structure SL2TransferMatrix extends TransferMatrix where
  det_eq_one : m11 * m22 - m12 * m21 = 1
  m22_ne_zero : m22 ≠ 0 -- Required to avoid singular scattering

/-- A 2x2 Scattering (S) Matrix. -/
structure ScatteringMatrix where
  t_R : ℂ
  r_L : ℂ
  r_R : ℂ
  t_L : ℂ

/-- 
Converts a Transfer Matrix into an S-Matrix.
Formally defines the relation between transfer and scattering formalisms.
-/
@[rep_depth thermo]
noncomputable def toSMatrix (M : TransferMatrix) : ScatteringMatrix := {
  t_R := 1 / M.m22
  r_L := -M.m12 / M.m22
  r_R := M.m21 / M.m22
  t_L := (M.m11 * M.m22 - M.m12 * M.m21) / M.m22
}

/-- 
Theorem: For any SL(2, ℂ) Transfer Matrix (where det M = 1), 
the transmission coefficients are reciprocal (t_R = t_L).
This proves the generalized pseudo-unitary conservation where transmission 
is symmetric despite the internal non-Hermitian geometry.
-/
@[rep_depth thermo]
theorem sl2_transmission_reciprocity (M : SL2TransferMatrix) :
    (toSMatrix M.toTransferMatrix).t_R = (toSMatrix M.toTransferMatrix).t_L := by
  dsimp [toSMatrix]
  have h_det : M.toTransferMatrix.m11 * M.toTransferMatrix.m22 - M.toTransferMatrix.m12 * M.toTransferMatrix.m21 = 1 := M.det_eq_one
  rw [h_det]

end InfoGeometry.Canonical.SMatrix

