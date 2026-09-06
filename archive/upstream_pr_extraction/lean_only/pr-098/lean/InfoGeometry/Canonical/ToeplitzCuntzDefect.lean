import InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation

/-!
# The finite Toeplitz defect calculation

This is the one-mode matrix calculation.  It identifies the defect of the
creation matrix with the second diagonal projection.  It does not assert a
Toeplitz--Cuntz representation, an infinite tensor colimit, or a von Neumann
factor.
-/

namespace InfoGeometry.Canonical.MatrixRep

open InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation

abbrev S : M₂ := sigmaPlus

abbrev SStar : M₂ := sigmaMinus

def P0 : M₂ := 1 - S * SStar

@[simp] theorem toeplitz_cuntz_defect_is_vacuum :
    P0 = nMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, S, SStar, sigmaPlus, sigmaMinus, nMinus]

@[simp] theorem toeplitz_cuntz_identity_resolution :
    S * SStar + P0 = (1 : M₂) := by
  rw [P0]
  simp [sub_eq_add_neg, add_comm]

@[simp] theorem defect_null_space_annihilation :
    SStar * P0 = 0 := by
  rw [toeplitz_cuntz_defect_is_vacuum]
  exact sigmaMinus_mul_nMinus

end InfoGeometry.Canonical.MatrixRep
