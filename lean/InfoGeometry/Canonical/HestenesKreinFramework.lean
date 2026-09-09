import InfoGeometry.Canonical.HestenesCircularSheetCARFinite

/-!
# Hestenes local Krein structure

This is the finite local Krein layer over the Pauli sheet realization.  It
records the fundamental symmetry, its Krein adjoint, and sheet exchange.  The
identification with native Clifford reverse is intentionally a separate bridge
 theorem.
-/

noncomputable section
namespace HestenesKreinFramework

open TwoSheetThreeColorWeyl
open HestenesCircularSheetCAR

abbrev Sheet := M2C

def fundamentalSymmetry : Sheet := sheetFlip

def kreinAdjoint (A : Sheet) : Sheet :=
  fundamentalSymmetry * Matrix.conjTranspose A * fundamentalSymmetry

@[simp] theorem fundamentalSymmetry_sq :
    fundamentalSymmetry * fundamentalSymmetry = (1 : Sheet) := by
  exact sheet_parity.2.1

theorem fundamentalSymmetry_selfAdjoint :
    Matrix.conjTranspose fundamentalSymmetry = fundamentalSymmetry := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fundamentalSymmetry, sheetFlip]

@[simp] theorem kreinAdjoint_zero : kreinAdjoint (0 : Sheet) = 0 := by
  simp [kreinAdjoint]

@[simp] theorem kreinAdjoint_add (A B : Sheet) :
    kreinAdjoint (A + B) = kreinAdjoint A + kreinAdjoint B := by
  simp [kreinAdjoint, Matrix.conjTranspose_add, Matrix.mul_add, add_mul]

@[simp] theorem kreinAdjoint_smul (c : ℂ) (A : Sheet) :
    kreinAdjoint (c • A) = starRingEnd ℂ c • kreinAdjoint A := by
  simp [kreinAdjoint, Matrix.conjTranspose_smul, smul_mul_assoc,
    mul_smul_comm]

@[simp] theorem kreinAdjoint_involutive (A : Sheet) :
    kreinAdjoint (kreinAdjoint A) = A := by
  unfold kreinAdjoint
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    fundamentalSymmetry_selfAdjoint]
  simp only [Matrix.conjTranspose_conjTranspose]
  calc
    fundamentalSymmetry *
          (fundamentalSymmetry * (A * fundamentalSymmetry)) * fundamentalSymmetry =
        (fundamentalSymmetry * fundamentalSymmetry) * A *
          (fundamentalSymmetry * fundamentalSymmetry) := by noncomm_ring
    _ = A := by simp [fundamentalSymmetry_sq]

@[simp] theorem kreinAdjoint_fundamentalSymmetry :
    kreinAdjoint fundamentalSymmetry = fundamentalSymmetry := by
  simp [kreinAdjoint, fundamentalSymmetry_selfAdjoint,
    fundamentalSymmetry_sq]

@[simp] theorem fundamentalSymmetry_uPlus_fundamentalSymmetry :
    fundamentalSymmetry * uPlus * fundamentalSymmetry = uMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fundamentalSymmetry, uPlus, uMinus, sheetFlip, sheetGamma,
      sheetPlus, sheetMinus, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] <;> norm_num

@[simp] theorem fundamentalSymmetry_uMinus_fundamentalSymmetry :
    fundamentalSymmetry * uMinus * fundamentalSymmetry = uPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fundamentalSymmetry, uPlus, uMinus, sheetFlip, sheetGamma,
      sheetPlus, sheetMinus, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] <;> norm_num

end HestenesKreinFramework
end noncomputable section
