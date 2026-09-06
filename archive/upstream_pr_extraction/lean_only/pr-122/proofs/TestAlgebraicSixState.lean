import proofs.SixStateGeneralizedPauliBasis
import Mathlib.Tactic.Ring

open SixStateGeneralizedPauliBasis
open Matrix

lemma sheetFlip_sq : sheetFlip ^ 2 = (1 : M2C) := by
  rw [sq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sheetFlip, Matrix.mul_apply, Matrix.one_apply] <;> ring

lemma sheetGamma_sq : sheetGamma ^ 2 = (1 : M2C) := by
  rw [sq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sheetGamma, sheetPlus, sheetMinus, Matrix.mul_apply, Matrix.one_apply] <;> ring

lemma sheetGamma_Flip : sheetGamma * sheetFlip = - (sheetFlip * sheetGamma) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sheetGamma, sheetPlus, sheetMinus, sheetFlip, Matrix.mul_apply] <;> ring
