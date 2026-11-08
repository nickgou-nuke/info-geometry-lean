import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open Matrix

local notation "RealMat" => Matrix (Fin 2) (Fin 2) ℝ

def matOneR : RealMat := !![1, 0; 0, 1]

example (D : RealMat) (h_chiral : D * matOneR + matOneR * D = 0) : D 0 0 = 0 := by
  have h := congr_arg (fun M => M 0 0) h_chiral
  simp only [matOneR, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one] at h
  linarith
