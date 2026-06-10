import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

open scoped BigOperators

noncomputable section

namespace Section3

open Matrix

def s0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def sf : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3
def eta4 : Matrix (Fin 4) (Fin 4) ℂ := !![(-1),0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem trace_ortho (a b : Fin 4) : ((∑ i : Fin 2, (sf a * sf b) i i) / (2 : ℂ)) = if a = b then (1 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [sf, s0, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two]

theorem vec_recover (t x y z : ℂ) (a : Fin 4) :
    ((∑ i : Fin 2, (sf a * (t • s0 + x • s1 + y • s2 + z • s3)) i i) / (2 : ℂ))
    = match a with | 0 => t | 1 => x | 2 => y | 3 => z := by
  fin_cases a <;> simp [sf, s0, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two]
  · ring_nf
  · ring_nf
  · ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) by simp [pow_two, Complex.I_mul_I]]
    ring_nf
  · ring_nf

theorem completeness (A B Ap Bp : Fin 2) :
    (∑ a : Fin 4, ∑ b : Fin 4, eta4 a b * sf a A Ap * sf b B Bp) = (-2 : ℂ) * eps A B * eps Ap Bp := by
  fin_cases A <;> fin_cases B <;> fin_cases Ap <;> fin_cases Bp <;>
    simp [sf, s0, s1, s2, s3, eta4, eps, Fin.sum_univ_four] <;> ring

end Section3
