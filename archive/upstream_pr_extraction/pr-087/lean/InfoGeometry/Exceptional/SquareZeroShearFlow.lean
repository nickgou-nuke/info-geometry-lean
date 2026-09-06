import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Module

/-!
# Exact algebra of a square-zero shear

These lemmas isolate the representation-dependent part of a parabolic flow.
No nilpotence of an abstract Lie-algebra radical is assumed: the hypothesis is
explicitly `N * N = 0` for the concrete endomorphism under study.
-/

namespace InfoGeometry.Exceptional.SquareZeroShear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Mat (ι : Type*) [Fintype ι] [DecidableEq ι] := Matrix ι ι ℝ

def shear (N : Mat ι) (t : ℝ) : Mat ι := 1 + t • N

theorem shear_mul (N : Mat ι) (hN : N * N = 0) (s t : ℝ) :
    shear N s * shear N t = shear N (s + t) := by
  simp only [shear, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    smul_mul_assoc, mul_smul_comm, hN, smul_zero, add_zero]
  module

theorem shear_inverse (N : Mat ι) (hN : N * N = 0) (t : ℝ) :
    shear N t * shear N (-t) = 1 := by
  rw [shear_mul N hN]
  simp [shear]

theorem shear_commute (N : Mat ι) (hN : N * N = 0) (s t : ℝ) :
    shear N s * shear N t = shear N t * shear N s := by
  rw [shear_mul N hN, shear_mul N hN, add_comm]

end InfoGeometry.Exceptional.SquareZeroShear
