import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The finite cyclotomic Clifford--Pauli system

This is the associative `3 × 3` qutrit operator lane.  It is kept separate
from the nonassociative native Zorn carrier: the clock/shift matrices below
are genuine endomorphisms, while a Zorn-grade charge requires a separately
constructed linear carrier.
-/

namespace InfoGeometry.Canonical

open Matrix

noncomputable section

def cubicRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

/-- The existing qutrit phase is a primitive third root of unity. -/
theorem cubicRoot_is_primitive_root : IsPrimitiveRoot cubicRoot 3 := by
  dsimp [cubicRoot]
  exact Complex.isPrimitiveRoot_exp 3 (by decide)

@[simp] theorem cubicRoot_pow_three : cubicRoot ^ 3 = 1 := by
  dsimp [cubicRoot]
  have hpow : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3) ^ 3 =
      Complex.exp ((3 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 3)) := by
    rw [← Complex.exp_nat_mul]
    norm_num
  have h : (3 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 3) =
      2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hpow, h, Complex.exp_two_pi_mul_I]

@[simp] theorem cubicRoot_mul_sq : cubicRoot * cubicRoot ^ 2 = 1 := by
  calc
    cubicRoot * cubicRoot ^ 2 = cubicRoot ^ 3 := by ring
    _ = 1 := cubicRoot_pow_three

def qutritClock : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, cubicRoot, 0;
     0, 0, cubicRoot ^ 2]

def qutritShift : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

@[simp] theorem qutritClock_cube :
    qutritClock ^ 3 = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have h3 : cubicRoot * (cubicRoot * cubicRoot) = 1 := by
    simpa [pow_three] using cubicRoot_pow_three
  have h6 : cubicRoot ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by norm_num, pow_mul, cubicRoot_pow_three]
    simp
  have h6' : cubicRoot * cubicRoot *
      (cubicRoot * cubicRoot * (cubicRoot * cubicRoot)) = 1 := by
    calc
      cubicRoot * cubicRoot *
          (cubicRoot * cubicRoot * (cubicRoot * cubicRoot)) =
          (cubicRoot * (cubicRoot * cubicRoot)) *
            (cubicRoot * (cubicRoot * cubicRoot)) := by ring
      _ = 1 := by rw [h3]; simp
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritClock, Matrix.mul_apply, Fin.sum_univ_succ,
      pow_succ, h3, h6, h6']

@[simp] theorem qutritShift_cube :
    qutritShift ^ 3 = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritShift, Matrix.mul_apply, Fin.sum_univ_succ]

theorem qutritClock_mul_shift :
    qutritClock * qutritShift =
      cubicRoot • (qutritShift * qutritClock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritClock, qutritShift, Matrix.mul_apply,
      Fin.sum_univ_succ, cubicRoot_mul_sq, pow_two,
      cubicRoot_pow_three] <;>
    try simpa [pow_succ, mul_assoc] using cubicRoot_pow_three.symm

theorem qutrit_clock_shift_commutator_phase :
    qutritClock * qutritShift - qutritShift * qutritClock =
      (cubicRoot - 1) • (qutritShift * qutritClock) := by
  rw [qutritClock_mul_shift]
  rw [sub_smul]
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

def qutritWeyl (a b : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  qutritClock ^ a * qutritShift ^ b

@[simp] theorem qutritWeyl_zero_zero :
    qutritWeyl 0 0 = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  simp [qutritWeyl]

end
end InfoGeometry.Canonical
