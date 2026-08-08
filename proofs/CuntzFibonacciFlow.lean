import Mathlib
import proofs.CuntzEndomorphism
import proofs.CuntzZornIntegration

noncomputable section

namespace CuntzFibonacciFlow

open CuntzEndomorphism
open CuntzZornIntegration
open Matrix
open ZornCore

variable {A : Type*} [Ring A] [StarRing A]
variable (S₁ S₂ : A) [hC : CuntzO2 S₁ S₂]

theorem CuntzFibonacciOperator_mul_inverse :
    CuntzFibonacciOperator S₁ S₂ * (CuntzFibonacciOperator S₁ S₂ - 1) = 1 := by
  calc
    CuntzFibonacciOperator S₁ S₂ * (CuntzFibonacciOperator S₁ S₂ - 1)
      = CuntzFibonacciOperator S₁ S₂ * CuntzFibonacciOperator S₁ S₂ - CuntzFibonacciOperator S₁ S₂ := by rw [mul_sub, mul_one]
    _ = 1 + CuntzFibonacciOperator S₁ S₂ - CuntzFibonacciOperator S₁ S₂ := by rw [CuntzFibonacciOperator_fusion]
    _ = 1 := by abel

theorem CuntzFibonacciOperator_inverse_mul :
    (CuntzFibonacciOperator S₁ S₂ - 1) * CuntzFibonacciOperator S₁ S₂ = 1 := by
  calc
    (CuntzFibonacciOperator S₁ S₂ - 1) * CuntzFibonacciOperator S₁ S₂
      = CuntzFibonacciOperator S₁ S₂ * CuntzFibonacciOperator S₁ S₂ - CuntzFibonacciOperator S₁ S₂ := by rw [sub_mul, one_mul]
    _ = 1 + CuntzFibonacciOperator S₁ S₂ - CuntzFibonacciOperator S₁ S₂ := by rw [CuntzFibonacciOperator_fusion]
    _ = 1 := by abel

/-- The Fibonacci Operator bundled as an invertible element. -/
def CuntzFibonacciUnit : Aˣ where
  val := CuntzFibonacciOperator S₁ S₂
  inv := CuntzFibonacciOperator S₁ S₂ - 1
  val_inv := CuntzFibonacciOperator_mul_inverse S₁ S₂
  inv_val := CuntzFibonacciOperator_inverse_mul S₁ S₂

/-- Discrete Z-dynamics: The Endomorphism Flow. -/
def fibonacciFlow (n : ℤ) (a : A) : A :=
  (CuntzFibonacciUnit S₁ S₂ ^ n).val * a * (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val

/-- Fibonacci normal form for positive powers: X^n = F_{n-1} 1 + F_n X. -/
theorem CuntzFibonacciOperator_pow_normal_form (n : ℕ) :
    (CuntzFibonacciOperator S₁ S₂) ^ (n + 1) =
      (Nat.fib n : A) + (Nat.fib (n + 1) : A) * CuntzFibonacciOperator S₁ S₂ := by
  induction' n with k ih
  · simp
  · calc
      (CuntzFibonacciOperator S₁ S₂) ^ (k + 1 + 1) = (CuntzFibonacciOperator S₁ S₂) ^ (k + 1) * CuntzFibonacciOperator S₁ S₂ := pow_succ _ _
      _ = ((Nat.fib k : A) + (Nat.fib (k + 1) : A) * CuntzFibonacciOperator S₁ S₂) * CuntzFibonacciOperator S₁ S₂ := by rw [ih]
      _ = (Nat.fib k : A) * CuntzFibonacciOperator S₁ S₂ + (Nat.fib (k + 1) : A) * (CuntzFibonacciOperator S₁ S₂ * CuntzFibonacciOperator S₁ S₂) := by
        rw [add_mul, mul_assoc]
      _ = (Nat.fib k : A) * CuntzFibonacciOperator S₁ S₂ + (Nat.fib (k + 1) : A) * (1 + CuntzFibonacciOperator S₁ S₂) := by rw [CuntzFibonacciOperator_fusion]
      _ = (Nat.fib k : A) * CuntzFibonacciOperator S₁ S₂ + ((Nat.fib (k + 1) : A) * 1 + (Nat.fib (k + 1) : A) * CuntzFibonacciOperator S₁ S₂) := by
        rw [mul_add]
      _ = (Nat.fib k : A) * CuntzFibonacciOperator S₁ S₂ + (Nat.fib (k + 1) : A) + (Nat.fib (k + 1) : A) * CuntzFibonacciOperator S₁ S₂ := by
        rw [mul_one, ← add_assoc]
      _ = (Nat.fib (k + 1) : A) + ((Nat.fib k : A) + (Nat.fib (k + 1) : A)) * CuntzFibonacciOperator S₁ S₂ := by
        noncomm_ring
      _ = (Nat.fib (k + 1) : A) + (Nat.fib (k + 2) : A) * CuntzFibonacciOperator S₁ S₂ := by
        have hfib : (Nat.fib (k + 2) : A) = ((Nat.fib (k + 1) + Nat.fib k : ℕ) : A) := by
          rw [Nat.fib_add_two, add_comm]
        have hcast : (((Nat.fib (k + 1) + Nat.fib k : ℕ) : A)) = (Nat.fib (k + 1) : A) + (Nat.fib k : A) := by
          exact Nat.cast_add _ _
        rw [hfib, hcast]
        noncomm_ring

abbrev Matrix2x2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The inverse of the local Fibonacci matrix. -/
def fibonacciMatrixInv : Matrix2x2 :=
  FibonacciLocalMatrix - 1

theorem fibonacciMatrix_inv_mul :
    fibonacciMatrixInv * FibonacciLocalMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fibonacciMatrixInv, FibonacciLocalMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]

/-- The inverse of the Zorn embedded Fibonacci element. -/
theorem fibonacciZorn_inv (e : Vec3) (he : dot e e = 1) (hx : cross e e = 0) :
    Z_X e he * (Z_X e he - zornOne) = zornOne := by
  calc
    Z_X e he * (Z_X e he - zornOne) = Z_X e he * Z_X e he - Z_X e he * zornOne := mul_sub _ _ _
    _ = zornOne + Z_X e he - Z_X e he * zornOne := by rw [zornFibonacci_sq e he hx]
    _ = zornOne + Z_X e he - Z_X e he := by simp
    _ = zornOne := by abel

/-- Zorn normal form for positive powers. -/
theorem fibonacciZorn_pow_normal_form (e : Vec3) (he : dot e e = 1) (hx : cross e e = 0) (n : ℕ) :
    (Z_X e he) ^ (n + 1) =
      (Nat.fib n : ℝ) • zornOne + (Nat.fib (n + 1) : ℝ) • Z_X e he := by
  induction' n with k ih
  · simp
  · calc
      (Z_X e he) ^ (k + 1 + 1) = (Z_X e he) ^ (k + 1) * Z_X e he := pow_succ _ _
      _ = ((Nat.fib k : ℝ) • zornOne + (Nat.fib (k + 1) : ℝ) • Z_X e he) * Z_X e he := by rw [ih]
      _ = (Nat.fib k : ℝ) • (zornOne * Z_X e he) + (Nat.fib (k + 1) : ℝ) • (Z_X e he * Z_X e he) := by simp [add_mul]
      _ = (Nat.fib k : ℝ) • Z_X e he + (Nat.fib (k + 1) : ℝ) • (zornOne + Z_X e he) := by rw [zornFibonacci_sq e he hx]; simp
      _ = (Nat.fib k : ℝ) • Z_X e he + ((Nat.fib (k + 1) : ℝ) • zornOne + (Nat.fib (k + 1) : ℝ) • Z_X e he) := by rw [smul_add]
      _ = (Nat.fib (k + 1) : ℝ) • zornOne + ((Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ)) • Z_X e he := by module
      _ = (Nat.fib (k + 1) : ℝ) • zornOne + (Nat.fib (k + 2) : ℝ) • Z_X e he := by
        have hfib : (Nat.fib (k + 2) : ℝ) = ((Nat.fib (k + 1) + Nat.fib k : ℕ) : ℝ) := by
          rw [Nat.fib_add_two, add_comm]
        have hcast : (((Nat.fib (k + 1) + Nat.fib k : ℕ) : ℝ)) = (Nat.fib (k + 1) : ℝ) + (Nat.fib k : ℝ) := by
          exact Nat.cast_add _ _
        rw [hfib, hcast]

end CuntzFibonacciFlow
