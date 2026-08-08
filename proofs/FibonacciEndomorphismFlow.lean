import Mathlib
import proofs.CuntzEndomorphism
import proofs.CuntzMatrixCorner
import proofs.FibonacciPeirceProjectors
import proofs.ZornPeirceBridge

noncomputable section

open Matrix ZornCore Real FibonacciPeirceProjectors

namespace FibonacciEndomorphismFlow

variable {A : Type*} [Ring A] [StarRing A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

/-- 1. Invertibility of the Cuntz Fibonacci Operator
Because X^2 = 1 + X, X has a canonical algebraic inverse: X^{-1} = X - 1.
-/
theorem CuntzFibonacciOperator_mul_inverse :
    CuntzMatrixCorner.fibonacciCuntzOperator S *
        (CuntzMatrixCorner.fibonacciCuntzOperator S - 1) = 1 := by
  have h := CuntzMatrixCorner.fibonacciCuntzOperator_sq S
  calc
    CuntzMatrixCorner.fibonacciCuntzOperator S * (CuntzMatrixCorner.fibonacciCuntzOperator S - 1)
      = CuntzMatrixCorner.fibonacciCuntzOperator S * CuntzMatrixCorner.fibonacciCuntzOperator S - CuntzMatrixCorner.fibonacciCuntzOperator S * 1 := by rw [mul_sub]
    _ = (CuntzMatrixCorner.fibonacciCuntzOperator S + 1) - CuntzMatrixCorner.fibonacciCuntzOperator S := by rw [h, mul_one]
    _ = 1 := by abel

theorem CuntzFibonacciOperator_inverse_mul :
    (CuntzMatrixCorner.fibonacciCuntzOperator S - 1) *
        CuntzMatrixCorner.fibonacciCuntzOperator S = 1 := by
  have h := CuntzMatrixCorner.fibonacciCuntzOperator_sq S
  calc
    (CuntzMatrixCorner.fibonacciCuntzOperator S - 1) * CuntzMatrixCorner.fibonacciCuntzOperator S
      = CuntzMatrixCorner.fibonacciCuntzOperator S * CuntzMatrixCorner.fibonacciCuntzOperator S - 1 * CuntzMatrixCorner.fibonacciCuntzOperator S := by rw [sub_mul]
    _ = (CuntzMatrixCorner.fibonacciCuntzOperator S + 1) - CuntzMatrixCorner.fibonacciCuntzOperator S := by rw [h, one_mul]
    _ = 1 := by abel

/-- Packaging the operator into the group of units Aˣ -/
def CuntzFibonacciUnit : Aˣ where
  val := CuntzMatrixCorner.fibonacciCuntzOperator S
  inv := CuntzMatrixCorner.fibonacciCuntzOperator S - 1
  val_inv := CuntzFibonacciOperator_mul_inverse S
  inv_val := CuntzFibonacciOperator_inverse_mul S

/-- 2. Discrete ℤ-flow (Inner Automorphism Flow)
Φ_n(a) = X^n a X^{-n}
-/
def FibonacciFlow (n : ℤ) (a : A) : A :=
  (CuntzFibonacciUnit S ^ n).val * a * (CuntzFibonacciUnit S ^ (-n)).val

theorem FibonacciFlow_zero (a : A) :
    FibonacciFlow S 0 a = a := by
  dsimp [FibonacciFlow]
  simp

theorem FibonacciFlow_add (m n : ℤ) (a : A) :
    FibonacciFlow S (m + n) a = FibonacciFlow S m (FibonacciFlow S n a) := by
  dsimp [FibonacciFlow]
  rw [zpow_add, neg_add, zpow_add]
  simp only [Units.val_mul]
  simp_rw [mul_assoc]

theorem FibonacciFlow_mul (n : ℤ) (a b : A) :
    FibonacciFlow S n (a * b) = FibonacciFlow S n a * FibonacciFlow S n b := by
  dsimp [FibonacciFlow]
  have h1 : (CuntzFibonacciUnit S ^ (-n)).val * (CuntzFibonacciUnit S ^ n).val = 1 := by
    rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  calc
    (CuntzFibonacciUnit S ^ n).val * (a * b) * (CuntzFibonacciUnit S ^ (-n)).val
      = (CuntzFibonacciUnit S ^ n).val * a * 1 * b * (CuntzFibonacciUnit S ^ (-n)).val := by simp only [mul_one, mul_assoc]
    _ = (CuntzFibonacciUnit S ^ n).val * a * ((CuntzFibonacciUnit S ^ (-n)).val * (CuntzFibonacciUnit S ^ n).val) * b * (CuntzFibonacciUnit S ^ (-n)).val := by rw [h1]
    _ = ((CuntzFibonacciUnit S ^ n).val * a * (CuntzFibonacciUnit S ^ (-n)).val) * ((CuntzFibonacciUnit S ^ n).val * b * (CuntzFibonacciUnit S ^ (-n)).val) := by simp_rw [mul_assoc]

/-- 3. Fibonacci Sequence Normal Form for Powers
X^n = F_{n-1} 1 + F_n X  for n ≥ 1.
-/
theorem CuntzFibonacciOperator_pow (n : ℕ) (hn : 1 ≤ n) :
    (CuntzMatrixCorner.fibonacciCuntzOperator S) ^ n =
      (Nat.fib (n - 1) : A) * 1 + (Nat.fib n : A) * CuntzMatrixCorner.fibonacciCuntzOperator S := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  subst hk
  induction' k with k ih
  · simp
  · have h1 : k + 1 + 1 - 1 = k + 1 := rfl
    have h2 : k + 1 - 1 = k := rfl
    rw [h1]
    calc
      CuntzMatrixCorner.fibonacciCuntzOperator S ^ (k + 1 + 1) = CuntzMatrixCorner.fibonacciCuntzOperator S ^ (k + 1) * CuntzMatrixCorner.fibonacciCuntzOperator S := pow_succ _ _
      _ = ((Nat.fib k : A) * 1 + (Nat.fib (k + 1) : A) * CuntzMatrixCorner.fibonacciCuntzOperator S) * CuntzMatrixCorner.fibonacciCuntzOperator S := by
        have hih : CuntzMatrixCorner.fibonacciCuntzOperator S ^ (k + 1) = (Nat.fib (k + 1 - 1) : A) * 1 + (Nat.fib (k + 1) : A) * CuntzMatrixCorner.fibonacciCuntzOperator S := ih (by omega)
        rw [h2] at hih
        rw [hih]
      _ = (Nat.fib k : A) * CuntzMatrixCorner.fibonacciCuntzOperator S + (Nat.fib (k + 1) : A) * (CuntzMatrixCorner.fibonacciCuntzOperator S * CuntzMatrixCorner.fibonacciCuntzOperator S) := by noncomm_ring
      _ = (Nat.fib k : A) * CuntzMatrixCorner.fibonacciCuntzOperator S + (Nat.fib (k + 1) : A) * (CuntzMatrixCorner.fibonacciCuntzOperator S + 1) := by rw [CuntzMatrixCorner.fibonacciCuntzOperator_sq S]
      _ = (Nat.fib (k + 1) : A) * 1 + ((Nat.fib (k + 1) : A) + (Nat.fib k : A)) * CuntzMatrixCorner.fibonacciCuntzOperator S := by noncomm_ring
      _ = (Nat.fib (k + 1) : A) * 1 + (Nat.fib (k + 1 + 1) : A) * CuntzMatrixCorner.fibonacciCuntzOperator S := by
        have hfib : (Nat.fib (k + 1 + 1) : A) = ((Nat.fib (k + 1) + Nat.fib k : ℕ) : A) := by
          rw [Nat.fib_add_two, add_comm]
        have hcast : (((Nat.fib (k + 1) + Nat.fib k : ℕ) : A)) = (Nat.fib (k + 1) : A) + (Nat.fib k : A) := by
          exact Nat.cast_add _ _
        rw [hfib, hcast]

/-- 4. Transport to Local Matrix
The local 2x2 matrix also exhibits the identical inverse relation M_X(M_X - I) = I.
-/
theorem fibonacciMatrixReal_inv :
    fibonacciMatrixReal * (fibonacciMatrixReal - 1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- 5. Transport to Zorn
Because zornLineEmbed is a unital algebra homomorphism on the associative section,
the inverse property and Fibonacci sequence powers transport directly to the Zorn algebra.
-/
def Z_X (e : Vec3) (he : dot e e = 1) : Zorn :=
  zornLineEmbed e he fibonacciMatrixReal

theorem zornFibonacci_inv (e : Vec3) (he : dot e e = 1) (hx : cross e e = 0) :
    Z_X e he * (Z_X e he - zornOne) = zornOne := by
  dsimp [Z_X]
  rw [← zornLineEmbed_one he]
  rw [← zornLineEmbed_sub e he]
  rw [← zornLineEmbed_mul e he hx]
  rw [fibonacciMatrixReal_inv]
  rw [zornLineEmbed_one he]

theorem zornFibonacci_pow (e : Vec3) (he : dot e e = 1) (hx : cross e e = 0) (n : ℕ) (hn : 1 ≤ n) :
    (Z_X e he) ^ n = (Nat.fib (n - 1) : ℝ) • zornOne + (Nat.fib n : ℝ) • Z_X e he := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  subst hk
  induction' k with k ih
  · simp
  · have h1 : k + 1 + 1 - 1 = k + 1 := rfl
    have h2 : k + 1 - 1 = k := rfl
    rw [h1]
    calc
      Z_X e he ^ (k + 1 + 1) = Z_X e he ^ (k + 1) * Z_X e he := pow_succ _ _
      _ = ((Nat.fib k : ℝ) • zornOne + (Nat.fib (k + 1) : ℝ) • Z_X e he) * Z_X e he := by
        have hih : Z_X e he ^ (k + 1) = (Nat.fib (k + 1 - 1) : ℝ) • zornOne + (Nat.fib (k + 1) : ℝ) • Z_X e he := ih (by omega)
        rw [h2] at hih
        rw [hih]
      _ = (Nat.fib k : ℝ) • (zornOne * Z_X e he) + (Nat.fib (k + 1) : ℝ) • (Z_X e he * Z_X e he) := by rw [add_mul, smul_mul_assoc, smul_mul_assoc]
      _ = (Nat.fib k : ℝ) • Z_X e he + (Nat.fib (k + 1) : ℝ) • (zornOne + Z_X e he) := by
        have hsq : Z_X e he * Z_X e he = zornOne + Z_X e he := by
          dsimp [Z_X]
          rw [← zornLineEmbed_mul e he hx]
          have hsqM : fibonacciMatrixReal * fibonacciMatrixReal = 1 + fibonacciMatrixReal := by
            ext i j; fin_cases i <;> fin_cases j <;> rfl
          rw [hsqM, zornLineEmbed_add e he, zornLineEmbed_one he]
        rw [hsq, one_mul]
      _ = (Nat.fib (k + 1) : ℝ) • zornOne + ((Nat.fib (k + 1) : ℝ) + (Nat.fib k : ℝ)) • Z_X e he := by
        rw [smul_add]
        have h : (Nat.fib k : ℝ) • Z_X e he + ((Nat.fib (k + 1) : ℝ) • zornOne + (Nat.fib (k + 1) : ℝ) • Z_X e he) =
            (Nat.fib (k + 1) : ℝ) • zornOne + ((Nat.fib k : ℝ) • Z_X e he + (Nat.fib (k + 1) : ℝ) • Z_X e he) := by abel
        rw [h, ← add_smul, add_comm]
      _ = (Nat.fib (k + 1) : ℝ) • zornOne + (Nat.fib (k + 1 + 1) : ℝ) • Z_X e he := by
        have hfib : (Nat.fib (k + 1 + 1) : ℝ) = ((Nat.fib (k + 1) + Nat.fib k : ℕ) : ℝ) := by
          rw [Nat.fib_add_two, add_comm]
        have hcast : (((Nat.fib (k + 1) + Nat.fib k : ℕ) : ℝ)) = (Nat.fib (k + 1) : ℝ) + (Nat.fib k : ℝ) := by
          exact Nat.cast_add _ _
        rw [hfib, hcast]

end FibonacciEndomorphismFlow
