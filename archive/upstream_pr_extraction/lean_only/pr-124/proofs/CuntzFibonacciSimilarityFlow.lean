import Mathlib
import proofs.CuntzEndomorphism
import proofs.CuntzMatrixCorner
import proofs.CuntzZornIntegration

open Matrix ZornCore Real CuntzZornIntegration

namespace CuntzFibonacciSimilarityFlow

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] [Nontrivial A] [NoZeroSMulDivisors ℝ A]
variable (S₁ S₂ : A) [hC : CuntzO2 S₁ S₂]

theorem CuntzFibonacciOperator_mul_inverse :
    CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ * (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ - 1) = 1 := by
  have h := fibonacciCuntzOperator_fusion S₁ S₂
  calc
    CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ * (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ - 1)
      = CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ - CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ * 1 := by rw [mul_sub]
    _ = (1 + CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) - CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by rw [h, mul_one]
    _ = 1 := by abel

theorem CuntzFibonacciOperator_inverse_mul :
    (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ - 1) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ = 1 := by
  have h := fibonacciCuntzOperator_fusion S₁ S₂
  calc
    (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ - 1) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂
      = CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ - 1 * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by rw [sub_mul]
    _ = (1 + CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) - CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by rw [h, one_mul]
    _ = 1 := by abel

/-- Packaging into the group of units Aˣ -/
def CuntzFibonacciUnit : Aˣ where
  val := CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂
  inv := CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ - 1
  val_inv := CuntzFibonacciOperator_mul_inverse S₁ S₂
  inv_val := CuntzFibonacciOperator_inverse_mul S₁ S₂

/-- 2. Inner Similarity Flow -/
def fibonacciSimilarityFlow (n : ℤ) (a : A) : A :=
  (CuntzFibonacciUnit S₁ S₂ ^ n).val * a * (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val

theorem fibonacciSimilarityFlow_zero (a : A) :
    fibonacciSimilarityFlow S₁ S₂ 0 a = a := by
  dsimp [fibonacciSimilarityFlow]
  simp

theorem fibonacciSimilarityFlow_add (m n : ℤ) (a : A) :
    fibonacciSimilarityFlow S₁ S₂ (m + n) a =
      fibonacciSimilarityFlow S₁ S₂ m (fibonacciSimilarityFlow S₁ S₂ n a) := by
  dsimp [fibonacciSimilarityFlow]
  rw [_root_.zpow_add, neg_add, add_comm (-m), _root_.zpow_add]
  simp only [Units.val_mul, mul_assoc]

theorem fibonacciSimilarityFlow_mul (n : ℤ) (a b : A) :
    fibonacciSimilarityFlow S₁ S₂ n (a * b) =
      fibonacciSimilarityFlow S₁ S₂ n a * fibonacciSimilarityFlow S₁ S₂ n b := by
  dsimp [fibonacciSimilarityFlow]
  have h1 : (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val * (CuntzFibonacciUnit S₁ S₂ ^ n).val = 1 := by
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  calc
    (CuntzFibonacciUnit S₁ S₂ ^ n).val * (a * b) * (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val
      = (CuntzFibonacciUnit S₁ S₂ ^ n).val * a * 1 * b * (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val := by simp only [mul_one, mul_assoc]
    _ = (CuntzFibonacciUnit S₁ S₂ ^ n).val * a * ((CuntzFibonacciUnit S₁ S₂ ^ (-n)).val * (CuntzFibonacciUnit S₁ S₂ ^ n).val) * b * (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val := by rw [h1]
    _ = ((CuntzFibonacciUnit S₁ S₂ ^ n).val * a * (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val) * ((CuntzFibonacciUnit S₁ S₂ ^ n).val * b * (CuntzFibonacciUnit S₁ S₂ ^ (-n)).val) := by simp_rw [mul_assoc]

/-- 3. Fibonacci Normal Form for Powers -/
theorem fibonacci_pow_normal_form (n : ℕ) :
    (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) ^ (n + 1) =
      (Nat.fib (n + 1) : A) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ + (Nat.fib n : A) * 1 := by
  induction' n with k ih
  · simp
  · calc
      CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ ^ (k + 1 + 1) = CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ ^ (k + 1) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := pow_succ _ _
      _ = ((Nat.fib (k + 1) : A) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ + (Nat.fib k : A) * 1) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by rw [ih]
      _ = (Nat.fib (k + 1) : A) * (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) + (Nat.fib k : A) * 1 * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by rw [add_mul, mul_assoc]
      _ = (Nat.fib (k + 1) : A) * (1 + CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) + (Nat.fib k : A) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by rw [fibonacciCuntzOperator_fusion, mul_one]
      _ = (Nat.fib (k + 1) : A) * 1 + (Nat.fib (k + 1) : A) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ + (Nat.fib k : A) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by rw [mul_add]
      _ = (Nat.fib (k + 2) : A) * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ + (Nat.fib (k + 1) : A) * 1 := by
        have hfib : (Nat.fib (k + 2) : A) = ((Nat.fib (k + 1) + Nat.fib k : ℕ) : A) := by
          rw [Nat.fib_add_two, add_comm]
        have hcast : (((Nat.fib (k + 1) + Nat.fib k : ℕ) : A)) = (Nat.fib (k + 1) : A) + (Nat.fib k : A) := by
          exact Nat.cast_add _ _
        rw [hfib, hcast]
        noncomm_ring

/-- 4. Trivial Dynamics on the Generated Subalgebra -/
theorem fibonacciFlow_fixed_on_generated_subalgebra
    (n : ℤ) (a b : A) (ha : Commute (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) a) (hb : Commute (CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) b) :
    fibonacciSimilarityFlow S₁ S₂ n (a + b * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) =
      a + b * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂ := by
  unfold fibonacciSimilarityFlow
  have hc : Commute (CuntzFibonacciUnit S₁ S₂).val (a + b * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) := by
    apply Commute.add_right
    · exact ha
    · exact Commute.mul_right hb (Commute.refl _)
  have hc_zpow : Commute ((CuntzFibonacciUnit S₁ S₂ ^ n).val) (a + b * CuntzZornIntegration.CuntzFibonacciOperator S₁ S₂) := by
    exact (Commute.units_zpow_right hc.symm n).symm
  rw [hc_zpow.eq, mul_assoc, ← Units.val_mul]
  have h_inv : (CuntzFibonacciUnit S₁ S₂ ^ n) * (CuntzFibonacciUnit S₁ S₂ ^ (-n)) = 1 := by
    rw [← _root_.zpow_add, add_neg_cancel, zpow_zero]
  rw [h_inv, Units.val_one, mul_one]

/-- 5. Zorn Transport -/
def Z_X (e : Vec3) (he : dot e e = 1) : Zorn :=
  zornLineEmbed e he FibonacciLocalMatrix

theorem zornFibonacci_inv (e : Vec3) (he : dot e e = 1) :
    Z_X e he * (Z_X e he - zornOne) = zornOne := by
  ext1
  · simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne, dot]
    exact he
  · ext x; fin_cases x <;> simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne, cross] <;> try ring
  · ext x; fin_cases x <;> simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne, cross] <;> try ring
  · simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne, dot]
    exact he

def zornPow (Z : Zorn) : ℕ → Zorn
| 0 => zornOne
| (n + 1) => zornPow Z n * Z

lemma dot_smul_left (c : ℝ) (u v : Vec3) : dot (c • u) v = c * dot u v := by
  dsimp [dot]
  have : (fun i => c * u i * v i) = (fun i => c * (u i * v i)) := by ext i; ring
  rw [this, ← Finset.mul_sum]

lemma cross_smul_left (c : ℝ) (u v : Vec3) : cross (c • u) v = c • cross u v := by
  ext x; fin_cases x <;> { dsimp [cross]; ring }

theorem zornFibonacci_pow (e : Vec3) (he : dot e e = 1) (n : ℕ) :
    zornPow (Z_X e he) (n + 1) =
      (Nat.fib (n + 1) : ℝ) • Z_X e he + (Nat.fib n : ℝ) • zornOne := by
  induction' n with k ih
  · ext1
    · simp [zornPow, zornOne, Z_X, zornLineEmbed, FibonacciLocalMatrix, dot]
    · ext x; fin_cases x <;> simp [zornPow, zornOne, Z_X, zornLineEmbed, FibonacciLocalMatrix, cross] <;> try ring
    · ext x; fin_cases x <;> simp [zornPow, zornOne, Z_X, zornLineEmbed, FibonacciLocalMatrix, cross] <;> try ring
    · simp [zornPow, zornOne, Z_X, zornLineEmbed, FibonacciLocalMatrix, dot]
  · change zornPow (Z_X e he) (k + 1) * Z_X e he = _
    rw [ih]
    ext1
    · simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne]
      rw [dot_smul_left, he, mul_one]
    · ext x; fin_cases x <;> {
        simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne, cross_smul_left]
        dsimp [cross]
        have hfib : (Nat.fib (k + 2) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ) := by
          have : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
          rw [this, Nat.cast_add]
        try rw [hfib]
        try ring
      }
    · ext x; fin_cases x <;> {
        simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne, cross_smul_left]
        dsimp [cross]
        have hfib : (Nat.fib (k + 2) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ) := by
          have : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
          rw [this, Nat.cast_add]
        try rw [hfib]
        try ring
      }
    · simp [Z_X, zornLineEmbed, FibonacciLocalMatrix, zornOne]
      rw [dot_smul_left, he, mul_one]
      have hfib : (Nat.fib (k + 2) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ) := by
        have : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
        rw [this, Nat.cast_add]
      linarith

end CuntzFibonacciSimilarityFlow
