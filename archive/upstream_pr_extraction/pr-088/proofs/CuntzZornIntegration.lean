import Mathlib
import proofs.ZornPeirceBridge
import proofs.CuntzEndomorphism

noncomputable section

open Matrix ZornCore Real

namespace CuntzZornIntegration

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] [Nontrivial A] [NoZeroSMulDivisors ℝ A]
variable (S₁ S₂ : A) [hC : CuntzO2 S₁ S₂]

/-- The Fibonacci operator within the Cuntz algebra -/
def CuntzFibonacciOperator : A :=
  BraidTwist S₁ S₂ + S₂ * star S₂

theorem CuntzFibonacciOperator_mul_S₁ :
    CuntzFibonacciOperator S₁ S₂ * S₁ = S₂ := by
  unfold CuntzFibonacciOperator BraidTwist
  calc
    (S₁ * star S₂ + S₂ * star S₁ + S₂ * star S₂) * S₁ =
        S₁ * (star S₂ * S₁) +
        S₂ * (star S₁ * S₁) +
        S₂ * (star S₂ * S₁) := by noncomm_ring
    _ = S₂ := by
      rw [hC.ortho₂₁, hC.isom₁]
      simp

theorem CuntzFibonacciOperator_mul_S₂ :
    CuntzFibonacciOperator S₁ S₂ * S₂ = S₁ + S₂ := by
  unfold CuntzFibonacciOperator BraidTwist
  calc
    (S₁ * star S₂ + S₂ * star S₁ + S₂ * star S₂) * S₂ =
        S₁ * (star S₂ * S₂) +
        S₂ * (star S₁ * S₂) +
        S₂ * (star S₂ * S₂) := by noncomm_ring
    _ = S₁ + S₂ := by
      rw [hC.isom₂, hC.ortho₁₂]
      simp

/-- Explicit fusion polynomial for the abstract Cuntz element -/
theorem fibonacciCuntzOperator_fusion :
    CuntzFibonacciOperator S₁ S₂ * CuntzFibonacciOperator S₁ S₂ = 1 + CuntzFibonacciOperator S₁ S₂ := by
  unfold CuntzFibonacciOperator BraidTwist
  calc
    (S₁ * star S₂ + S₂ * star S₁ + S₂ * star S₂) * (S₁ * star S₂ + S₂ * star S₁ + S₂ * star S₂)
      = S₁ * (star S₂ * S₁) * star S₂ +
        S₁ * (star S₂ * S₂) * star S₁ +
        S₁ * (star S₂ * S₂) * star S₂ +
        S₂ * (star S₁ * S₁) * star S₂ +
        S₂ * (star S₁ * S₂) * star S₁ +
        S₂ * (star S₁ * S₂) * star S₂ +
        S₂ * (star S₂ * S₁) * star S₂ +
        S₂ * (star S₂ * S₂) * star S₁ +
        S₂ * (star S₂ * S₂) * star S₂ := by noncomm_ring
    _ = S₁ * 0 * star S₂ +
        S₁ * 1 * star S₁ +
        S₁ * 1 * star S₂ +
        S₂ * 1 * star S₂ +
        S₂ * 0 * star S₁ +
        S₂ * 0 * star S₂ +
        S₂ * 0 * star S₂ +
        S₂ * 1 * star S₁ +
        S₂ * 1 * star S₂ := by
      rw [hC.ortho₂₁, hC.isom₂, hC.isom₁, hC.ortho₁₂]
    _ = S₁ * star S₁ + S₁ * star S₂ + S₂ * star S₂ + S₂ * star S₁ + S₂ * star S₂ := by
      simp only [mul_zero, zero_mul, smul_zero, zero_add, add_zero, mul_one, one_mul]
    _ = (S₁ * star S₁ + S₂ * star S₂) + (S₁ * star S₂ + S₂ * star S₁ + S₂ * star S₂) := by abel
    _ = 1 + (S₁ * star S₂ + S₂ * star S₁ + S₂ * star S₂) := by rw [hC.cuntz_sum]

/-- Local matrix representation in the basis {S₁, S₂} -/
def FibonacciLocalMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1],
    ![1, 1]]

/-- Synthesis map constructing the submodule element from coordinate vector -/
def synth (v : Fin 2 → ℝ) : A :=
  (v 0) • S₁ + (v 1) • S₂

theorem synth_injective : Function.Injective (synth S₁ S₂) := by
  intro v w hvw
  apply funext
  intro i
  have himp : ∀ x y : ℝ, x • (1 : A) = y • (1 : A) → x = y := by
    intro x y hxy
    have h1 : (x - y) • (1 : A) = 0 := by rw [sub_smul, hxy, sub_self]
    cases smul_eq_zero.mp h1 with
    | inl h2 => exact eq_of_sub_eq_zero h2
    | inr h2 => exact False.elim (one_ne_zero h2)
  match i with
  | 0 =>
    have h := congrArg (fun a => star S₁ * a) hvw
    dsimp [synth] at h
    simp only [mul_add, Algebra.mul_smul_comm, hC.isom₁, hC.ortho₁₂, mul_one, mul_zero, smul_zero, add_zero] at h
    exact himp _ _ h
  | 1 =>
    have h := congrArg (fun a => star S₂ * a) hvw
    dsimp [synth] at h
    simp only [mul_add, Algebra.mul_smul_comm, hC.isom₂, hC.ortho₂₁, mul_one, mul_zero, smul_zero, zero_add] at h
    exact himp _ _ h

theorem synth_intertwine (v : Fin 2 → ℝ) :
    CuntzFibonacciOperator S₁ S₂ * synth S₁ S₂ v = synth S₁ S₂ (FibonacciLocalMatrix *ᵥ v) := by
  dsimp [synth, FibonacciLocalMatrix, Matrix.mulVec, dotProduct]
  simp only [mul_add, Algebra.mul_smul_comm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, zero_mul, one_mul, zero_add, add_zero]
  -- We have v 0 • (CuntzFibonacciOperator * S₁) + v 1 • (CuntzFibonacciOperator * S₂)
  rw [CuntzFibonacciOperator_mul_S₁ S₁ S₂, CuntzFibonacciOperator_mul_S₂ S₁ S₂]
  simp [smul_add, add_smul]
  abel

/-- The matrix fusion rule (Fibonacci polynomial) -/
theorem FibonacciLocalMatrix_sq :
    FibonacciLocalMatrix * FibonacciLocalMatrix = 1 + FibonacciLocalMatrix := by
  ext i j
  dsimp [FibonacciLocalMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> {
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  }

/-- Peirce Spectral Layer -/
def phi : ℝ := (1 + Real.sqrt 5) / 2
def lambda_minus : ℝ := 1 - phi

lemma phi_sq : phi * phi = phi + 1 := by
  dsimp [phi]
  have h5 : 0 ≤ (5 : ℝ) := by norm_num
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt h5
  nlinarith

def n_plus : Fin 2 → ℝ := ![1, phi]
def n_minus : Fin 2 → ℝ := ![phi, -1]

lemma n_plus_dot_n_minus : dotProduct n_plus n_minus = 0 := by
  dsimp [n_plus, n_minus, dotProduct]; rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring

-- Векторна форма на проекторите (канонична Mathlib дефиниция)
def P_plus : Matrix (Fin 2) (Fin 2) ℝ :=
  (dotProduct n_plus n_plus)⁻¹ • vecMulVec n_plus n_plus

def P_minus : Matrix (Fin 2) (Fin 2) ℝ :=
  (dotProduct n_minus n_minus)⁻¹ • vecMulVec n_minus n_minus

-- Структурно доказателство за идемпотентност
lemma vecMulVec_mul_vecMulVec {n : Type*} [Fintype n] [CommRing R] (v : n → R) :
    vecMulVec v v * vecMulVec v v = dotProduct v v • vecMulVec v v := by
  ext i j
  dsimp [vecMulVec, dotProduct, Matrix.mul_apply, smul_apply, smul_eq_mul]
  calc
    ∑ k, (v i * v k) * (v k * v j)
      = ∑ k, (v k * v k) * (v i * v j) := by congr; ext k; ring
    _ = (∑ k, v k * v k) * (v i * v j) := by rw [Finset.sum_mul]

theorem P_plus_idempotent : P_plus * P_plus = P_plus := by
  dsimp [P_plus]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, vecMulVec_mul_vecMulVec, ← smul_assoc]
  have h_dot : dotProduct n_plus n_plus = 2 + phi := by
    dsimp [n_plus, dotProduct]; rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    calc 1 * 1 + phi * phi = 1 * 1 + (phi + 1) := by rw [phi_sq]
         _ = 2 + phi := by ring
  have h_inv : (((dotProduct n_plus n_plus)⁻¹ * (dotProduct n_plus n_plus)⁻¹) • dotProduct n_plus n_plus) = (dotProduct n_plus n_plus)⁻¹ := by
    change ((dotProduct n_plus n_plus)⁻¹ * (dotProduct n_plus n_plus)⁻¹) * dotProduct n_plus n_plus = (dotProduct n_plus n_plus)⁻¹
    rw [mul_assoc]
    have h_nz : dotProduct n_plus n_plus ≠ 0 := by
      rw [h_dot]
      dsimp [phi]
      have h5 : 0 < (5 : ℝ) := by norm_num
      have hsqrt : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr h5
      linarith
    rw [inv_mul_cancel₀ h_nz, mul_one]
  rw [h_inv]

/-- Zorn Transport Layer -/
def Z_X (e : Vec3) (he : dot e e = 1) : Zorn :=
  zornLineEmbed e he FibonacciLocalMatrix

theorem zornLineEmbed_add (e : Vec3) (he : dot e e = 1) (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    zornLineEmbed e he (A + B) = zornLineEmbed e he A + zornLineEmbed e he B := by
  dsimp [zornLineEmbed, Matrix.add_apply]
  ext <;> simp [add_smul, add_mul] <;> ring

theorem zornFibonacci_sq (e : Vec3) (he : dot e e = 1) (hx : cross e e = 0) :
    Z_X e he * Z_X e he = zornOne + Z_X e he := by
  dsimp [Z_X]
  rw [← zornLineEmbed_mul e he hx]
  rw [FibonacciLocalMatrix_sq]
  rw [zornLineEmbed_add e he, zornLineEmbed_one e he]

end CuntzZornIntegration
