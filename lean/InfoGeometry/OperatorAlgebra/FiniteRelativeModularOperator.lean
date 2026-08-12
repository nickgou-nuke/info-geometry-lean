import Mathlib
import InfoGeometry.Physics.RegularBimoduleCommutant

/-!
# Finite relative modular operator

This owner isolates the finite algebraic part of the relative modular
construction.  Invertibility is carried by explicit two-sided inverse
witnesses; no positivity or logarithmic functional calculus is assumed here.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteRelativeModularOperator

open InfoGeometry.Physics.RegularBimoduleCommutant

abbrev MatrixCarrier (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev EndCarrier (n : ℕ) := MatrixCarrier n →ₗ[ℂ] MatrixCarrier n

structure InvertibleMatrix (n : ℕ) where
  val : MatrixCarrier n
  inv : MatrixCarrier n
  val_mul_inv : val * inv = 1
  inv_mul_val : inv * val = 1

def relativeModular (ρ σ : InvertibleMatrix n) : EndCarrier n :=
  (leftAction (R := ℂ) ρ.val).comp (rightAction (R := ℂ) σ.inv)

@[simp] theorem relativeModular_apply (ρ σ : InvertibleMatrix n)
    (X : MatrixCarrier n) :
    relativeModular ρ σ X = ρ.val * X * σ.inv := by
  simp [relativeModular, leftAction, rightAction, LinearMap.comp_apply, mul_assoc]

def relativeModularInverse (ρ σ : InvertibleMatrix n) : EndCarrier n :=
  (leftAction (R := ℂ) ρ.inv).comp (rightAction (R := ℂ) σ.val)

@[simp] theorem relativeModularInverse_apply (ρ σ : InvertibleMatrix n)
    (X : MatrixCarrier n) :
    relativeModularInverse ρ σ X = ρ.inv * X * σ.val := by
  simp [relativeModularInverse, leftAction, rightAction, LinearMap.comp_apply,
    mul_assoc]

theorem relativeModular_mul_inverse (ρ σ : InvertibleMatrix n) :
    (relativeModular ρ σ).comp (relativeModularInverse ρ σ) = 1 := by
  apply LinearMap.ext
  intro X
  have h : ρ.val * ρ.inv * X * (σ.val * σ.inv) = X := by
    rw [ρ.val_mul_inv, σ.val_mul_inv]
    simp
  simpa [relativeModular, relativeModularInverse, leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc] using h

theorem relativeModular_inverse_mul (ρ σ : InvertibleMatrix n) :
    (relativeModularInverse ρ σ).comp (relativeModular ρ σ) = 1 := by
  apply LinearMap.ext
  intro X
  have h : ρ.inv * ρ.val * X * (σ.inv * σ.val) = X := by
    rw [ρ.inv_mul_val, σ.inv_mul_val]
    simp
  simpa [relativeModular, relativeModularInverse, leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc] using h

def diagonalInvertible {n : ℕ} (p pinv : Fin n → ℂ)
    (h₁ : ∀ i, p i * pinv i = 1) (h₂ : ∀ i, pinv i * p i = 1) :
    InvertibleMatrix n :=
  { val := Matrix.diagonal p
    inv := Matrix.diagonal pinv
    val_mul_inv := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [h₁]
      · simp [hij]
    inv_mul_val := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [h₂]
      · simp [hij] }

def matrixUnit {n : ℕ} (i j : Fin n) : MatrixCarrier n :=
  Matrix.single i j 1

theorem matrixUnit_ne_zero {n : ℕ} (i j : Fin n) :
    matrixUnit i j ≠ 0 := by
  intro h
  have hij := congrArg (fun M : MatrixCarrier n => M i j) h
  simpa [matrixUnit, Matrix.single] using hij

theorem diagonal_relativeModular_matrixUnit
    {n : ℕ} (p pinv q qinv : Fin n → ℂ)
    (hp : ∀ i, p i * pinv i = 1) (hp' : ∀ i, pinv i * p i = 1)
    (hq : ∀ i, q i * qinv i = 1) (hq' : ∀ i, qinv i * q i = 1)
    (i j : Fin n) :
    relativeModular (diagonalInvertible p pinv hp hp')
      (diagonalInvertible q qinv hq hq') (matrixUnit i j) =
      (p i * qinv j) • matrixUnit i j := by
  rw [relativeModular_apply]
  unfold diagonalInvertible matrixUnit
  change Matrix.diagonal p * Matrix.single i j (1 : ℂ) * Matrix.diagonal qinv =
    (p i * qinv j) • Matrix.single i j (1 : ℂ)
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply]
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simp [Matrix.single]
    · have hb' : j ≠ b := Ne.symm hb
      simp [Matrix.single, hb']
  · have ha' : i ≠ a := Ne.symm ha
    by_cases hb : b = j
    · subst b
      simp [Matrix.single, ha']
    · have hb' : j ≠ b := Ne.symm hb
      simp [Matrix.single, ha', hb']

theorem neg_log_div_pos (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    -Real.log (p / q) = -Real.log p + Real.log q := by
  rw [Real.log_div hp.ne' hq.ne']
  ring

end InfoGeometry.OperatorAlgebra.FiniteRelativeModularOperator
