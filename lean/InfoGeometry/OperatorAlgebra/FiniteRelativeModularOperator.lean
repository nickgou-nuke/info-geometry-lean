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

abbrev InvertibleMatrix (n : ℕ) := (MatrixCarrier n)ˣ

noncomputable def invertibleMatrixOfDetNeZero
    {n : ℕ} (A : MatrixCarrier n)
    (hdet : A.det ≠ 0) : InvertibleMatrix n := by
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  exact hunit.unit

@[simp] theorem invertibleMatrixOfDetNeZero_val
    {n : ℕ} (A : MatrixCarrier n) (hdet : A.det ≠ 0) :
    (invertibleMatrixOfDetNeZero A hdet : MatrixCarrier n) = A := by
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  exact hunit.unit_spec

@[simp] theorem invertibleMatrixOfDetNeZero_inv
    {n : ℕ} (A : MatrixCarrier n) (hdet : A.det ≠ 0) :
    ((invertibleMatrixOfDetNeZero A hdet)⁻¹ : MatrixCarrier n) = A⁻¹ := by
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  change ((hunit.unit)⁻¹ : MatrixCarrier n) = A⁻¹
  simpa using congrArg (fun M : MatrixCarrier n => M⁻¹) hunit.unit_spec

theorem rawRelativeModular_inverse_apply
    {n : ℕ} (ρ σ X : MatrixCarrier n)
    (hρ : ρ.det ≠ 0) (hσ : σ.det ≠ 0) :
    ρ⁻¹ * (ρ * X * σ⁻¹) * σ = X := by
  have hρunit : IsUnit ρ := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hρ
  have hσunit : IsUnit σ := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hσ
  have hρinv : ρ⁻¹ * ρ = 1 := by
    simpa [hρunit.unit_spec] using hρunit.unit.inv_val
  have hσinv : σ⁻¹ * σ = 1 := by
    simpa [hσunit.unit_spec] using hσunit.unit.inv_val
  calc
    ρ⁻¹ * (ρ * X * σ⁻¹) * σ = (ρ⁻¹ * ρ) * X * (σ⁻¹ * σ) := by
      noncomm_ring
    _ = X := by rw [hρinv, hσinv]; simp

theorem rawRelativeModular_forward_inverse_apply
    {n : ℕ} (ρ σ X : MatrixCarrier n)
    (hρ : ρ.det ≠ 0) (hσ : σ.det ≠ 0) :
    ρ * (ρ⁻¹ * X * σ) * σ⁻¹ = X := by
  have hρunit : IsUnit ρ := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hρ
  have hσunit : IsUnit σ := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hσ
  have hρinv : ρ * ρ⁻¹ = 1 := by
    simpa [hρunit.unit_spec] using hρunit.unit.val_inv
  have hσinv : σ * σ⁻¹ = 1 := by
    simpa [hσunit.unit_spec] using hσunit.unit.val_inv
  calc
    ρ * (ρ⁻¹ * X * σ) * σ⁻¹ = (ρ * ρ⁻¹) * X * (σ * σ⁻¹) := by
      noncomm_ring
    _ = X := by rw [hρinv, hσinv]; simp

noncomputable def relativeModular (ρ σ : InvertibleMatrix n) : EndCarrier n :=
  (leftAction (R := ℂ) (ρ : MatrixCarrier n)).comp
    (rightAction (R := ℂ) ((σ⁻¹ : InvertibleMatrix n) : MatrixCarrier n))

@[simp] theorem relativeModular_apply (ρ σ : InvertibleMatrix n)
    (X : MatrixCarrier n) :
    relativeModular ρ σ X = ρ * X *
      ((σ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) := by
  simp [relativeModular, leftAction, rightAction, LinearMap.comp_apply, mul_assoc]

noncomputable def relativeModularInverse (ρ σ : InvertibleMatrix n) : EndCarrier n :=
  (leftAction (R := ℂ) ((ρ⁻¹ : InvertibleMatrix n) : MatrixCarrier n)).comp
    (rightAction (R := ℂ) (σ : MatrixCarrier n))

@[simp] theorem relativeModularInverse_apply (ρ σ : InvertibleMatrix n)
    (X : MatrixCarrier n) :
    relativeModularInverse ρ σ X =
      ((ρ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) * X * σ := by
  simp [relativeModularInverse, leftAction, rightAction, LinearMap.comp_apply,
    mul_assoc]

theorem relativeModular_mul_inverse (ρ σ : InvertibleMatrix n) :
    (relativeModular ρ σ).comp (relativeModularInverse ρ σ) = 1 := by
  apply LinearMap.ext
  intro X
  have h : (ρ : MatrixCarrier n) *
      ((ρ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) * X *
      ((σ : MatrixCarrier n) *
        ((σ⁻¹ : InvertibleMatrix n) : MatrixCarrier n)) = X := by
    have hρinv : (ρ : MatrixCarrier n) *
        ((ρ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) = 1 := ρ.val_inv
    have hσinv : (σ : MatrixCarrier n) *
        ((σ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) = 1 := σ.val_inv
    rw [hρinv, hσinv]
    simp
  simpa [relativeModular, relativeModularInverse, leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc] using h

theorem relativeModular_inverse_mul (ρ σ : InvertibleMatrix n) :
    (relativeModularInverse ρ σ).comp (relativeModular ρ σ) = 1 := by
  apply LinearMap.ext
  intro X
  have h : ((ρ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) *
      (ρ : MatrixCarrier n) * X *
      (((σ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) *
        (σ : MatrixCarrier n)) = X := by
    have hρinv : ((ρ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) *
        (ρ : MatrixCarrier n) = 1 := ρ.inv_val
    have hσinv : ((σ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) *
        (σ : MatrixCarrier n) = 1 := σ.inv_val
    rw [hρinv, hσinv]
    simp
  simpa [relativeModular, relativeModularInverse, leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc] using h

/-- The finite relative modular operator is a genuine linear equivalence. -/
noncomputable def relativeModularEquiv (ρ σ : InvertibleMatrix n) :
    MatrixCarrier n ≃ₗ[ℂ] MatrixCarrier n where
  toLinearMap := relativeModular ρ σ
  invFun := relativeModularInverse ρ σ
  left_inv := by
    intro X
    have h := congrArg (fun T : EndCarrier n => T X)
      (relativeModular_inverse_mul ρ σ)
    simpa [LinearMap.comp_apply] using h
  right_inv := by
    intro X
    have h := congrArg (fun T : EndCarrier n => T X)
      (relativeModular_mul_inverse ρ σ)
    simpa [LinearMap.comp_apply] using h
@[simp] theorem relativeModularEquiv_apply (ρ σ : InvertibleMatrix n)
    (X : MatrixCarrier n) :
    relativeModularEquiv ρ σ X = (ρ : MatrixCarrier n) * X *
      ((σ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) := by
  exact relativeModular_apply ρ σ X

@[simp] theorem relativeModularEquiv_symm_apply (ρ σ : InvertibleMatrix n)
    (X : MatrixCarrier n) :
    (relativeModularEquiv ρ σ).symm X =
      ((ρ⁻¹ : InvertibleMatrix n) : MatrixCarrier n) * X *
      (σ : MatrixCarrier n) := by
  exact relativeModularInverse_apply ρ σ X

noncomputable def diagonalInvertible {n : ℕ} (p pinv : Fin n → ℂ)
    (h₁ : ∀ i, p i * pinv i = 1) (h₂ : ∀ i, pinv i * p i = 1) :
    InvertibleMatrix n :=
  { val := Matrix.diagonal p
    inv := Matrix.diagonal pinv
    val_inv := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [h₁]
      · simp [hij]
    inv_val := by
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
  have hqmat : (Matrix.diagonal q : MatrixCarrier n)⁻¹ =
      Matrix.diagonal qinv := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst b
      simp [hq]
    · simp [hab]
  have hqunit :
      (↑((diagonalInvertible q qinv hq hq')⁻¹ : InvertibleMatrix n) :
        MatrixCarrier n) = Matrix.diagonal qinv := by
    rfl
  rw [hqunit]
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
