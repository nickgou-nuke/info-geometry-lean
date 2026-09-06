import Mathlib

open Matrix

/-!
Determinant-sign grading for finite `2 × 2` real matrices.

This file formalizes:
* `superGrade A := SignType.sign (det A)`,
* multiplicativity `superGrade (A ⬝ B) = superGrade A * superGrade B`,
* explicit matrices `chiralParity = diag(1,-1)` and `modular_j`,
* the multiplication table induced by determinant signs,
* the trace identity `Tr(chiralParity · ρ) = ρ₀₀ - ρ₁₁`.
-/

noncomputable section

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Diagonal parity matrix `diag(1,-1)`. -/
def chiralParity : M2R := !![1, 0; 0, -1]

/-- Off-diagonal swap matrix. -/
def modular_j : M2R := !![0, 1; 1, 0]

/-- Product of the swap and diagonal parity matrices. -/
def emergentK : M2R := modular_j * chiralParity

/-- Determinant-sign grading of a `2 × 2` real matrix. -/
def superGrade (A : M2R) : SignType := SignType.sign A.det

/-- Determinant-signed grading is multiplicative by `det`-multiplicativity. -/
theorem superGrade_mul (A B : M2R) :
    superGrade (A * B) = superGrade A * superGrade B := by
  change SignType.sign ((A * B).det) = SignType.sign A.det * SignType.sign B.det
  rw [Matrix.det_mul]
  simpa using (sign_mul (A.det) (B.det))

/-- Identity is even (`sign 1 = 1`). -/
theorem superGrade_id : superGrade (1 : M2R) = 1 := by
  simp [superGrade]

/-- `ε` is an odd involution (`ε² = I`, `det ε = -1`). -/
theorem chiralParity_sq : chiralParity * chiralParity = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralParity]

theorem chiralParity_det : chiralParity.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [chiralParity]

theorem superGrade_chiralParity : superGrade chiralParity = (-1 : SignType) := by
  simp [superGrade, chiralParity_det]

/-- Sheet swap is odd (`J² = I`, `det J = -1`). -/
theorem modular_j_sq : modular_j * modular_j = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modular_j]

theorem modular_j_det : modular_j.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [modular_j]

theorem superGrade_modular_j : superGrade modular_j = (-1 : SignType) := by
  simp [superGrade, modular_j_det]

/-- `J` and `ε` anticommute (`J ε = - ε J`). -/
theorem modular_j_chiralParity_anticomm : modular_j * chiralParity = -(chiralParity * modular_j) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modular_j, chiralParity]

/-- The emergent complex `K = J ε` is even (`K² = -I`, `det K = 1`). -/
theorem emergentK_sq : emergentK * emergentK = -(1 : M2R) := by
  rw [emergentK]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modular_j, chiralParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem emergentK_det : emergentK.det = 1 := by
  simp [emergentK, Matrix.det_mul, modular_j_det, chiralParity_det]

theorem superGrade_emergentK : superGrade emergentK = (1 : SignType) := by
  simp [superGrade, emergentK_det]

/-- Multiplication rules in grading language:
`even * even = even`, `even * odd = odd`, `odd * even = odd`, `odd * odd = even`. -/
theorem even_even (A B : M2R)
    (hA : superGrade A = (1 : SignType)) (hB : superGrade B = (1 : SignType)) :
    superGrade (A * B) = (1 : SignType) := by
  simpa [hA, hB] using (superGrade_mul A B)

theorem even_odd (A B : M2R)
    (hA : superGrade A = (1 : SignType)) (hB : superGrade B = (-1 : SignType)) :
    superGrade (A * B) = (-1 : SignType) := by
  simpa [hA, hB] using (superGrade_mul A B)

theorem odd_even (A B : M2R)
    (hA : superGrade A = (-1 : SignType)) (hB : superGrade B = (1 : SignType)) :
    superGrade (A * B) = (-1 : SignType) := by
  simpa [hA, hB] using (superGrade_mul A B)

theorem odd_odd (A B : M2R)
    (hA : superGrade A = (-1 : SignType)) (hB : superGrade B = (-1 : SignType)) :
    superGrade (A * B) = (1 : SignType) := by
  simpa [hA, hB] using (superGrade_mul A B)

/-- Graded trace `Tr(chiralParity · ρ)`. -/
def superTrace (ρ : M2R) : ℝ := Matrix.trace (chiralParity * ρ)

/-- In coordinates the graded trace is `ρ₀₀ - ρ₁₁`. -/
theorem superTrace_formula (ρ : M2R) :
    superTrace ρ = ρ 0 0 - ρ 1 1 := by
  have h00 : (chiralParity * ρ) 0 0 = ρ 0 0 := by
    simp [chiralParity, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (chiralParity * ρ) 1 1 = -ρ 1 1 := by
    simp [chiralParity, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    superTrace ρ = (chiralParity * ρ) 0 0 + (chiralParity * ρ) 1 1 := by
      simp [superTrace, Matrix.trace]
    _ = ρ 0 0 - ρ 1 1 := by
      rw [h00, h11]
      ring

/-- The graded trace vanishes when the two diagonal entries agree. -/
theorem superTrace_vanishing_of_sheet_balance (ρ : M2R) (h : ρ 0 0 = ρ 1 1) :
    superTrace ρ = 0 := by
  rw [superTrace_formula ρ]
  linarith

/-- Scalar diagonal matrix. -/
def vacuumDensity (w : ℝ) : M2R := !![w, 0; 0, w]

theorem superTrace_vacuum (w : ℝ) : superTrace (vacuumDensity w) = 0 := by
  simp [vacuumDensity, superTrace, chiralParity]

/-- The two-sheeted parity package in one statement. -/
theorem superGrade_table :
    superGrade modular_j = (-1 : SignType) ∧
      superGrade chiralParity = (-1 : SignType) ∧
      superGrade emergentK = (1 : SignType) := by
  constructor
  · exact superGrade_modular_j
  · constructor
    · exact superGrade_chiralParity
    · exact superGrade_emergentK

/-- Consolidated determinant-sign grading facts. -/
theorem determinant_supergrading_central_package :
    (∀ A B : M2R, superGrade (A * B) = superGrade A * superGrade B) ∧
      superGrade modular_j = (-1 : SignType) ∧
      superGrade chiralParity = (-1 : SignType) ∧
      superGrade emergentK = (1 : SignType) := by
  constructor
  · exact superGrade_mul
  · constructor
    · exact superGrade_modular_j
    · constructor
      · exact superGrade_chiralParity
      · exact superGrade_emergentK
