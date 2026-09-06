import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Emergent Spacetime Soldering Bridge and Frobenius-Schur Metric Spectrum

This module formalizes the 4-level soldering cascade from split-octonionic Witt
data to emergent Minkowski spacetime:

1. **Pauli Soldering Map:**
   $$\theta(x) = x^0 \sigma_0 + x^1 \sigma_1 + x^2 \sigma_2 + x^3 \sigma_3 =
     \begin{pmatrix} x^0 + x^3 & x^1 - i x^2 \\ x^1 + i x^2 & x^0 - x^3 \end{pmatrix}$$

2. **Minkowski Metric as the Soldering Determinant:**
   $$\det(\theta(x)) = (x^0)^2 - (x^1)^2 - (x^2)^2 - (x^3)^2 = \eta_{\mu\nu} x^\mu x^\nu$$

3. **Frobenius-Schur Signature Spectrum:**
   The metric signature is governed by the Peirce defect fermion number $F_P$:
   $$\nu(\mu) = (-1)^{F_P(\mu)} = \begin{cases} +1, & \mu = 0 \text{ (Time / Real axis)} \\ -1, & \mu \in \{1,2,3\} \text{ (Space / Quaternionic axes)} \end{cases}$$

The finite algebraic identities below are checked by Lean; geometric and
physical interpretations require the explicit carrier and representation data.
-/

noncomputable section

namespace InfoGeometry.Canonical.EmergentSpacetimeSolderingBridge

open Matrix Complex

/-- 4D Minkowski vector over ℝ -/
abbrev FourVector := Fin 4 → ℝ
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrix basis σ₀, σ₁, σ₂, σ₃ -/
def sigma0 : Mat2C := !![1, 0; 0, 1]
def sigma1 : Mat2C := !![0, 1; 1, 0]
def sigma2 : Mat2C := !![0, -I; I, 0]
def sigma3 : Mat2C := !![1, 0; 0, -1]

/-- 🏆 THEOREM 1: Explicit Matrix Elements of Pauli Soldering θ(x) -/
def pauliSoldering (x : FourVector) : Mat2C :=
  (x 0 : ℂ) • sigma0 + (x 1 : ℂ) • sigma1 + (x 2 : ℂ) • sigma2 + (x 3 : ℂ) • sigma3

/-- Matrix representation of Pauli soldering -/
theorem pauliSoldering_eq (x : FourVector) :
    pauliSoldering x = !![(x 0 + x 3 : ℂ), (x 1 - I * x 2 : ℂ); (x 1 + I * x 2 : ℂ), (x 0 - x 3 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliSoldering, sigma0, sigma1, sigma2, sigma3] <;> ring

theorem pauliSoldering_add (x y : FourVector) :
    pauliSoldering (x + y) = pauliSoldering x + pauliSoldering y := by
  rw [pauliSoldering_eq, pauliSoldering_eq, pauliSoldering_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem pauliSoldering_smul (r : ℝ) (x : FourVector) :
    pauliSoldering (r • x) = (r : ℂ) • pauliSoldering x := by
  rw [pauliSoldering_eq, pauliSoldering_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The finite Pauli soldering map as an `ℝ`-linear map. -/
def pauliSolderingLinear : FourVector →ₗ[ℝ] Mat2C where
  toFun := pauliSoldering
  map_add' x y := pauliSoldering_add x y
  map_smul' r x := by
    rw [pauliSoldering_smul]
    ext i j
    simp [Matrix.smul_apply]

@[simp] theorem pauliSolderingLinear_apply (x : FourVector) :
    pauliSolderingLinear x = pauliSoldering x := rfl

/-- Quadratic Minkowski norm η_{1,3}(x) = (x⁰)² - (x¹)² - (x²)² - (x³)² -/
def minkowskiQuadraticForm (x : FourVector) : ℝ :=
  (x 0)^2 - (x 1)^2 - (x 2)^2 - (x 3)^2

/-- 🏆 THEOREM 2: Emergent Spacetime Metric as the Soldering Determinant:
    $$\det(\theta(x)) = \eta_{\mu\nu} x^\mu x^\nu$$ -/
theorem det_pauliSoldering_eq_minkowski (x : FourVector) :
    (pauliSoldering x).det = (minkowskiQuadraticForm x : ℂ) := by
  rw [pauliSoldering_eq, Matrix.det_fin_two]
  have hI : I * I = -1 := by
    have h : I ^ 2 = -1 := Complex.I_sq
    rw [sq] at h
    exact h
  calc
    (↑(x 0) + ↑(x 3)) * (↑(x 0) - ↑(x 3)) - (↑(x 1) - I * ↑(x 2)) * (↑(x 1) + I * ↑(x 2)) =
      ((↑(x 0) : ℂ)^2 - (↑(x 3))^2) - ((↑(x 1))^2 - (I * ↑(x 2))^2) := by ring
    _ = ((↑(x 0) : ℂ)^2 - (↑(x 3))^2) - ((↑(x 1))^2 - (I * I) * (↑(x 2))^2) := by ring
    _ = ((↑(x 0) : ℂ)^2 - (↑(x 3))^2) - ((↑(x 1))^2 - (-1) * (↑(x 2))^2) := by rw [hI]
    _ = ((↑(x 0) : ℂ)^2 - (↑(x 1))^2 - (↑(x 2))^2 - (↑(x 3))^2) := by ring
    _ = (((x 0)^2 - (x 1)^2 - (x 2)^2 - (x 3)^2 : ℝ) : ℂ) := by push_cast; rfl

theorem pauliSolderingLinear_injective :
    Function.Injective pauliSolderingLinear := by
  intro x y h
  change pauliSoldering x = pauliSoldering y at h
  rw [pauliSoldering_eq, pauliSoldering_eq] at h
  have h00 := congrArg (fun M : Mat2C => M 0 0) h
  have h01 := congrArg (fun M : Mat2C => M 0 1) h
  have h10 := congrArg (fun M : Mat2C => M 1 0) h
  have h11 := congrArg (fun M : Mat2C => M 1 1) h
  funext i
  fin_cases i
  · have hsum : (x 0 : ℂ) + x 3 = y 0 + y 3 := by simpa using h00
    have hdiff : (x 0 : ℂ) - x 3 = y 0 - y 3 := by simpa using h11
    have hsumR := congrArg Complex.re hsum
    have hdiffR := congrArg Complex.re hdiff
    norm_num at hsumR hdiffR
    simpa using (show x 0 = y 0 by linarith)
  · have hsum : (x 1 : ℂ) - I * x 2 = y 1 - I * y 2 := by simpa using h01
    have hdiff : (x 1 : ℂ) + I * x 2 = y 1 + I * y 2 := by simpa using h10
    have hsumR := congrArg Complex.re hsum
    have hdiffR := congrArg Complex.re hdiff
    norm_num at hsumR hdiffR
    simpa using (show x 1 = y 1 by linarith)
  · have hsum : (x 1 : ℂ) - I * x 2 = y 1 - I * y 2 := by simpa using h01
    have hdiff : (x 1 : ℂ) + I * x 2 = y 1 + I * y 2 := by simpa using h10
    have hsumI := congrArg Complex.im hsum
    have hdiffI := congrArg Complex.im hdiff
    norm_num at hsumI hdiffI
    simpa using (show x 2 = y 2 by linarith)
  · have hsum : (x 0 : ℂ) + x 3 = y 0 + y 3 := by simpa using h00
    have hdiff : (x 0 : ℂ) - x 3 = y 0 - y 3 := by simpa using h11
    have hsumR := congrArg Complex.re hsum
    have hdiffR := congrArg Complex.re hdiff
    norm_num at hsumR hdiffR
    simpa using (show x 3 = y 3 by linarith)

theorem pauliSoldering_det_eq_zero_iff (x : FourVector) :
    (pauliSoldering x).det = 0 ↔ minkowskiQuadraticForm x = 0 := by
  rw [det_pauliSoldering_eq_minkowski]
  exact_mod_cast (show (minkowskiQuadraticForm x : ℂ) = 0 ↔
    minkowskiQuadraticForm x = 0 by simp)

/-- Peirce defect fermion number F_P(μ) on coordinate directions -/
def peirceFermionNumber (μ : Fin 4) : ℕ :=
  if μ = 0 then 0 else 1

/-- Frobenius-Schur indicator spectrum ν(μ) = (-1)^{F_P(μ)} -/
def frobeniusSchurSpectrum (μ : Fin 4) : ℝ :=
  if μ = 0 then 1 else -1

/-- 🏆 THEOREM 3: Frobenius-Schur Spectrum matches (-1)^{F_P(μ)} -/
theorem frobeniusSchur_eq_neg_one_pow_fermionNumber (μ : Fin 4) :
    frobeniusSchurSpectrum μ = (-1 : ℝ) ^ (peirceFermionNumber μ) := by
  fin_cases μ
  · rfl
  · dsimp [frobeniusSchurSpectrum, peirceFermionNumber]; rw [pow_one]
  · dsimp [frobeniusSchurSpectrum, peirceFermionNumber]; rw [pow_one]
  · dsimp [frobeniusSchurSpectrum, peirceFermionNumber]; rw [pow_one]

/-- Polarized Minkowski Bilinear Form from Frobenius-Schur Spectrum -/
def emergentMinkowskiBilinear (x y : FourVector) : ℝ :=
  ∑ μ : Fin 4, frobeniusSchurSpectrum μ * x μ * y μ

theorem emergentMinkowskiBilinear_eq_minkowskiPolarization
    (x y : FourVector) :
    emergentMinkowskiBilinear x y =
      x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  have h2 : (2 : Fin 4) ≠ 0 := by decide
  have h3 : (3 : Fin 4) ≠ 0 := by decide
  dsimp [emergentMinkowskiBilinear, frobeniusSchurSpectrum]
  norm_num [Fin.sum_univ_four, Fin.isValue, h2, h3]
  ring

/-- 🏆 THEOREM 4: The Emergent Minkowski Metric matches the Polarized Soldering Metric -/
theorem emergentMinkowskiBilinear_self (x : FourVector) :
    emergentMinkowskiBilinear x x = minkowskiQuadraticForm x := by
  dsimp [emergentMinkowskiBilinear, minkowskiQuadraticForm, frobeniusSchurSpectrum]
  simp only [Fin.sum_univ_four, Fin.isValue]
  dsimp
  ring

theorem det_pauliSoldering_polarization (x y : FourVector) :
    (pauliSoldering (x + y)).det - (pauliSoldering x).det -
        (pauliSoldering y).det =
      (2 * emergentMinkowskiBilinear x y : ℂ) := by
  rw [det_pauliSoldering_eq_minkowski, det_pauliSoldering_eq_minkowski,
    det_pauliSoldering_eq_minkowski]
  rw [emergentMinkowskiBilinear_eq_minkowskiPolarization]
  simp only [minkowskiQuadraticForm, Pi.add_apply]
  push_cast
  ring

theorem emergentMinkowskiBilinear_comm (x y : FourVector) :
    emergentMinkowskiBilinear x y = emergentMinkowskiBilinear y x := by
  unfold emergentMinkowskiBilinear
  apply Finset.sum_congr rfl
  intro μ hμ
  ring

theorem emergentMinkowskiBilinear_add_left (x y z : FourVector) :
    emergentMinkowskiBilinear (x + y) z =
      emergentMinkowskiBilinear x z + emergentMinkowskiBilinear y z := by
  unfold emergentMinkowskiBilinear
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ hμ
  ring

theorem emergentMinkowskiBilinear_smul_left (c : ℝ) (x y : FourVector) :
    emergentMinkowskiBilinear (c • x) y =
      c • emergentMinkowskiBilinear x y := by
  unfold emergentMinkowskiBilinear
  rw [smul_eq_mul]
  simp only [Pi.smul_apply]
  calc
    (∑ μ, frobeniusSchurSpectrum μ * (c * x μ) * y μ) =
        ∑ μ, c * (frobeniusSchurSpectrum μ * x μ * y μ) := by
          apply Finset.sum_congr rfl
          intro μ hμ
          ring
    _ = c * ∑ μ, frobeniusSchurSpectrum μ * x μ * y μ := by
      rw [Finset.mul_sum]

/-- Hermiticity of Pauli Soldering -/
theorem pauliSoldering_is_hermitian (x : FourVector) :
    (pauliSoldering x).conjTranspose = pauliSoldering x := by
  rw [pauliSoldering_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [Matrix.conjTranspose, Complex.ext_iff]

end InfoGeometry.Canonical.EmergentSpacetimeSolderingBridge
