import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Causal.CausalAlgebra

open Matrix

/-!
# CausalSpectralTriple — The 2×2 Causal Model as a Spectral Triple

This file constructs the two-point spectral triple underlying the 2×2
causal orientation algebra.

## The Two-Point Spectral Triple

| Symbol | Matrix | Meaning |
|--------|--------|---------|
| `A`    | `diag(x₀, x₁)` | Two-point function algebra C({0,1}) |
| `H`    | ℝ² | Fibre with Euclidean inner product |
| `γ`    | `σ₃` | Chiral grading (even dimension) |
| `J`    | `Oℝ = σ₁` | Real structure / charge conjugation |
| `D`    | 0 | Zero Dirac (ultra-local point) |

## Connection to the Causal Algebra

The real structure J = Oℝ is precisely the causal orientation.
The causal projectors d = (1+J)/2, δ = (1-J)/2 coincide with the
±1 spectral projections of the real structure.
-/

set_option autoImplicit false

namespace InfoGeometry.Causal.SpectralTriple

open InfoGeometry.Causal.Algebra

/-! ## 1. The Operators -/

/-- The causal orientation Oℝ as the real structure J. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := Oℝ

/-- The chiral grading γ = σ₃ (diagonal Pauli). -/
def γ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The zero Dirac operator — the ultra-local limit. -/
def D : Matrix (Fin 2) (Fin 2) ℝ := 0

/-- The identity operator. -/
def I : Matrix (Fin 2) (Fin 2) ℝ := 1

/-! ## 2. The Represented Algebra — Diagonal Matrices -/

/-- Diagonal matrix from two scalars. -/
def diag (x₀ x₁ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x₀, 0; 0, x₁]

/-- Representation of the two-point algebra A ≅ C({0,1}) on ℝ². -/
def ρ (x₀ x₁ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diag x₀ x₁

/-- Opposite representation via J. -/
def ρ_op (x₀ x₁ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  J * ρ x₀ x₁ * J

/-! ## 3. Spectral Triple Axioms -/

theorem chi_sq_eq_one : γ * γ = I := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [γ, I, one_apply]

theorem J_sq_eq_one : J * J = I :=
  Oℝ_mul_Oℝ

theorem J_chi_anticommutes : J * γ = -(γ * J) := by
  ext i j; fin_cases i <;> fin_cases j
  · simp [J, γ, Oℝ, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring
  · simp [J, γ, Oℝ, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring
  · simp [J, γ, Oℝ, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring
  · simp [J, γ, Oℝ, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring

/-- With D = 0, the oddness condition is trivial. -/
theorem D_odd : D * γ + γ * D = 0 := by
  simp [D]

/-- J commutes with D (both are 0 on one side). -/
theorem J_D_commute : J * D = D * J := by
  simp [D]

/-- The matrix Oℝ is symmetric. -/
theorem Oℝ_symmetric : (Oℝ : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = Oℝ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Oℝ]

/-! ## 4. Order Zero and Order One Conditions -/

/-- Order zero: [ρ(a), ρ_op(b)] = 0 for all a, b ∈ A. -/
theorem order_zero_holds (x₀ x₁ y₀ y₁ : ℝ) :
    ρ x₀ x₁ * ρ_op y₀ y₁ = ρ_op y₀ y₁ * ρ x₀ x₁ := by
  ext i j; fin_cases i <;> fin_cases j
  · simp [ρ, ρ_op, J, Oℝ, diag, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring
  · simp [ρ, ρ_op, J, Oℝ, diag, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring
  · simp [ρ, ρ_op, J, Oℝ, diag, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring
  · simp [ρ, ρ_op, J, Oℝ, diag, Matrix.mul_apply, one_apply, Fin.sum_univ_two]; try ring

/-- Order one: [D, ρ(a)] · ρ_op(b) = ρ_op(b) · [D, ρ(a)], trivially true since D = 0. -/
theorem order_one_holds (x₀ x₁ y₀ y₁ : ℝ) :
    (D * ρ x₀ x₁ - ρ x₀ x₁ * D) * ρ_op y₀ y₁ = ρ_op y₀ y₁ * (D * ρ x₀ x₁ - ρ x₀ x₁ * D) := by
  simp [D]

/-! ## 5. Connection to the Causal Projectors -/

/-- The projector (1+J)/2 = dℝ is the future causal projector. -/
theorem d_from_triple : (1/2 : ℝ) • (I + J) = dℝ := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [J, I, dℝ, Oℝ]

/-- The projector (1-J)/2 = δℝ is the past causal projector. -/
theorem δ_from_triple : (1/2 : ℝ) • (I - J) = δℝ := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [J, I, δℝ, Oℝ]

/-- The projectors sum to identity: d + δ = I. -/
theorem projectors_sum_to_one : dℝ + δℝ = I := by
  calc
    dℝ + δℝ = ((1/2 : ℝ) • (I + J)) + ((1/2 : ℝ) • (I - J)) := by
      rw [← d_from_triple, ← δ_from_triple]
    _ = I := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [I, J, Oℝ]

/-- Characteristic polynomial: det(γ - s·I) = s² - 1. -/
theorem det_spectrum (s : ℝ) : det (γ - s • I) = s ^ 2 - 1 := by
  simp [γ, I, Matrix.det_fin_two, sub_apply, smul_apply]
  ring_nf

end InfoGeometry.Causal.SpectralTriple
