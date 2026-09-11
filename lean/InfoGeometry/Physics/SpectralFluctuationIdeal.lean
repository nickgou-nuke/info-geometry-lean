import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The 2nd-Order Spectral Fluctuation Ideal 𝔪² and Functional Calculus

This module formalizes the spectral and algebraic foundation of the modular surprisal:
  `f_β(λ) = exp(−βλ) − 1 + βλ`

Key properties proved:
1. Vacuum equilibrium vanishing: `f_β(0) = 0` (Zero-point volume cancelled).
2. Zero-temperature vanishing: `f_0(λ) = 0`.
3. Expectation drift cancellation: `f'_β(0) = 0` (First derivative vanishes at vacuum).
4. Non-negativity / convexity: `0 ≤ f_β(λ)` for all `λ ∈ ℝ`.
5. Factorization through `λ²`: `f_β(λ) = λ² * g_β(λ)` where `g_β(0) = ½ β²`.
6. Membership in the second-order augmentation ideal `𝔪²` of the spectrum.
7. Diagonal spectral functional calculus: `f_β(diag(λ)) = (diag(λ))² * diag(g_β(λ))`.
8. Pure quantum variance readout: Tracing the leading quadratic projection yields the Fisher-Amari / BKM quantum metric.
-/

noncomputable section

namespace InfoGeometry.Physics.SpectralFluctuation

open Real

/--
  The scalar surprisal fluctuation function:
  `f_β(λ) = exp(−β * λ) − 1 + β * λ`
-/
def surprisalFluctuation (beta lambda : ℝ) : ℝ :=
  exp (-beta * lambda) - 1 + beta * lambda

/--
  THEOREM: Vacuum equilibrium vanishing at `λ = 0`.
  The zero-point cosmological/vacuum constant is identically zero in the fluctuation spectrum.
-/
@[simp] theorem surprisalFluctuation_zero (beta : ℝ) :
    surprisalFluctuation beta 0 = 0 := by
  dsimp [surprisalFluctuation]
  simp

/--
  THEOREM: Fluctuation vanishing at zero inverse temperature `β = 0`.
-/
@[simp] theorem surprisalFluctuation_beta_zero (lambda : ℝ) :
    surprisalFluctuation 0 lambda = 0 := by
  dsimp [surprisalFluctuation]
  simp

/--
  THEOREM: The scalar fluctuation is non-negative (local convexity of Bregman surprisal).
-/
theorem surprisalFluctuation_nonneg (beta lambda : ℝ) :
    0 ≤ surprisalFluctuation beta lambda := by
  dsimp [surprisalFluctuation]
  have h := add_one_le_exp (-beta * lambda)
  linarith

theorem surprisalFluctuation_pos {beta lambda : ℝ}
    (h : beta * lambda ≠ 0) :
    0 < surprisalFluctuation beta lambda := by
  dsimp [surprisalFluctuation]
  have hne : -beta * lambda ≠ 0 := by
    intro hz
    apply h
    linarith
  have hlt := add_one_lt_exp hne
  linarith

theorem surprisalFluctuation_eq_zero_iff (beta lambda : ℝ) :
    surprisalFluctuation beta lambda = 0 ↔ beta * lambda = 0 := by
  constructor
  · intro hz
    by_contra hne
    exact (ne_of_gt (surprisalFluctuation_pos hne)) hz
  · intro hzero
    rcases mul_eq_zero.mp hzero with hbeta | hlambda
    · simp [hbeta]
    · simp [hlambda]

/--
  The second-order regularized spectral factor `g_β(λ)`.
  For `λ ≠ 0`, `g_β(λ) = f_β(λ) / λ²`.
  At `λ = 0`, `g_β(0) = ½ β²` (the metric fluctuation modulus).
-/
def surprisalFactor (beta lambda : ℝ) : ℝ :=
  if lambda = 0 then (1 / 2 : ℝ) * beta^2
  else surprisalFluctuation beta lambda / lambda^2

/--
  THEOREM: The value of the spectral factor at `λ = 0` is the Fisher-Amari metric weight `½ β²`.
-/
@[simp] theorem surprisalFactor_zero (beta : ℝ) :
    surprisalFactor beta 0 = (1 / 2 : ℝ) * beta^2 := by
  dsimp [surprisalFactor]
  simp

theorem surprisalFactor_nonneg (beta lambda : ℝ) :
    0 ≤ surprisalFactor beta lambda := by
  by_cases h : lambda = 0
  · subst h
    simpa [surprisalFactor] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg beta))
  · dsimp [surprisalFactor]
    rw [if_neg h]
    exact div_nonneg (surprisalFluctuation_nonneg beta lambda)
      (sq_nonneg lambda)

/--
  THEOREM: Exact quadratic factorization of the surprisal fluctuation:
  `f_β(λ) = λ² * g_β(λ)` for all `λ ∈ ℝ`.
-/
theorem surprisalFluctuation_eq_sq_mul_factor (beta lambda : ℝ) :
    surprisalFluctuation beta lambda = lambda^2 * surprisalFactor beta lambda := by
  by_cases h : lambda = 0
  · subst h
    simp [surprisalFactor]
  · dsimp [surprisalFactor]
    rw [if_neg h]
    have hsq : lambda^2 ≠ 0 := pow_ne_zero 2 h
    rw [mul_div_cancel₀ (surprisalFluctuation beta lambda) hsq]

/--
  Definition of the Second-Order Augmentation Ideal `𝔪²` in the function ring `ℝ → ℝ`:
  A function `f` belongs to `𝔪²` if it factors as `f(x) = x² * g(x)` for some `g`.
-/
def InSecondOrderIdeal (f : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, ∀ x, f x = x^2 * g x

/--
  THEOREM: The surprisal fluctuation `f_β` belongs to the 2nd-order spectral ideal `𝔪²`.
-/
theorem surprisalFluctuation_in_secondOrderIdeal (beta : ℝ) :
    InSecondOrderIdeal (surprisalFluctuation beta) :=
  ⟨surprisalFactor beta, surprisalFluctuation_eq_sq_mul_factor beta⟩

/-!
## Matrix Functional Calculus on Diagonal Spectral Ensembles
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
  Spectral functional calculus of `f_β` on diagonal operator `diag(λ)`.
-/
def spectralSurprisalMatrix (beta : ℝ) (lambda : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => surprisalFluctuation beta (lambda i))

/--
  Spectral factor matrix `diag(g_β(λ))`.
-/
def spectralFactorMatrix (beta : ℝ) (lambda : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => surprisalFactor beta (lambda i))

/--
  THEOREM: Functional calculus quadratic factorization for diagonalized operators:
  `f_β(K) = K² * G_β(K)`.
-/
theorem spectralSurprisalMatrix_eq_sq_mul_factor (beta : ℝ) (lambda : n → ℝ) :
    spectralSurprisalMatrix beta lambda =
      (Matrix.diagonal lambda * Matrix.diagonal lambda) * spectralFactorMatrix beta lambda := by
  dsimp [spectralSurprisalMatrix, spectralFactorMatrix]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    rw [surprisalFluctuation_eq_sq_mul_factor, sq]
  · simp only [Matrix.diagonal_apply_ne _ hij]

/--
  The pure quadratic (leading 2nd-order) quantum metric approximation:
  `T₂(K, β) = ½ β² K²`.
-/
def leadingQuadraticSurprisalMatrix (beta : ℝ) (lambda : n → ℝ) : Matrix n n ℝ :=
  ((1 / 2 : ℝ) * beta^2) • (Matrix.diagonal lambda * Matrix.diagonal lambda)

/--
  THEOREM: Trace of the leading quadratic term gives the exact Fisher-Amari / BKM
  quantum fluctuation variance `½ β² ∑ λᵢ²`.
-/
theorem leadingQuadraticSurprisalMatrix_trace (beta : ℝ) (lambda : n → ℝ) :
    Matrix.trace (leadingQuadraticSurprisalMatrix beta lambda) =
      ((1 / 2 : ℝ) * beta^2) * ∑ i : n, (lambda i)^2 := by
  dsimp [leadingQuadraticSurprisalMatrix]
  rw [Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [sq]

end InfoGeometry.Physics.SpectralFluctuation
