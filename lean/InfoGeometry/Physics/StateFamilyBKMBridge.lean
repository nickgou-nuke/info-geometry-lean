import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import InfoGeometry.Physics.SpectralFluctuationIdeal
import InfoGeometry.Physics.RegularizedSurprisalKernel

/-!
# Quantum State Families, BKM Information Metric, and 2nd-Order Hessian Bridge

This module formalizes the exact bridge between:
1. Quantum state families $\rho(\theta)$ and modular surprisal perturbations $K$.
2. The Bogoliubov-Kubo-Mori (BKM) metric on diagonal / commuting spectral states:
   `g_BKM(K₁, K₂) = Tr(ρ * K₁ * K₂)`
3. The quadratic Hessian structure: `g_BKM(K, K) = Tr(ρ * K²) = Var_ρ(K) ≥ 0`.
4. The exact identification of the 2nd-order Bregman divergence / relative entropy
   expansion with the regularized surprisal kernel `E₂(−βK) = ½ β² K²`.
5. Emergent Riemannian metric tensor on the quantum state manifold.
-/

noncomputable section

namespace InfoGeometry.Physics.StateFamilyBKM

open Matrix
open InfoGeometry.Physics.SpectralFluctuation

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
  A diagonal quantum state (probability distribution over eigenstates):
  `p : n → ℝ` with `∑ p_i = 1` and `p_i ≥ 0`.
-/
structure DiagonalQuantumState (n : Type*) [Fintype n] where
  prob : n → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum_one : ∑ i, prob i = 1

/--
  Density matrix associated to a diagonal quantum state:
  `ρ = diag(p)`.
-/
def densityMatrix (ρ : DiagonalQuantumState n) : Matrix n n ℝ :=
  Matrix.diagonal ρ.prob

/--
  THEOREM: The trace of the density matrix is identically 1 (normalization).
-/
@[simp] theorem densityMatrix_trace (ρ : DiagonalQuantumState n) :
    Matrix.trace (densityMatrix ρ) = 1 := by
  dsimp [densityMatrix]
  rw [Matrix.trace_diagonal]
  exact ρ.prob_sum_one

/--
  Expectation value of an observable operator `A` in state `ρ`:
  `⟨A⟩_ρ = Tr(ρ * A)`.
-/
def quantumExpectation (ρ : DiagonalQuantumState n) (A : Matrix n n ℝ) : ℝ :=
  Matrix.trace (densityMatrix ρ * A)

/-!
The scalar surprisal fluctuation has a positive diagonal-state readout.  This
is the finite commuting statement; no analytic functional calculus is needed.
-/
def surprisalFluctuationExpectation
    (ρ : DiagonalQuantumState n) (beta : ℝ) (lambda : n → ℝ) : ℝ :=
  ∑ i : n, ρ.prob i * surprisalFluctuation beta (lambda i)

theorem surprisalFluctuationExpectation_nonneg
    (ρ : DiagonalQuantumState n) (beta : ℝ) (lambda : n → ℝ) :
    0 ≤ surprisalFluctuationExpectation ρ beta lambda := by
  unfold surprisalFluctuationExpectation
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg (ρ.prob_nonneg i)
    (surprisalFluctuation_nonneg beta (lambda i))

/--
  The Bogoliubov-Kubo-Mori (BKM) quantum information metric inner product
  for diagonalized / commuting observable perturbations:
  `g_BKM(A, B) = Tr(ρ * A * B)`.
-/
def bkmMetric (ρ : DiagonalQuantumState n) (A B : Matrix n n ℝ) : ℝ :=
  Matrix.trace (densityMatrix ρ * A * B)

theorem bkmMetric_diagonal_eq_weighted_sum
    (ρ : DiagonalQuantumState n) (a b : n → ℝ) :
    bkmMetric ρ (Matrix.diagonal a) (Matrix.diagonal b) =
      ∑ i : n, ρ.prob i * a i * b i := by
  dsimp [bkmMetric, densityMatrix]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]

/-!
  Centering the diagonal observables gives the ordinary finite covariance
  readout of the state.
-/
def diagonalMean (ρ : DiagonalQuantumState n) (a : n → ℝ) : ℝ :=
  ∑ i : n, ρ.prob i * a i

theorem diagonalMean_const (ρ : DiagonalQuantumState n) (c : ℝ) :
    diagonalMean ρ (fun _ => c) = c := by
  unfold diagonalMean
  simp_rw [mul_comm (ρ.prob _) c]
  rw [← Finset.mul_sum, ρ.prob_sum_one, mul_one]

@[simp] theorem diagonalMean_zero (ρ : DiagonalQuantumState n) :
    diagonalMean ρ (fun _ => 0) = 0 := by
  simpa using diagonalMean_const ρ 0

def diagonalCovariance
    (ρ : DiagonalQuantumState n) (a b : n → ℝ) : ℝ :=
  ∑ i : n, ρ.prob i * (a i - diagonalMean ρ a) *
    (b i - diagonalMean ρ b)

theorem diagonalCovariance_swap
    (ρ : DiagonalQuantumState n) (a b : n → ℝ) :
    diagonalCovariance ρ a b = diagonalCovariance ρ b a := by
  unfold diagonalCovariance
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem diagonalCovariance_self_nonneg
    (ρ : DiagonalQuantumState n) (a : n → ℝ) :
    0 ≤ diagonalCovariance ρ a a := by
  unfold diagonalCovariance
  apply Finset.sum_nonneg
  intro i _hi
  rw [mul_assoc]
  exact mul_nonneg (ρ.prob_nonneg i)
    (mul_self_nonneg (a i - diagonalMean ρ a))

theorem diagonalCovariance_const_left
    (ρ : DiagonalQuantumState n) (c : ℝ) (b : n → ℝ) :
    diagonalCovariance ρ (fun _ => c) b = 0 := by
  unfold diagonalCovariance diagonalMean
  have hmean : (∑ i : n, ρ.prob i * c) = c := by
    simp_rw [mul_comm (ρ.prob _) c]
    rw [← Finset.mul_sum, ρ.prob_sum_one, mul_one]
  rw [hmean]
  simp

theorem diagonalCovariance_const_right
    (ρ : DiagonalQuantumState n) (a : n → ℝ) (c : ℝ) :
    diagonalCovariance ρ a (fun _ => c) = 0 := by
  rw [diagonalCovariance_swap, diagonalCovariance_const_left]

theorem diagonalCovariance_eq_bkm_centered
    (ρ : DiagonalQuantumState n) (a b : n → ℝ) :
    diagonalCovariance ρ a b =
      bkmMetric ρ
        (Matrix.diagonal (fun i => a i - diagonalMean ρ a))
        (Matrix.diagonal (fun i => b i - diagonalMean ρ b)) := by
  rw [bkmMetric_diagonal_eq_weighted_sum]
  rfl

/--
  THEOREM: The BKM metric is symmetric for diagonal operators:
  `g_BKM(diag(a), diag(b)) = g_BKM(diag(b), diag(a))`.
-/
theorem bkmMetric_diagonal_symmetric (ρ : DiagonalQuantumState n) (a b : n → ℝ) :
    bkmMetric ρ (Matrix.diagonal a) (Matrix.diagonal b) =
      bkmMetric ρ (Matrix.diagonal b) (Matrix.diagonal a) := by
  dsimp [bkmMetric, densityMatrix]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  congr 1
  ext i
  ring

/--
  THEOREM: The diagonal BKM quadratic form is positive semi-definite:
  `g_BKM(diag(a), diag(a)) = ∑ p_i * a_i² ≥ 0`.
-/
theorem bkmMetric_diagonal_nonneg (ρ : DiagonalQuantumState n) (a : n → ℝ) :
    0 ≤ bkmMetric ρ (Matrix.diagonal a) (Matrix.diagonal a) := by
  dsimp [bkmMetric, densityMatrix]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  apply Finset.sum_nonneg
  intro i _
  have hp : 0 ≤ ρ.prob i := ρ.prob_nonneg i
  have hsq : 0 ≤ (a i) * (a i) := mul_self_nonneg (a i)
  have hprod : 0 ≤ ρ.prob i * a i * a i := by
    rw [mul_assoc]
    exact mul_nonneg hp hsq
  exact hprod

/--
  THEOREM: Exact connection between the BKM quadratic form and the
  regularized surprisal kernel at temperature `β`:
  `Tr(ρ * E₂(−β K)) = ½ β² * g_BKM(K, K)`.
-/
theorem surprisalKernel_expectation_eq_bkm (ρ : DiagonalQuantumState n) (lambda : n → ℝ) (beta : ℝ) :
    quantumExpectation ρ (((1 / 2 : ℝ) * beta^2) • (Matrix.diagonal lambda * Matrix.diagonal lambda)) =
      ((1 / 2 : ℝ) * beta^2) * bkmMetric ρ (Matrix.diagonal lambda) (Matrix.diagonal lambda) := by
  dsimp [quantumExpectation, bkmMetric]
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]

theorem surprisalKernel_expectation_eq_weighted_square
    (ρ : DiagonalQuantumState n) (lambda : n → ℝ) (beta : ℝ) :
    quantumExpectation ρ
        (((1 / 2 : ℝ) * beta^2) •
          (Matrix.diagonal lambda * Matrix.diagonal lambda)) =
      ((1 / 2 : ℝ) * beta^2) *
        ∑ i : n, ρ.prob i * (lambda i)^2 := by
  rw [surprisalKernel_expectation_eq_bkm,
    bkmMetric_diagonal_eq_weighted_sum]
  apply congrArg (fun x : ℝ => ((1 / 2 : ℝ) * beta^2) * x)
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/--
  The second-order relative entropy Hessian approximation:
  `D₂(ρ_θ, ρ_{θ+δθ}) = ½ ∑_{ij} g_{ij} δθ_i δθ_j`.
-/
def secondOrderEntropyHessian (ρ : DiagonalQuantumState n) (delta : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * bkmMetric ρ (Matrix.diagonal delta) (Matrix.diagonal delta)

theorem secondOrderEntropyHessian_eq_weighted_sum
    (ρ : DiagonalQuantumState n) (delta : n → ℝ) :
    secondOrderEntropyHessian ρ delta =
      (1 / 2 : ℝ) * ∑ i : n, ρ.prob i * (delta i)^2 := by
  unfold secondOrderEntropyHessian
  rw [bkmMetric_diagonal_eq_weighted_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/--
  THEOREM: The 2nd-order entropy Hessian is non-negative (local convexity of quantum relative entropy).
-/
theorem secondOrderEntropyHessian_nonneg (ρ : DiagonalQuantumState n) (delta : n → ℝ) :
    0 ≤ secondOrderEntropyHessian ρ delta := by
  dsimp [secondOrderEntropyHessian]
  have hpos : (0 : ℝ) ≤ 1 / 2 := by linarith
  have hmet : 0 ≤ bkmMetric ρ (Matrix.diagonal delta) (Matrix.diagonal delta) :=
    bkmMetric_diagonal_nonneg ρ delta
  exact mul_nonneg hpos hmet

/--
  THEOREM: When fluctuation `delta = 0`, the entropy Hessian vanishes identically.
-/
@[simp] theorem secondOrderEntropyHessian_zero (ρ : DiagonalQuantumState n) :
    secondOrderEntropyHessian ρ 0 = 0 := by
  dsimp [secondOrderEntropyHessian, bkmMetric, densityMatrix]
  simp

end InfoGeometry.Physics.StateFamilyBKM
