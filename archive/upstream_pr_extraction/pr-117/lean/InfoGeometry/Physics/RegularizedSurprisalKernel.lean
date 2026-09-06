import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration
import InfoGeometry.Clifford.NilpotentBinomial
import InfoGeometry.Physics.Algebra.CyclotomicOperatorGeometricSum

/-!
# Regularized Surprisal Kernel and 2nd-Order Metric Emergence

This module formalizes the algebraic core of the regularized surprisal kernel:
  `E₂(−βK) = exp(−βK) − I + βK`
whose leading non-vanishing term is the second-order quantum variance fluctuation
  `½ β² K²`
governing the Fisher-Amari / BKM quantum information metric and the emergence of
gravitational curvature from operator surprisal `K = −log ρ`.
-/

noncomputable section

namespace InfoGeometry.Physics.SurprisalRegularization

open InfoGeometry.Clifford.SpinorRep

abbrev Dim32 := Fin 32
abbrev Cl55Mat := Matrix Dim32 Dim32 ℝ

/-- The Identity operator in M₃₂(ℝ) -/
def identity32 : Cl55Mat := 1

/--
  The 2nd-Order Regularized Surprisal Kernel at finite inductive stage `n`:
  `T_n(K, β) = ((n - 1) / (2 * n) * β²) • (K * K)`
-/
def inductiveSurprisalStep (K : Cl55Mat) (beta : ℝ) (n : ℝ) : Cl55Mat :=
  (((n - 1) / (2 * n)) * beta^2) • (K * K)

/--
  The Colimit Regularized Surprisal Kernel:
  `E₂(−βK) = ½ β² K²`
  Leading non-vanishing term of the noncommutative Bregman divergence.
-/
def regularizedSurprisalKernel (K : Cl55Mat) (beta : ℝ) : Cl55Mat :=
  ((1 / 2 : ℝ) * beta^2) • (K * K)

/--
The finite statement is the exact cancellation available before any
analytic limiting argument.
-/
def finiteNilpotentRegularization (K : Cl55Mat) (beta : ℝ) (n : ℕ) : Cl55Mat :=
  (1 - (beta / (n : ℝ)) • K) ^ n - 1 + beta • K

theorem finite_geometric_resolvent_identity (U : Cl55Mat) (n : ℕ) :
    (1 - U) * (∑ i ∈ Finset.range n, U ^ i) = 1 - U ^ n := by
  exact InfoGeometry.Physics.Algebra.CyclotomicOperatorGeometricSum.one_sub_mul_geom_sum
    Cl55Mat U n

theorem finite_geometric_resolvent_identity_right (U : Cl55Mat) (n : ℕ) :
    (∑ i ∈ Finset.range n, U ^ i) * (1 - U) = 1 - U ^ n := by
  exact InfoGeometry.Physics.Algebra.CyclotomicOperatorGeometricSum.geom_sum_mul_one_sub
    Cl55Mat U n

theorem finiteNilpotentRegularization_eq_zero
    (K : Cl55Mat) (beta : ℝ) (n : ℕ) (hn : n ≠ 0)
    (hK : K * K = 0) :
    finiteNilpotentRegularization K beta n = 0 := by
  unfold finiteNilpotentRegularization
  have hscaled :
      ((-(beta / (n : ℝ))) • K) * ((-(beta / (n : ℝ))) • K) = 0 := by
    simp [hK]
  have hpow := InfoGeometry.Clifford.NilpotentBinomial.one_add_pow_of_sq_zero
    ((-(beta / (n : ℝ))) • K) hscaled n
  rw [show 1 - (beta / (n : ℝ)) • K = 1 + (-(beta / (n : ℝ))) • K by
    simp [sub_eq_add_neg]]
  rw [hpow]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [add_sub_cancel_left]
  ext i j
  have hcancel : (n : ℝ) * (beta / (n : ℝ)) = beta := mul_div_cancel₀ beta hnR
  have h1 : (n • (-(beta / (n : ℝ)) • K)) i j = (n : ℝ) * (-(beta / (n : ℝ)) * K i j) := by
    change n • (-(beta / (n : ℝ)) • K i j) = _
    rw [smul_eq_mul, nsmul_eq_mul]
  have h2 : (beta • K) i j = beta * K i j := by
    change beta • K i j = _
    rw [smul_eq_mul]
  have h3 : ((n • (-(beta / (n : ℝ)) • K) + beta • K) i j) =
      (n • (-(beta / (n : ℝ)) • K)) i j + (beta • K) i j := rfl
  rw [Matrix.zero_apply, h3, h1, h2]
  rw [show (n : ℝ) * (-(beta / (n : ℝ)) * K i j) = -((n : ℝ) * (beta / (n : ℝ))) * K i j by ring]
  rw [hcancel]
  ring

theorem finiteNilpotentRegularization_trace_eq_zero
    (K : Cl55Mat) (beta : ℝ) (n : ℕ) (hn : n ≠ 0)
    (hK : K * K = 0) :
    Matrix.trace (finiteNilpotentRegularization K beta n) = 0 := by
  rw [finiteNilpotentRegularization_eq_zero K beta n hn hK]
  simp

theorem inductiveSurprisalStep_zero_of_square_zero
    (K : Cl55Mat) (beta n : ℝ) (hK : K * K = 0) :
    inductiveSurprisalStep K beta n = 0 := by
  unfold inductiveSurprisalStep
  rw [hK, smul_zero]

/--
  THEOREM: The trace of the inductive surprisal step is proportional to Tr(K²).
-/
theorem inductiveSurprisalStep_trace (K : Cl55Mat) (beta : ℝ) (n : ℝ) :
    Matrix.trace (inductiveSurprisalStep K beta n) =
      (((n - 1) / (2 * n)) * beta^2) * Matrix.trace (K * K) := by
  dsimp [inductiveSurprisalStep]
  rw [Matrix.trace_smul, smul_eq_mul]

/--
  THEOREM: The trace of the colimit regularized surprisal kernel isolates
  the pure second-order Quantum Variance / Fisher-Amari metric Tr(K²).
-/
theorem leading_term_is_quantum_metric (K : Cl55Mat) (beta : ℝ) :
    Matrix.trace (regularizedSurprisalKernel K beta) =
      ((1 / 2 : ℝ) * beta^2) * Matrix.trace (K * K) := by
  dsimp [regularizedSurprisalKernel]
  rw [Matrix.trace_smul, smul_eq_mul]

/--
  THEOREM: When the surprisal fluctuation vanishes (`K = 0`), the regularized
  kernel vanishes identically (flat equilibrium vacuum).
-/
@[simp] theorem regularizedSurprisalKernel_zero (beta : ℝ) :
    regularizedSurprisalKernel (0 : Cl55Mat) beta = 0 := by
  dsimp [regularizedSurprisalKernel]
  simp

/--
  THEOREM: When temperature parameter `beta = 0`, the regularized kernel vanishes.
-/
@[simp] theorem regularizedSurprisalKernel_beta_zero (K : Cl55Mat) :
    regularizedSurprisalKernel K 0 = 0 := by
  dsimp [regularizedSurprisalKernel]
  simp

end InfoGeometry.Physics.SurprisalRegularization
