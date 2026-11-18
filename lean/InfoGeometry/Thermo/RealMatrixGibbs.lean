/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelContinuityReduction
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFrechetBridge
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Gibbs calculus on the full real matrix algebra

The partition is the trace of the matrix exponential. Its normalization is a
faithful density for every self-adjoint exponent in nonzero finite dimension.
Entropy uses the actual real continuous-functional-calculus logarithm.

The first-variation proof reuses the existing Banach-algebra Duhamel theorem.
The inserted tangent matrix is arbitrary; only cyclicity of the trace removes
the ordered insertion integral. No common eigenbasis or commutation hypothesis
is imposed on the exponent and its variation.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealMatrixGibbs

open MeasureTheory
open InfoGeometry.OperatorAlgebra
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Interval

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℝ

local instance : NormedAlgebra ℚ Mat := NormedAlgebra.restrictScalars ℚ ℝ Mat

/-- The ordinary matrix trace as a real continuous linear map. -/
def traceCLM : Mat →L[ℝ] ℝ :=
  ⟨Matrix.traceLinearMap n ℝ ℝ,
    (Matrix.traceLinearMap n ℝ ℝ).continuous_of_finiteDimensional⟩

omit [DecidableEq n] in
@[simp] theorem traceCLM_apply (A : Mat) : traceCLM A = Matrix.trace A := rfl

/-- The statistical partition, as distinct from a determinant volume. -/
def partition (K : Mat) : ℝ := Matrix.trace (NormedSpace.exp K)

/-- Trace-normalized exponential on the full real matrix carrier. -/
def density (K : Mat) : Mat := (partition K)⁻¹ • NormedSpace.exp K

def massieu (K : Mat) : ℝ := Real.log (partition K)

def expectation (K A : Mat) : ℝ := Matrix.trace (density K * A)

/-- Density-weighted entropy with the native operator logarithm. -/
def entropy (K : Mat) : ℝ :=
  -Matrix.trace (density K * CFC.log (density K))

theorem exp_strictlyPositive (K : Mat) (hK : IsSelfAdjoint K) :
    IsStrictlyPositive (NormedSpace.exp K) :=
  ⟨hK.exp_nonneg, NormedSpace.isUnit_exp K⟩

theorem partition_pos [Nonempty n] (K : Mat) (hK : IsSelfAdjoint K) :
    0 < partition K :=
  (Matrix.isStrictlyPositive_iff_posDef.mp (exp_strictlyPositive K hK)).trace_pos

theorem density_strictlyPositive [Nonempty n]
    (K : Mat) (hK : IsSelfAdjoint K) : IsStrictlyPositive (density K) :=
  IsStrictlyPositive.smul (inv_pos.mpr (partition_pos K hK))
    (exp_strictlyPositive K hK)

theorem trace_density (K : Mat) (hZ : partition K ≠ 0) :
    Matrix.trace (density K) = 1 := by
  rw [density, Matrix.trace_smul]
  exact inv_mul_cancel₀ hZ

theorem log_density [Nonempty n] (K : Mat) (hK : IsSelfAdjoint K) :
    CFC.log (density K) = K - massieu K • (1 : Mat) := by
  rw [density, CFC.log_smul' (NormedSpace.exp K)
    (inv_pos.mpr (partition_pos K hK)) (exp_strictlyPositive K hK),
    Real.log_inv, map_neg, Algebra.algebraMap_eq_smul_one, CFC.log_exp K hK]
  simp only [massieu]
  abel

/-- The Massieu identity follows from the actual logarithm and trace one. -/
theorem entropy_eq_massieu_sub_expectation [Nonempty n]
    (K : Mat) (hK : IsSelfAdjoint K) :
    entropy K = massieu K - expectation K K := by
  rw [entropy, log_density K hK, mul_sub, Matrix.trace_sub,
    Matrix.mul_smul, mul_one, Matrix.trace_smul,
    trace_density K (partition_pos K hK).ne']
  simp only [smul_eq_mul, mul_one, expectation]
  abel

/-- Cyclicity collapses the ordered insertion, without commuting `K` and `A`. -/
theorem trace_duhamelIntegrand (K A : Mat) (s : ℝ) :
    Matrix.trace (NormedSpace.exp ((1 - s) • K) * A *
      NormedSpace.exp (s • K)) = Matrix.trace (NormedSpace.exp K * A) := by
  have hcomm : Commute (s • K) ((1 - s) • K) :=
    ((Commute.refl K).smul_left s).smul_right (1 - s)
  have hsum : s • K + (1 - s) • K = K := by
    rw [sub_smul, one_smul]
    abel
  rw [Matrix.trace_mul_cycle, ← NormedSpace.exp_add_of_commute hcomm, hsum]

theorem trace_exponentialDerivative (K A : Mat) :
    Matrix.trace (exponentialDerivative (𝕜 := ℝ) K A) =
      Matrix.trace (NormedSpace.exp K * A) := by
  have hcont : ContinuousAt (duhamelPerturbationIntegral K A) 0 :=
    (continuous_duhamelDifferenceQuotient K A).continuousAt
  rw [exponentialDerivative_apply_eq_duhamelDerivative_of_continuousAt K A hcont,
    duhamelDerivative_apply_integral]
  have hi : IntervalIntegrable
      (fun s : ℝ => NormedSpace.exp ((1 - s) • K) * A *
        NormedSpace.exp (s • K)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  change traceCLM (∫ s in (0 : ℝ)..1,
      NormedSpace.exp ((1 - s) • K) * A * NormedSpace.exp (s • K)) = _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm traceCLM hi]
  simp only [traceCLM_apply, trace_duhamelIntegrand]
  simp

/-- The real Fréchet derivative of the trace partition. -/
def partitionDifferential (K : Mat) : Mat →L[ℝ] ℝ :=
  traceCLM.comp (exponentialDerivative (𝕜 := ℝ) K)

theorem hasFDerivAt_partition (K : Mat) :
    HasFDerivAt partition (partitionDifferential K) K :=
  traceCLM.hasFDerivAt.comp K (hasFDerivAt_exp_noncommutative (𝕜 := ℝ) K)

theorem partitionDifferential_apply (K A : Mat) :
    partitionDifferential K A = Matrix.trace (NormedSpace.exp K * A) :=
  trace_exponentialDerivative K A

theorem expectation_eq_partitionDifferential_div (K A : Mat) :
    expectation K A = partitionDifferential K A / partition K := by
  rw [partitionDifferential_apply, expectation, density,
    smul_mul_assoc, Matrix.trace_smul]
  simp [div_eq_mul_inv, mul_comm]

/-- Differentiability of the normalized full matrix state. -/
theorem differentiableAt_density (K : Mat) (hZ : partition K ≠ 0) :
    DifferentiableAt ℝ density K :=
  ((hasFDerivAt_partition K).differentiableAt.inv hZ).smul
    (hasFDerivAt_exp_noncommutative (𝕜 := ℝ) K).differentiableAt

/-- The log-partition differential is expectation in every matrix direction. -/
theorem hasDerivAt_massieu_curve (K : ℝ → Mat) (A : Mat) (t : ℝ)
    (hK : HasDerivAt K A t) (hZ : partition (K t) ≠ 0) :
    HasDerivAt (fun s => massieu (K s)) (expectation (K t) A) t := by
  rw [expectation_eq_partitionDifferential_div]
  exact ((hasFDerivAt_partition (K t)).comp_hasDerivAt t hK).log hZ

/-- Entropy differentiation along a self-adjoint matrix curve. The specified
`R` is the derivative of the constructed normalized exponential. -/
theorem hasDerivAt_entropy_curve [Nonempty n]
    (K : ℝ → Mat) (A R : Mat) (t : ℝ)
    (hself : ∀ s, IsSelfAdjoint (K s))
    (hK : HasDerivAt K A t)
    (hR : HasDerivAt (fun s => density (K s)) R t) :
    HasDerivAt (fun s => entropy (K s)) (-Matrix.trace (R * K t)) t := by
  have hψ := hasDerivAt_massieu_curve K A t hK (partition_pos (K t) (hself t)).ne'
  have hU : HasDerivAt (fun s => Matrix.trace (density (K s) * K s))
      (Matrix.trace (R * K t) + Matrix.trace (density (K t) * A)) t := by
    simpa only [traceCLM_apply, Matrix.trace_add] using
      (traceCLM.hasFDerivAt.comp_hasDerivAt t (hR.mul hK))
  have hS := hψ.sub hU
  have hrate : expectation (K t) A -
      (Matrix.trace (R * K t) + Matrix.trace (density (K t) * A)) =
        -Matrix.trace (R * K t) := by
    unfold expectation
    abel
  rw [hrate] at hS
  have heq : (fun s => entropy (K s)) =
      fun s => massieu (K s) - Matrix.trace (density (K s) * K s) := by
    funext s
    exact entropy_eq_massieu_sub_expectation (K s) (hself s)
  rw [heq]
  exact hS

/-- Scaling the Hamiltonian and inverse-scaling beta preserves its entire
Gibbs exponent, and hence the full density operator. -/
omit [Fintype n] [DecidableEq n] in
theorem exponent_reciprocal_scale (H : Mat) (β c : ℝ) (hc : c ≠ 0) :
    (-(β / c)) • (c • H) = (-β) • H := by
  rw [smul_smul]
  congr 1
  rw [neg_mul, div_mul_cancel₀ β hc]

theorem density_reciprocal_scale (H : Mat) (β c : ℝ) (hc : c ≠ 0) :
    density ((-(β / c)) • (c • H)) = density ((-β) • H) := by
  rw [exponent_reciprocal_scale H β c hc]

theorem entropy_reciprocal_scale (H : Mat) (β c : ℝ) (hc : c ≠ 0) :
    entropy ((-(β / c)) • (c • H)) = entropy ((-β) • H) := by
  rw [exponent_reciprocal_scale H β c hc]

theorem expectation_reciprocal_scale (H : Mat) (β c : ℝ) (hc : c ≠ 0) :
    expectation ((-(β / c)) • (c • H)) (c • H) =
      c * expectation ((-β) • H) H := by
  rw [exponent_reciprocal_scale H β c hc, expectation,
    Matrix.mul_smul, Matrix.trace_smul]
  rfl

end InfoGeometry.Thermo.RealMatrixGibbs
