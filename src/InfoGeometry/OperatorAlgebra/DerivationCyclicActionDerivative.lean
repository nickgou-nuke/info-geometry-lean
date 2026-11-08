/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationCyclicAction
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The real first variation of the noncommutative cyclic curvature action

The coefficient algebra needs no topology: on every affine one-form line,
the traced action is exactly a real polynomial. Its derivative is established
using native `HasDerivAt`. This does not assert integration by parts or a
manifold Yang--Mills equation.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable (K : DerivationLieLane ℝ A)
variable {ι : Type*} [Fintype ι]

/-- The actual derivative of the trace action along an arbitrary operator
one-form perturbation. -/
theorem curvatureTraceAction_hasDerivAt
    (τ : A →ₗ[ℝ] ℝ) (frame : ι → K.L)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a)) (Γ α : OneForm K) :
    HasDerivAt (fun t : ℝ => curvatureTraceAction K τ frame (Γ + t • α))
      (2 * curvatureTracePairing K τ frame
        (connectionCurvature K Γ) (covariantExteriorDerivativeOne K Γ α)) 0 := by
  let B := curvatureTracePairing K τ frame
  let F := connectionCurvature K Γ
  let G := covariantExteriorDerivativeOne K Γ α
  let Q := connectionWedgeSquare K α
  have hlinear : HasDerivAt (fun t : ℝ => 2 * t * B F G) (2 * B F G) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul 2).mul_const (B F G)
  have htwo : HasDerivAt
      (fun t : ℝ => t ^ 2 * (B G G + 2 * B F Q)) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const (B G G + 2 * B F Q)
  have hthree : HasDerivAt (fun t : ℝ => 2 * t ^ 3 * B G Q) 0 0 := by
    simpa using ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 2).mul_const (B G Q)
  have hfour : HasDerivAt (fun t : ℝ => t ^ 4 * B Q Q) 0 0 := by
    simpa using (hasDerivAt_pow 4 (0 : ℝ)).mul_const (B Q Q)
  have hpoly : HasDerivAt
      (fun t : ℝ => curvatureTraceAction K τ frame Γ + 2 * t * B F G +
        t ^ 2 * (B G G + 2 * B F Q) + 2 * t ^ 3 * B G Q + t ^ 4 * B Q Q)
      (2 * B F G) 0 := by
    simpa only [Pi.add_def, zero_add, add_zero] using
      ((((hasDerivAt_const (0 : ℝ) (curvatureTraceAction K τ frame Γ)).add hlinear).add
        htwo).add hthree).add hfour
  apply hpoly.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    curvatureTraceAction_add_smul K τ frame hcyclic Γ α t

/-- The derivative expressed through Mathlib's `deriv` operation. -/
theorem curvatureTraceAction_deriv
    (τ : A →ₗ[ℝ] ℝ) (frame : ι → K.L)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a)) (Γ α : OneForm K) :
    deriv (fun t : ℝ => curvatureTraceAction K τ frame (Γ + t • α)) 0 =
      2 * curvatureTracePairing K τ frame
        (connectionCurvature K Γ) (covariantExteriorDerivativeOne K Γ α) :=
  (curvatureTraceAction_hasDerivAt K τ frame hcyclic Γ α).deriv

/-- The variational condition is orthogonality of curvature to every
linearized curvature, for the native trace pairing. -/
theorem curvatureTraceAction_stationary_iff
    (τ : A →ₗ[ℝ] ℝ) (frame : ι → K.L)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a)) (Γ : OneForm K) :
    (∀ α : OneForm K,
      deriv (fun t : ℝ => curvatureTraceAction K τ frame (Γ + t • α)) 0 = 0) ↔
    ∀ α : OneForm K, curvatureTracePairing K τ frame
      (connectionCurvature K Γ) (covariantExteriorDerivativeOne K Γ α) = 0 := by
  simp only [curvatureTraceAction_deriv K τ frame hcyclic, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or]

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
