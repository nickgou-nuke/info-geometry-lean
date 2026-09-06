import InfoGeometry.Clifford.SplitQuaternionNilpotentFlow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Split-quaternion elliptic, hyperbolic, and parabolic coordinate curves

This file records finite coordinate facts for three standard one-parameter
curves in the existing split-quaternion model:

* `ellipticFlow θ = cos θ + sin θ i`;
* `hyperbolicFlow η = cosh η + sinh η j`;
* `parabolicFlow T = 1 + T (i - j)`.

Each has split-quaternion quadratic norm one.  The parabolic curve is connected
back to `SplitQuaternionNilpotentFlow.sq_nilpotent_exp`.

The file does not classify all one-parameter subgroups of `SL(2,ℝ)`, does not
prove conformal action on any causal cone, and does not assert a global analytic
or Clifford-completion theorem.
-/

namespace InfoGeometry.Clifford.SplitQuaternionFlowCoordinates

/-- Elliptic unit-coordinate curve in the `1,i` split-quaternion plane. -/
noncomputable def ellipticFlow (θ : ℝ) : SplitQuaternion :=
  ⟨Real.cos θ, Real.sin θ, 0, 0⟩

/-- Hyperbolic unit-coordinate curve in the `1,j` split-quaternion plane. -/
noncomputable def hyperbolicFlow (η : ℝ) : SplitQuaternion :=
  ⟨Real.cosh η, 0, Real.sinh η, 0⟩

/-- Parabolic nilpotent coordinate curve `1 + T (i - j)`. -/
def parabolicFlow (T : ℝ) : SplitQuaternion :=
  ⟨1, T, -T, 0⟩

/-- The parabolic coordinate curve is the nilpotent truncation from `SplitQuaternionNilpotentFlow`. -/
theorem parabolicFlow_eq_nilpotent_exp (T : ℝ) :
    parabolicFlow T = _root_.InfoGeometry.Clifford.SplitQuaternionNilpotentFlow.sq_nilpotent_exp T := by
  rw [_root_.InfoGeometry.Clifford.SplitQuaternionNilpotentFlow.sq_nilpotent_exp_eq]
  rfl

/-- Elliptic coordinate curve has split-quaternion norm one. -/
theorem norm_ellipticFlow (θ : ℝ) :
    norm (ellipticFlow θ) = 1 := by
  unfold norm ellipticFlow
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    calc Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ
      _ = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by ring
      _ = 1 := Real.cos_sq_add_sin_sq θ
  linarith

/-- Hyperbolic coordinate curve has split-quaternion norm one. -/
theorem norm_hyperbolicFlow (η : ℝ) :
    norm (hyperbolicFlow η) = 1 := by
  unfold norm hyperbolicFlow
  have h : Real.cosh η * Real.cosh η - Real.sinh η * Real.sinh η = 1 := by
    calc Real.cosh η * Real.cosh η - Real.sinh η * Real.sinh η
      _ = Real.cosh η ^ 2 - Real.sinh η ^ 2 := by ring
      _ = 1 := Real.cosh_sq_sub_sinh_sq η
  linarith

/-- Parabolic nilpotent coordinate curve has split-quaternion norm one. -/
theorem norm_parabolicFlow (T : ℝ) :
    norm (parabolicFlow T) = 1 := by
  unfold norm parabolicFlow
  ring

/-- The concrete nilpotent truncation has split-quaternion norm one. -/
theorem norm_nilpotent_exp (T : ℝ) :
    norm (_root_.InfoGeometry.Clifford.SplitQuaternionNilpotentFlow.sq_nilpotent_exp T) = 1 := by
  rw [← parabolicFlow_eq_nilpotent_exp]
  exact norm_parabolicFlow T

/--
The three coordinate norm computations above are not a proof of an exhaustive
subgroup classification or a global causal/conformal theorem.
-/
/-
The three coordinate curves are proven norm-one flows.  Their exhaustive
classification is intentionally not asserted here: it requires a separate
Lie-group owner and is not implied by the coordinate identities above.
-/
theorem split_quaternion_coordinate_flows_are_norm_one :
    (∀ θ : ℝ, norm (ellipticFlow θ) = 1) ∧
    (∀ η : ℝ, norm (hyperbolicFlow η) = 1) ∧
    (∀ T : ℝ, norm (parabolicFlow T) = 1) := by
  exact ⟨norm_ellipticFlow, norm_hyperbolicFlow, norm_parabolicFlow⟩

end InfoGeometry.Clifford.SplitQuaternionFlowCoordinates
