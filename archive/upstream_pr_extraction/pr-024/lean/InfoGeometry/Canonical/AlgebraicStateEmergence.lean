import InfoGeometry.Canonical.AlgebraicStateLorentzAction
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.AlgebraicStateEmergence

open InfoGeometry.Canonical.AlgebraicStateFunctionalBridge
open InfoGeometry.Canonical.Cl11LorentzAction
open InfoGeometry.Canonical.AlgebraicStateLorentzAction
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Quantum
open InfoGeometry.Krein

section EmergentGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => DoubledSpace H →L[ℝ] DoubledSpace H

/--
Emergent symmetric Fisher-like metric on the algebraic state space.

Defined as the product of the state evaluations on the dual Bogoliubov channels
`uPlus` and `uMinus`. This is the fundamental Casimir-invariant operator geometry.
-/
@[rep_depth transport]
noncomputable def emergentMetric
    (X : RealSplitCl11Action (DoubledSpace H))
    (ω : PositiveNormalizedFunctional H) (A : EndH) : ℝ :=
  ω.probe (uPlus X A) * ω.probe (uMinus X A)

/--
Lorentz Invariance of the Emergent Metric.

Because the modular adjoint flow scales the `uPlus` channel by `exp(-2t)`
and the `uMinus` channel by `exp(2t)`, their product is strictly conserved.
This provides the emergent invariant Lorentz geometry over the operator algebra.
-/
@[rep_depth transport]
theorem emergentMetric_invariant
    (X : RealSplitCl11Action (DoubledSpace H)) (t : ℝ)
    (ω : PositiveNormalizedFunctional H) (A : EndH) :
    emergentMetric X (modularAdjointStateFlow X t ω) A = emergentMetric X ω A := by
  unfold emergentMetric
  rw [modularAdjointStateFlow_uPlus X t ω A]
  rw [modularAdjointStateFlow_uMinus X t ω A]
  calc
    (Real.exp (-2 * t) * ω.probe (uPlus X A)) * (Real.exp (2 * t) * ω.probe (uMinus X A))
      = (Real.exp (-2 * t) * Real.exp (2 * t)) * (ω.probe (uPlus X A) * ω.probe (uMinus X A)) := by ring
    _ = Real.exp ((-2 * t) + (2 * t)) * (ω.probe (uPlus X A) * ω.probe (uMinus X A)) := by rw [← Real.exp_add]
    _ = Real.exp 0 * (ω.probe (uPlus X A) * ω.probe (uMinus X A)) := by
          have h_zero : (-2 * t) + (2 * t) = 0 := by ring
          rw [h_zero]
    _ = 1 * (ω.probe (uPlus X A) * ω.probe (uMinus X A)) := by simp
    _ = ω.probe (uPlus X A) * ω.probe (uMinus X A) := by ring

/--
Emergent Connection Ratio (Covariant derivative readout).

Defined as the ratio of the state evaluations on the dual Bogoliubov channels.
It measures the "tilt" or gradient of the state with respect to the phase-space shift.
-/
@[rep_depth transport]
noncomputable def emergentCovariantRatio
    (X : RealSplitCl11Action (DoubledSpace H))
    (ω : PositiveNormalizedFunctional H) (A : EndH) : ℝ :=
  ω.probe (uPlus X A) / ω.probe (uMinus X A)

/--
Covariance of the Emergent Connection.

The connection ratio transforms linearly by scaling with `exp(-4t)` under the
modular adjoint flow, acting as an exact tensorial readout of the local boost action.
-/
@[rep_depth transport]
theorem emergentCovariantRatio_covariant
    (X : RealSplitCl11Action (DoubledSpace H)) (t : ℝ)
    (ω : PositiveNormalizedFunctional H) (A : EndH) :
    emergentCovariantRatio X (modularAdjointStateFlow X t ω) A =
      Real.exp (-4 * t) * emergentCovariantRatio X ω A := by
  unfold emergentCovariantRatio
  rw [modularAdjointStateFlow_uPlus X t ω A]
  rw [modularAdjointStateFlow_uMinus X t ω A]
  calc
    (Real.exp (-2 * t) * ω.probe (uPlus X A)) / (Real.exp (2 * t) * ω.probe (uMinus X A))
      = (Real.exp (-2 * t) / Real.exp (2 * t)) * (ω.probe (uPlus X A) / ω.probe (uMinus X A)) := by ring
    _ = Real.exp (-2 * t - 2 * t) * (ω.probe (uPlus X A) / ω.probe (uMinus X A)) := by rw [Real.exp_sub]
    _ = Real.exp (-4 * t) * (ω.probe (uPlus X A) / ω.probe (uMinus X A)) := by
          have h : -2 * t - 2 * t = -4 * t := by ring
          rw [h]

end EmergentGeometry

end InfoGeometry.Canonical.AlgebraicStateEmergence
