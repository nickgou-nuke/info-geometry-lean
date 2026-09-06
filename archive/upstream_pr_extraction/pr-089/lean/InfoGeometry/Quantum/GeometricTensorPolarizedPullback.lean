import InfoGeometry.Quantum.GeometricTensorOperatorLift

/-!
# Bi-frame operator pullback

The three triality carriers are deliberately not identified here.  This owner
proves the generic same-carrier bi-frame identity used by their later bridges.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Quantum.GeometricQuantumTensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

noncomputable def polarizedPullbackMetric
    (Uplus Uminus G : EndH) : EndH :=
  (ContinuousLinearMap.adjoint Uminus).comp (G.comp Uplus)

theorem metricOfOperator_polarizedPullbackMetric_apply
    (Uplus Uminus G : EndH) (u v : H) :
    ⟪polarizedPullbackMetric Uplus Uminus G u, v⟫_ℝ =
      ⟪G (Uplus u), Uminus v⟫_ℝ := by
  change ⟪ContinuousLinearMap.adjoint Uminus (G (Uplus u)), v⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_left]

end InfoGeometry.Quantum.GeometricQuantumTensor
