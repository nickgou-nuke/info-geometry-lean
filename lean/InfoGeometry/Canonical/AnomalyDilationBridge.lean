import InfoGeometry.Canonical.ConformalUnification
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.NoncommRing
set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.AnomalyDilationBridge

Operator-level bridge between the projector-anomaly layer and the conformal
dilation layer.

This file stays at the level currently justified by the codebase:
- the Jacobi expansion for `[D, χ]`
- the finite-dimensional trace vanishing of the dilation commutator
- the resulting no-go theorem for a nontrivial finite-dimensional trace anomaly
-/

namespace InfoGeometry.Canonical.AnomalyDilationBridge

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.MoorePenrose

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

namespace ConformalInference

variable (CI : ConformalInference E)

section DynamicalCommutator

/--
Jacobi expansion of the dilation-action on the chiral anomaly operator.

This expresses `[D, χ]` purely in terms of the independent dilation commutators
with the spectral and metric projectors.
-/
theorem dilation_anomaly_jacobi_expansion :
    CI.D * CI.chiralAnomalyOperator - CI.chiralAnomalyOperator * CI.D =
      (CI.D * CI.P_D - CI.P_D * CI.D) * CI.P_MP
      + CI.P_D * (CI.D * CI.P_MP - CI.P_MP * CI.D)
      - (CI.D * CI.P_MP - CI.P_MP * CI.D) * CI.P_D
      - CI.P_MP * (CI.D * CI.P_D - CI.P_D * CI.D) := by
  simp [ConformalInference.chiralAnomalyOperator, ConformalInference.chiralAnomaly]
  noncomm_ring

end DynamicalCommutator

section TraceAnomaly

/--
In finite dimensions, the trace of the dilation generator vanishes exactly.

This is the trace-zero property of a commutator: `D = (1/2) [P, K]`.
-/
theorem trace_dilation_eq_zero :
    LinearMap.trace ℝ E CI.D.toLinearMap = 0 := by
  have hProjectorTrace :
      LinearMap.trace ℝ E
          ((IsMoorePenroseInverse.rightProjector CI.A CI.A_MP : E →L[ℝ] E).toLinearMap) =
        LinearMap.trace ℝ E
          ((IsMoorePenroseInverse.leftProjector CI.A CI.A_MP : E →L[ℝ] E).toLinearMap) := by
    simpa [IsMoorePenroseInverse.rightProjector, IsMoorePenroseInverse.leftProjector] using
      LinearMap.trace_mul_comm (R := ℝ) (M := E) CI.A.toLinearMap CI.A_MP.toLinearMap
  rw [CI.dilation_eq_half_sub_mp_projectors]
  simp [sub_eq_add_neg]
  rw [hProjectorTrace]
  simp

/--
Finite-dimensional trace-anomaly no-go theorem.

If a trace-anomaly equation of the form
`trace D = ε * trace P_D`
holds with nonzero spectral trace, then the anomaly scale must vanish.
-/
theorem normal_phase_of_trace_anomaly_in_finite_dim
    (hTraceAnomaly :
      LinearMap.trace ℝ E CI.D.toLinearMap =
        CI.chiralScale * LinearMap.trace ℝ E CI.P_D.toLinearMap)
    (hRankPos : LinearMap.trace ℝ E CI.P_D.toLinearMap ≠ 0) :
    CI.IsNormalInference := by
  have hScaleMul : CI.chiralScale * LinearMap.trace ℝ E CI.P_D.toLinearMap = 0 := by
    calc
      CI.chiralScale * LinearMap.trace ℝ E CI.P_D.toLinearMap
          = LinearMap.trace ℝ E CI.D.toLinearMap := hTraceAnomaly.symm
      _ = 0 := trace_dilation_eq_zero (CI := CI)
  exact (mul_eq_zero.mp hScaleMul).resolve_right hRankPos

end TraceAnomaly

end ConformalInference

end InfoGeometry.Canonical.AnomalyDilationBridge
