import InfoGeometry.Research.ConformalUnification
import InfoGeometry.Research.SpectralInference
import Mathlib.LinearAlgebra.Matrix.Trace

namespace InfoGeometry.Research.ChiralAction

open InfoGeometry.Research.ConformalUnification
open InfoGeometry.Research.SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Chiral Dirac Operator.
Here, the Geometric Chiral Anomaly χ = [P_D, P_MP] acts as a Gauge Field
that couples to the standard Information Dirac Operator D.
D_χ = D + g * χ, where g is a coupling constant.
-/
noncomputable def chiralDirac (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g : ℝ) : E →L[ℝ] E :=
  IST.D + g • CI.chiralAnomaly

/--
The Chiral Information Action.
S_chiral = Tr(D_χ² / Λ²).
This action incorporates both the standard Fisher Metric diffusion and the 
topological tension induced by the metric-spectral incompatibility.
-/
noncomputable def chiralInformationAction (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g Λ : ℝ) : ℝ :=
  let D_chi := chiralDirac IST CI g
  -- The trace of the squared chiral Dirac operator normalized by the scale Λ
  (LinearMap.trace ℝ E (D_chi * D_chi).toLinearMap) / (Λ ^ 2)

omit [FiniteDimensional ℝ E] in
/--
Theorem: If the inference system is normal (ε = 0), the Chiral Information Action
reduces to the standard Spectral Action.
-/
theorem chiral_action_reduces_for_normal (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g _Λ : ℝ)
    (h_normal : CI.IsNormalInference) :
    chiralDirac IST CI g = IST.D := by
  have he : CI.epsilon = 0 := h_normal
  have hnreal : (nnnorm CI.chiralAnomaly : ℝ) = 0 := by
    simpa [ConformalInference.epsilon] using he
  have hc : CI.chiralAnomaly = 0 := by
    have hn : nnnorm CI.chiralAnomaly = 0 := by
      exact_mod_cast hnreal
    exact (nnnorm_eq_zero).mp hn
  unfold chiralDirac
  rw [hc, smul_zero, add_zero]

end InfoGeometry.Research.ChiralAction
