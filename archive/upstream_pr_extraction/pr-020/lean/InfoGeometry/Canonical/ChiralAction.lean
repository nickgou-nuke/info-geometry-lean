import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.SpectralInference
import Mathlib.LinearAlgebra.Determinant

namespace InfoGeometry.Canonical.ChiralAction

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.SpectralInference

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
S_chiral = log |det(D_χ² / Λ²)|.
This action incorporates both the standard Fisher Metric diffusion and the 
topological tension induced by the metric-spectral incompatibility.
-/
noncomputable def chiralInformationAction (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g Λ : ℝ) : ℝ :=
  let D_chi := chiralDirac IST CI g
  -- Log-absolute Jacobian determinant of the squared chiral Dirac operator.
  (Real.log (|LinearMap.det (D_chi * D_chi).toLinearMap|)) / (Λ ^ 2)

omit [FiniteDimensional ℝ E] in
/--
Theorem: If the inference system is normal (ε = 0), the Chiral Information Action
reduces to the standard Spectral Action.
-/
theorem chiral_action_reduces_for_normal (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g _Λ : ℝ)
    (h_normal : CI.IsNormalInference) :
    chiralDirac IST CI g = IST.D := by
  have hActionZero : CI.unitOfAction = 0 :=
    CI.unitOfAction_eq_zero_of_normalInference h_normal
  have hNormZero : ‖CI.actionStructureConstantOp‖ = 0 := by
    simpa [ConformalInference.unitOfAction] using hActionZero
  have hActionOpZero : CI.actionStructureConstantOp = 0 :=
    norm_eq_zero.mp hNormZero
  have hc : CI.chiralAnomaly = 0 := by
    have hAnomZero : CI.chiralAnomalyOperator = 0 := by
      simpa [CI.actionStructureConstantOp_eq_chiralAnomalyOperator] using hActionOpZero
    simpa [ConformalInference.chiralAnomalyOperator] using hAnomZero
  unfold chiralDirac
  rw [hc, smul_zero, add_zero]


omit [FiniteDimensional ℝ E] in
/--
Under unit relative volume, the chiral Dirac perturbation collapses to the
base Dirac operator.
-/
theorem chiralDirac_eq_of_unitRelativeVolume
    {n : Nat}
    (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g : ℝ)
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (hUnitVolume : InfoGeometry.Canonical.MoE.relativeVolumeChangeRN n M = 1) :
    chiralDirac IST CI g = IST.D := by
  have hNormal : CI.IsNormalInference := by
    exact CI.isNormalInference_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  exact chiral_action_reduces_for_normal IST CI g 0 hNormal

end InfoGeometry.Canonical.ChiralAction
