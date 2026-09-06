import InfoGeometry.Canonical.RealUHFProjectionRankSystem
import InfoGeometry.Canonical.RealUHFFiniteMatrixNormedCarrier
import InfoGeometry.Clifford.Cl11MarkovJonesEngine

/-!
# Continuous finite-stage dimension readouts

The normalized trace at each finite matrix stage is packaged as a continuous
linear map.  The successor embedding preserves this readout, giving the
topological naturality square for the finite binary tower.
-/

namespace InfoGeometry.Canonical.RealUHFProjectionRankSystemTopological

open InfoGeometry.Canonical.RealUHFProjectionRankSystem
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine

noncomputable section

def finiteStageNormalizedTraceCLM (n : ℕ) : MatStage n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (normalizedTraceLinear n)

@[simp] theorem finiteStageNormalizedTraceCLM_apply
    (n : ℕ) (A : MatStage n) :
    finiteStageNormalizedTraceCLM n A = normalizedTrace n A := by
  change normalizedTraceLinear n A = normalizedTrace n A
  rfl

def stageEmbedCLM (n : ℕ) : MatStage n →L[ℝ] MatStage (n + 1) :=
  LinearMap.toContinuousLinearMap (stageEmbed n).toLinearMap

@[simp] theorem stageEmbedCLM_apply (n : ℕ) (A : MatStage n) :
    stageEmbedCLM n A = stageEmbed n A := by
  rfl

theorem finiteStageNormalizedTraceCLM_natural (n : ℕ) :
    (finiteStageNormalizedTraceCLM (n + 1)).comp (stageEmbedCLM n) =
      finiteStageNormalizedTraceCLM n := by
  ext A
  change normalizedTraceLinear (n + 1) (stageEmbed n A) =
    normalizedTraceLinear n A
  exact cl11_normalizedTrace_one_step n A

theorem finiteStageNormalizedTraceCLM_continuous (n : ℕ) :
    Continuous (finiteStageNormalizedTraceCLM n) :=
  (finiteStageNormalizedTraceCLM n).continuous

end
end InfoGeometry.Canonical.RealUHFProjectionRankSystemTopological
