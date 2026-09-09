import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace Experimental.SpinorKLBridge

open InfoGeometry.Canonical.SouriauOperatorialLogPotential

/--
**Spinor Likelihood Model**:
The identification mapping between the microscopic spinor bilinear
and the macroscopic information-geometric quantities.
-/
structure SpinorLikelihoodModel (State : Type) where
  state : Type
  bilinear : ℝ
  normalizer : ℝ
  overlap : ℝ
  normalizedOverlap : ℝ
  innovationScalar : ℝ
  spinorBilinear_nonneg_hyp : 0 ≤ bilinear
  spinorBilinear_normalizer_pos_hyp : 0 < normalizer
  normalizedOverlap_def_hyp : normalizedOverlap = overlap / normalizer
  logLikelihoodRatio_of_spinorBilinear_hyp : Real.log (bilinear / normalizer) = innovationScalar
  FenchelLegendre_dual_of_momentPotential_hyp : innovationScalar + Real.log normalizer = Real.log bilinear

namespace SpinorLikelihoodModel

variable {State : Type}

theorem spinorBilinear_nonneg (M : SpinorLikelihoodModel State) : 0 ≤ M.bilinear :=
  M.spinorBilinear_nonneg_hyp

theorem spinorBilinear_normalizer_pos (M : SpinorLikelihoodModel State) : 0 < M.normalizer :=
  M.spinorBilinear_normalizer_pos_hyp

theorem normalizedOverlap_def (M : SpinorLikelihoodModel State) :
    M.normalizedOverlap = M.overlap / M.normalizer :=
  M.normalizedOverlap_def_hyp

theorem logLikelihoodRatio_of_spinorBilinear (M : SpinorLikelihoodModel State) :
    Real.log (M.bilinear / M.normalizer) = M.innovationScalar :=
  M.logLikelihoodRatio_of_spinorBilinear_hyp

theorem relativeEntropy_eq_normalizedSpinorOverlap (M : SpinorLikelihoodModel State) :
    M.innovationScalar = Real.log (M.bilinear / M.normalizer) :=
  M.logLikelihoodRatio_of_spinorBilinear_hyp.symm

theorem FenchelLegendre_dual_of_momentPotential (M : SpinorLikelihoodModel State) :
    M.innovationScalar + Real.log M.normalizer = Real.log M.bilinear :=
  M.FenchelLegendre_dual_of_momentPotential_hyp

theorem OnsagerQuadraticForm_eq_secondVariation_of_freeEnergy (M : SpinorLikelihoodModel State) :
    Real.log (M.bilinear / M.normalizer) + Real.log M.normalizer = Real.log M.bilinear := by
  rw [M.logLikelihoodRatio_of_spinorBilinear_hyp]
  exact M.FenchelLegendre_dual_of_momentPotential_hyp

end SpinorLikelihoodModel

end Experimental.SpinorKLBridge
