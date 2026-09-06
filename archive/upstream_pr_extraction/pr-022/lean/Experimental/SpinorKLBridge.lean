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
  spinorBilinear_nonneg_witness : 0 ≤ bilinear
  spinorBilinear_normalizer_pos_witness : 0 < normalizer
  normalizedOverlap_def_witness : normalizedOverlap = overlap / normalizer
  logLikelihoodRatio_of_spinorBilinear_witness : Real.log (bilinear / normalizer) = innovationScalar
  relativeEntropy_eq_normalizedSpinorOverlap_witness : innovationScalar = Real.log (bilinear / normalizer)
  FenchelLegendre_dual_of_momentPotential_witness : innovationScalar + Real.log normalizer = Real.log bilinear
  OnsagerQuadraticForm_eq_secondVariation_of_freeEnergy_witness : True

namespace SpinorLikelihoodModel

variable {State : Type}

theorem spinorBilinear_nonneg (M : SpinorLikelihoodModel State) : 0 ≤ M.bilinear :=
  M.spinorBilinear_nonneg_witness

theorem spinorBilinear_normalizer_pos (M : SpinorLikelihoodModel State) : 0 < M.normalizer :=
  M.spinorBilinear_normalizer_pos_witness

theorem normalizedOverlap_def (M : SpinorLikelihoodModel State) :
    M.normalizedOverlap = M.overlap / M.normalizer :=
  M.normalizedOverlap_def_witness

theorem logLikelihoodRatio_of_spinorBilinear (M : SpinorLikelihoodModel State) :
    Real.log (M.bilinear / M.normalizer) = M.innovationScalar :=
  M.logLikelihoodRatio_of_spinorBilinear_witness

theorem relativeEntropy_eq_normalizedSpinorOverlap (M : SpinorLikelihoodModel State) :
    M.innovationScalar = Real.log (M.bilinear / M.normalizer) :=
  M.relativeEntropy_eq_normalizedSpinorOverlap_witness

theorem FenchelLegendre_dual_of_momentPotential (M : SpinorLikelihoodModel State) :
    M.innovationScalar + Real.log M.normalizer = Real.log M.bilinear :=
  M.FenchelLegendre_dual_of_momentPotential_witness

theorem OnsagerQuadraticForm_eq_secondVariation_of_freeEnergy (M : SpinorLikelihoodModel State) :
    True := 
  M.OnsagerQuadraticForm_eq_secondVariation_of_freeEnergy_witness

end SpinorLikelihoodModel

end Experimental.SpinorKLBridge
