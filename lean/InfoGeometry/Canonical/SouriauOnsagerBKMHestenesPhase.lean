import InfoGeometry.Canonical.SouriauOnsagerBKMEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit

/-!
# Hestenes phase readout for the finite BKM operators

The finite Kubo--Mori transform and its canonical inverse are complex-linear
maps.  This file records their repository-native Hestenes/Krein readout after
restriction of scalars.  It does not introduce a complex-analytic theorem or
identify the CFC logarithm with an ambient map on non-self-adjoint operators.
-/

noncomputable section

namespace SouriauOnsagerBKM

open InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit
open InfoGeometry.Geometry.BilingualAnalyticity

variable {n : ℕ}

theorem kuboMoriKernel_isHestenesPhaseLinear
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ) :
    (complexModulePhase (FiniteOperatorAlgebra n)).IsPhaseLinearMap
      ((kuboMoriKernelCLM D A s).restrictScalars ℝ)
      (complexModulePhase ℂ) := by
  exact complexLinearMap_isPhaseLinear (kuboMoriKernelCLM D A s)

set_option synthInstance.maxHeartbeats 100000 in
theorem FaithfulDensityOperator.kuboMoriTransform_isHestenesPhaseLinear
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    (complexModulePhase (FiniteOperatorAlgebra n)).IsPhaseLinearMap
      ((D.kuboMoriTransformCLM h_rpow).restrictScalars ℝ)
      (complexModulePhase (FiniteOperatorAlgebra n)) := by
  exact complexLinearMap_isPhaseLinear (D.kuboMoriTransformCLM h_rpow)

set_option synthInstance.maxHeartbeats 100000 in
theorem FaithfulDensityOperator.inverseKuboMoriCLM_isHestenesPhaseLinear
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    (complexModulePhase (FiniteOperatorAlgebra n)).IsPhaseLinearMap
      ((D.inverseKuboMoriCLM h_rpow).restrictScalars ℝ)
      (complexModulePhase (FiniteOperatorAlgebra n)) := by
  exact complexLinearMap_isPhaseLinear (D.inverseKuboMoriCLM h_rpow)

end SouriauOnsagerBKM
