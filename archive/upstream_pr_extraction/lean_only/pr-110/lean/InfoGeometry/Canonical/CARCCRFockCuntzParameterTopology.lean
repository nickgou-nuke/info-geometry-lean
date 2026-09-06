import InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat

/-!
# CAR/CCR/Cuntz readouts of the owned q-parameter topology

`CStarCuntzCARCCRParameterTopCat` owns the parameter space, its continuous
residual, and the closed fibers.  This companion contributes only the
relation-specific readout lemmas, so no second parameter-space construction is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.CARCCRFockCuntzParameterTopology

open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
open InfoGeometry.Physics.CStarCuntzTensorQuotient

variable {A : Type*} [CStarAlgebra A]

theorem car_pair_mem_parameter_zero_fiber
    (c cstar : A) (h : c * cstar + cstar * c = 1) :
    (c, (cstar, (-1 : A))) ∈
      qCcrParameterZeroLocus (A := A) := by
  change qCcrParameterResidualContinuousMap (A := A)
      (c, (cstar, (-1 : A))) = 0
  simpa [qCcrParameterResidualContinuousMap] using
    (car_is_neg_one_qccr c cstar h)

theorem ccr_pair_mem_parameter_one_fiber
    (c cstar : A) (h : c * cstar - cstar * c = 1) :
    (c, (cstar, (1 : A))) ∈
      qCcrParameterZeroLocus (A := A) := by
  change qCcrParameterResidualContinuousMap (A := A)
      (c, (cstar, (1 : A))) = 0
  simpa [qCcrParameterResidualContinuousMap] using
    (ccr_is_plus_one_qccr c cstar h)

theorem cstar_cuntz_pair_mem_parameter_zero_fiber
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : CStarCuntzFamily A ι) (i : ι) :
    (star (F.S i), (F.S i, (0 : A))) ∈
      qCcrParameterZeroLocus (A := A) := by
  change qCcrParameterResidualContinuousMap (A := A)
      (star (F.S i), (F.S i, (0 : A))) = 0
  simpa [qCcrParameterResidualContinuousMap] using
    (cstar_cuntz_generator_qccr_zero F i)

end InfoGeometry.Canonical.CARCCRFockCuntzParameterTopology
