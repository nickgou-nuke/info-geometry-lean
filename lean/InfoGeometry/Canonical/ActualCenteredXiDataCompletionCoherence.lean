import InfoGeometry.Canonical.ActualCenteredXiDataBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ActualCompletedXiDatumBridge

/-!
# Coherence of the concrete centered completed-Xi realization

The concrete centered `riemannXi` datum is the affine-coordinate transport of
the concrete completed-Xi datum.  This is only a structure-level coherence
statement; it introduces no new analytic hypotheses or zero-set claims.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualCenteredXiDataCompletionCoherence

open InfoGeometry.Canonical.ActualCenteredXiDataBridge
open InfoGeometry.Canonical.ActualCompletedXiDatumBridge
open InfoGeometry.Arithmetic.RiemannZetaEquivalences

theorem actualCenteredXiData_eq_centeredXiDataOfCompletedDatum :
    actualCenteredXiData =
      centeredXiDataOfCompletedDatum actualCompletedXiDatum_concrete := by
  rfl

@[simp] theorem actualCenteredXiData_completion_lambda (s : ℂ) :
    (centeredXiDataOfCompletedDatum actualCompletedXiDatum_concrete).lambda s =
      riemannXi s := rfl

@[simp] theorem actualCenteredXiData_completion_xi (z : ℂ) :
    (centeredXiDataOfCompletedDatum actualCompletedXiDatum_concrete).xi z =
      riemannXi ((1 / 2 : ℂ) + z) := rfl

end InfoGeometry.Canonical.ActualCenteredXiDataCompletionCoherence
