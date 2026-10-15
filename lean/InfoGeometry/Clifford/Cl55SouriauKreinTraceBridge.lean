import InfoGeometry.Clifford.Cl55SuperTKK
import Mathlib.LinearAlgebra.Trace

/-!
# Souriau trace readout on the Cl(5,5) vacuum ideal and its Krein carrier

The vacuum-ideal/spinor equivalence in `Cl55SuperTKK` identifies the same
32-dimensional carrier with a doubled real Krein space.  This module records
the trace transport needed to evaluate any finite operator partition
function on either presentation.  It does not assert that a particular
operator family is an exponential, nor that a Pin(5,5) group integral exists.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SouriauKreinTraceBridge

open InfoGeometry.Clifford.Cl55SuperTKK

/-- The trace of a vacuum-ideal endomorphism is unchanged when the operator is
transported to the doubled real Krein carrier. -/
theorem idealTrace_eq_kreinTrace (A : EndV) :
    LinearMap.trace ℝ KreinDouble
        ((idealKreinEquiv.conjAlgEquiv ℝ) A) =
      LinearMap.trace ℝ V A := by
  change LinearMap.trace ℝ KreinDouble (idealKreinEquiv.conj A) = _
  exact LinearMap.trace_conj' A idealKreinEquiv

end InfoGeometry.Clifford.Cl55SouriauKreinTraceBridge

end
