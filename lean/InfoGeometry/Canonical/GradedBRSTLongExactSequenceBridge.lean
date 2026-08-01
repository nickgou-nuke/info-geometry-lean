import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge
import InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
import InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge
import InfoGeometry.Canonical.GradedBRSTOperatorSequenceBridge
import InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.GradedBRSTLongExactSequenceBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
open InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge
open InfoGeometry.Canonical.GradedBRSTOperatorSequenceBridge
open InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
open InfoGeometry.Canonical.BRSTExactClassZeroBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Graded Sequence BRST Charge Null-State Inclusion Q(E_g) ⊆ Ker(Q). -/
theorem graded_sequence_charge_closed
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (chi : ExteriorAlgebra R V) :
    q (q chi) = 0 := by
  exact LinearMap.congr_fun hq2 chi

/-- **Theorem**: Graded Sequence State Class Zero [Q χ_g] = 0 ∈ H_Q for all Ghost Sectors g. -/
theorem graded_sequence_class_zero
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (g_prev : R)
    (chi : ghostEigenspace g_op g_prev) :
    Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨q chi.1, graded_sequence_charge_closed q g_op hq2 chi.1⟩ =
      (Submodule.Quotient.mk 0 : brstCohomologyModule q hq2) := by
  exact exact_state_class_eq_zero q hq2 chi.1

end InfoGeometry.Canonical.GradedBRSTLongExactSequenceBridge
