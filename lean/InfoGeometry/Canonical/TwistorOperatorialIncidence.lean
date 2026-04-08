import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.EinsteinAnomalyOperator
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical.ConformalUnification

namespace CertifiedConformalInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open InfoGeometry.Krein
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Operatorial twistor incidence: the doubled-space projector obstruction vanishes.
This is the non-scalar, full operatorial incidence condition on the doubled carrier.
-/
def operatorialIncidence (CCI : CertifiedConformalInference E) : Prop :=
  CCI.liftedProjectorObstructionOperator = 0

/--
Operatorial incidence is equivalent to vanishing of the base chiral anomaly operator.
-/
theorem operatorialIncidence_iff_chiralAnomalyOperator_zero
    (CCI : CertifiedConformalInference E) :
    CCI.operatorialIncidence ↔ CCI.chiralAnomalyOperator = 0 := by
  constructor
  · intro hInc
    change CCI.liftedChiralAnomalyOperator = 0 at hInc
    change dualSheetLift (E := E) CCI.chiralAnomalyOperator = 0 at hInc
    exact (dualSheetLift_eq_zero_iff (E := E) (A := CCI.chiralAnomalyOperator)).1 hInc
  · intro hZero
    have hLift :=
      (dualSheetLift_eq_zero_iff (E := E) (A := CCI.chiralAnomalyOperator)).2 hZero
    change CCI.liftedChiralAnomalyOperator = 0
    change dualSheetLift (E := E) CCI.chiralAnomalyOperator = 0
    exact hLift

/--
Operatorial incidence is equivalent to vanishing of the certified projector
obstruction operator.
-/
theorem operatorialIncidence_iff_projectorObstructionOperator_zero
    (CCI : CertifiedConformalInference E) :
    CCI.operatorialIncidence ↔ CCI.projectorObstructionOperator = 0 := by
  constructor
  · intro hInc
    have hZero :
        CCI.chiralAnomalyOperator = 0 :=
      (operatorialIncidence_iff_chiralAnomalyOperator_zero (CCI := CCI)).1 hInc
    change CCI.chiralAnomalyOperator = 0
    exact hZero
  · intro hZero
    have hZero' : CCI.chiralAnomalyOperator = 0 := by
      change CCI.chiralAnomalyOperator = 0
      exact hZero
    exact (operatorialIncidence_iff_chiralAnomalyOperator_zero (CCI := CCI)).2 hZero'

end CertifiedConformalInference

end InfoGeometry.Canonical.ConformalUnification
