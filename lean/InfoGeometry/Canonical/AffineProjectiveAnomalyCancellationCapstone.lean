import InfoGeometry.Canonical.AffineProjectiveAnomalyCancellationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.AffineProjectiveAnomalyCancellationCapstone

open InfoGeometry.Canonical.AffineProjectiveAnomaly
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
🏆 **CAPSTONE: Canonical Verification of Doubled-Krein Anomaly Cancellation**
-/
theorem affine_projective_anomaly_cancellation_canonical_capstone
    (A : AnomalyFunctional E)
    (Op : SkewDiracOperator E) :
    A.anomaly Op.D + A.anomaly (conjugateDirac Op) = 0 :=
  doubled_krein_anomaly_cancellation A Op

end InfoGeometry.Canonical.AffineProjectiveAnomalyCancellationCapstone
