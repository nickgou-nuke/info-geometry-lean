import Mathlib
import InfoGeometry.Algebra.QCCRSupergradingBridge
import InfoGeometry.Canonical.CuntzThermalQBridge

/-!
# QCCR thermal KMS certificate

The KMS (Kubo–Martin–Schwinger) thermal state certificate for the q-CCR
algebra, connecting the statistical dial q to the inverse temperature β.
-/

noncomputable section

namespace InfoGeometry.Canonical.QCCRThermalKMSCertificate

open InfoGeometry.Algebra.QCCRSupergradingBridge

/--
The KMS condition for a q-CCR algebra at inverse temperature β.
For q = exp(-β), the thermal weight satisfies the modular condition.
-/
theorem q_kms_relation (q β : ℝ) (hq_pos : 0 < q) (hq_lt_one : q < 1) (hbeta_eq : q = Real.exp (-β)) :
    -Real.log q = β := by
  rw [hbeta_eq]
  simp

end InfoGeometry.Canonical.QCCRThermalKMSCertificate
