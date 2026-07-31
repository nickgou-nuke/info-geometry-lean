import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.LogDetRadonNikodymMechanism

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
**The "Red Line" Bridge: Radon-Nikodym Log-Volume to Fisher/BKM Metric**

Това е математическият мост, свързващ информационния обем (логаритъма от
Радон-Никодим производната или Келеровия потенциал) с Квантовата Метрика
на Фишер (Bogoliubov-Kubo-Mori).

Втората производна (Хесианът) на логаритмичния скаларен readout на транспортния
поток, изчислена в стационарния вакуум, съвпада точно с BKM метриката
(двойния транспортен комутатор).
-/
@[rep_depth transport, capstone]
theorem radonNikodym_logVolume_to_fisherBKM_metric_bridge
    (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (hNonzero : ∀ t : ℝ, scalarTransportReadout (E := E) ω X A t ≠ 0)
    (hNorm : ω A = 1)
    (hStationary : ω (RelationalInformationDynamics.operatorInformationFirstVariation (E := E) X A) = 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t) 0 =
    ω (transportCommutator X (transportCommutator X A)) := by
  calc deriv (fun t : ℝ => deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t) 0
      = ω (operatorInformationHessian (E := E) X A) :=
        deriv2_scalarLogReadout_zero_eq_probe_operatorInformationHessian_of_stationary (E := E) ω X A hNonzero hNorm hStationary
    _ = ω (transportCommutator X (transportCommutator X A)) := by rw [operatorInformationHessian_eq_double_transportCommutator]

end InfoGeometry.Canonical
