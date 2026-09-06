import Mathlib
import InfoGeometry.Canonical.RadonNikodymFisherMetricBridge
import InfoGeometry.Algebra.SplitOctonionColeFurySpinorBridge

noncomputable section

namespace InfoGeometry.Supersymmetry.OctonionicKugoOjima

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Algebra.ColeFurySpinorBridge
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- 1. БРСТ оператор Q_B, произтичащ от симетриите на разцепените октониони. -/
def brstCharge (X A : EndH) : EndH :=
  transportCommutator X A

/-- 
2. Критерият на Куго-Оджима за конфайнмънт на цвета.
   Физическият безцветен вакуум се дефинира от състоянията, отразени обратно от бариерата.
   Алгебрично това означава, че двойният комутатор (Хесианът) изчезва върху вакуума.
-/
def kugoOjimaConfinementCondition (ω : EndH →L[ℝ] ℝ) (X A : EndH) : Prop :=
  ω (transportCommutator X (brstCharge X A)) = 0

/-- 
**Finite readout theorem**:
an explicit vanishing Hessian readout is sufficient for the
Kugo--Ojima confinement condition.  No octonion-to-spinor representation is
claimed here; that representation requires a separate, nonzero owner.
-/
@[rep_depth transport]
theorem kugoOjima_confinement_of_hessian_barrier
    (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (hHessian : deriv (fun t : ℝ => deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t) 0 =
                ω (transportCommutator X (transportCommutator X A)))
    (hBarrier : deriv (fun t : ℝ => deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t) 0 = 0) :
    kugoOjimaConfinementCondition ω X A := by
  dsimp [kugoOjimaConfinementCondition, brstCharge]
  rw [← hHessian, hBarrier]

end InfoGeometry.Supersymmetry.OctonionicKugoOjima
