import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LogDetRadonNikodymMechanism

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Operatorial Fisher/BKM probe bridge.

The theorem below is a statement about the operatorial transport Hessian on
`EndH`: after applying a continuous linear probe `ω`, the stationary second
variation is the probe of the double transport commutator.  It does not
identify that probe with a Radon--Nikodym derivative or with a
measure-theoretic log-volume; such scalar readouts are downstream shadows.
-/
@[rep_depth transport, capstone]
theorem operatorialHessian_probe_eq_double_transportCommutator
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
