import InfoGeometry.Canonical.KreinCarrierInstances.Datum
import InfoGeometry.Canonical.KreinCarrierInstances.RotorFlow
import InfoGeometry.Canonical.KreinCarrierInstances.CoreProjector
import InfoGeometry.Canonical.KreinCarrierInstances.RelativeFredholm
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

theorem concreteBridgeKlein_core_fredholm_count_comparison :
    concreteRelativeFredholmKlein.relativeCountDensity =
      Real.log (1 + concreteRelativeFredholmKlein.fredholm.kreinTrace) := by
  dsimp [concreteRelativeFredholmKlein]
  rw [add_zero, Real.log_one]

/-- Concrete Hestenes/Krein modular Fredholm bridge on the Klein carrier. -/
def concreteBridgeKlein : HestenesKreinModularFredholmBridge KleinBottleCarrier where
  datum := concreteKreinDatumKlein
  flow := concreteRotorFlowKlein concreteKreinDatumKlein
  core := concreteCoreProjectorKlein concreteKreinDatumKlein
  relativeFredholm := concreteRelativeFredholmKlein
  core_fredholm_count_comparison := concreteBridgeKlein_core_fredholm_count_comparison

/-- The concrete bridge has zero Krein trace by explicit construction. -/
theorem concreteBridgeKlein_kreinTrace :
    concreteBridgeKlein.relativeFredholm.fredholm.kreinTrace = 0 := by
  rfl

/-- The arithmetic input for `137`: its 2-adic valuation is zero. -/
theorem padicValNat_two_137 : padicValNat 2 137 = 0 := by
  norm_num [padicValNat.eq_zero_of_not_dvd]

/--
The concrete bridge has the stated trace-zero law for `137`.  The proof is
still a hardcoded readout of this concrete zero-defect bridge; it is not an
unconditional p-adic anomaly theorem.
-/
theorem concreteBridgeKlein_traceZeroAnomalyResolution_137 :
    HestenesKreinModularFredholmBridge.TraceZeroAnomalyResolution
      concreteBridgeKlein 137 := by
  intro _h137
  exact concreteBridgeKlein_kreinTrace

/-- Read back trace zero from the explicit `137` p-adic valuation law. -/
theorem concreteBridgeKlein_traceZero_of_padicValNat_137 :
    concreteBridgeKlein.relativeFredholm.fredholm.kreinTrace = 0 :=
  concreteBridgeKlein_traceZeroAnomalyResolution_137 padicValNat_two_137

end
