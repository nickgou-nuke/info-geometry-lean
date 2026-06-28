import InfoGeometry.Canonical.KreinCarrierInstances

/-!
# InfoGeometry.Physics.ConcreteKleinBridge

Thin projection package over the owner file
`InfoGeometry.Canonical.KreinCarrierInstances`.

This keeps the mathematically correct `WithLp 2 (ℝ × ℝ)` carrier and reuses the
already-verified concrete Klein/Krein datum instead of duplicating raw-product
smoke-test code.

Honesty boundary:
- the carrier is the `L²` product carrier, not raw `ℝ × ℝ`
- the trace-zero theorem is still a concrete readout theorem for the explicit
  zero-defect bridge
- this file is a projection surface, not a new owner formalization
-/

namespace InfoGeometry.Physics.ConcreteKleinBridge

abbrev KleinCoverCarrier : Type := _root_.KleinBottleCarrier

abbrev fundamentalSymmetryKlein : KleinCoverCarrier →L[ℝ] KleinCoverCarrier :=
  _root_.fundamentalSymmetryKlein

abbrev modularGeneratorKlein : KleinCoverCarrier →L[ℝ] KleinCoverCarrier :=
  _root_.modularGeneratorKlein

noncomputable abbrev concreteKreinDatumKlein := _root_.concreteKreinDatumKlein
noncomputable abbrev concreteRotorFlowKlein := _root_.concreteRotorFlowKlein
noncomputable abbrev concreteCoreProjectorKlein := _root_.concreteCoreProjectorKlein
noncomputable abbrev concreteRelativeFredholmKlein := _root_.concreteRelativeFredholmKlein
noncomputable abbrev concreteBridgeKlein := _root_.concreteBridgeKlein

/-- The fundamental symmetry on the `WithLp` Klein carrier is involutive. -/
theorem fundamentalSymmetryKlein_sq :
    fundamentalSymmetryKlein * fundamentalSymmetryKlein =
      ContinuousLinearMap.id ℝ KleinCoverCarrier :=
  _root_.fundamentalSymmetryKlein_sq

/-- Honest concrete readout: the explicit bridge has zero Krein trace. -/
theorem concreteBridgeKlein_kreinTrace_zero :
    concreteBridgeKlein.relativeFredholm.fredholm.kreinTrace = 0 :=
  _root_.concreteBridgeKlein_kreinTrace

/-- Re-export the concrete 2-adic valuation fact for `137`. -/
theorem padicValNat_137_eq_zero : padicValNat 2 137 = 0 :=
  _root_.padicValNat_two_137

/--
Projection of the owner theorem: this is still a concrete bridge theorem, not a
uniform p-adic anomaly theorem for arbitrary bridges.
-/
theorem concreteBridgeKlein_traceZeroAnomalyResolution_137 :
    InfoGeometry.Canonical.HestenesKreinModularGeometry.HestenesKreinModularFredholmBridge.TraceZeroAnomalyResolution
      concreteBridgeKlein 137 :=
  _root_.concreteBridgeKlein_traceZeroAnomalyResolution_137

end InfoGeometry.Physics.ConcreteKleinBridge
