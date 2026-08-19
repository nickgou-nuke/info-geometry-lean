import InfoGeometry.Physics.Thermodynamics.LogCFTKMSModularTriple

/-!
# LogCFT KMS modular bridge

Canonical re-export of the thin logarithmic CFT KMS modular-triple packaging.
This bridge does not add analytic claims; it only forwards the verified
readout/interface layer from the physics owner.
-/

namespace InfoGeometry.Canonical.LogCFTKMSModularBridge

open InfoGeometry.Physics.Thermodynamics
open InfoGeometry.Physics.Thermodynamics.TopologicalMonodromyKMSBridge

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Canonical packaging alias for the logarithmic CFT KMS modular triple. -/
def canonical
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (hM : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperatorLaws M) :
    LogCFTKMSModularTriple (H := H) :=
  logCFTKMSCanonical (H := H) M hM

/-- The canonical packaging reuses the existing readout datum. -/
@[simp] theorem canonical_readout
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (hM : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperatorLaws M) :
    (canonical (H := H) M hM).readout =
      unipotentMonodromyReadoutDatum M hM :=
  rfl

/-- Compatibility alias for the positive inverse-temperature property. -/
theorem beta_pos (T : LogCFTKMSModularTriple (H := H)) :
    0 < (T.readout.beta : ℝ) :=
  InfoGeometry.Physics.Thermodynamics.logCFTKMS_beta_pos T

/-- Compatibility alias for the flow invariance property. -/
theorem flow_invariant (T : LogCFTKMSModularTriple (H := H)) :
    ∀ t : ℝ, ∀ X : H →L[ℝ] H,
      T.readout.state (T.readout.flow t X) = T.readout.state X :=
  InfoGeometry.Physics.Thermodynamics.logCFTKMS_flow_invariant T

end InfoGeometry.Canonical.LogCFTKMSModularBridge
