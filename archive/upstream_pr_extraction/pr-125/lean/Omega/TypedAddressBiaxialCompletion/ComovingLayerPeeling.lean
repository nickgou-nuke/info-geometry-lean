import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address restatement of the recursive layer-peeling theorem: the residual Fourier
transform and its leading decay gap identify the current layer, Fourier inversion recovers that
layer, and finite recursion recovers the full measure.
    thm:typed-address-biaxial-completion-comoving-layer-peeling -/
theorem paper_typed_address_biaxial_completion_comoving_layer_peeling
    (residualFourierTransform leadingDecayGapEstimate layerFourierInversion : Prop)
    (leadingDecayLayerIdentified layerFourierRecovered fullMeasureRecovered : Prop)
    (residualFourierTransform_h : residualFourierTransform)
    (leadingDecayGapEstimate_h : leadingDecayGapEstimate)
    (layerFourierInversion_h : layerFourierInversion)
    (identifyLeadingLayer :
      residualFourierTransform → leadingDecayGapEstimate → leadingDecayLayerIdentified)
    (recoverLayer :
      leadingDecayLayerIdentified → layerFourierInversion → layerFourierRecovered)
    (recoverMeasure : layerFourierRecovered → fullMeasureRecovered) :
    leadingDecayLayerIdentified ∧ layerFourierRecovered ∧ fullMeasureRecovered := by
  have hLead : leadingDecayLayerIdentified :=
    identifyLeadingLayer residualFourierTransform_h leadingDecayGapEstimate_h
  have hLayer : layerFourierRecovered :=
    recoverLayer hLead layerFourierInversion_h
  exact ⟨hLead, hLayer, recoverMeasure hLayer⟩

end Omega.TypedAddressBiaxialCompletion
