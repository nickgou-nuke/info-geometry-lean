import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingLayerPeeling

namespace Omega.CircleDimension

/-- Paper-facing recursive layer-peeling wrapper: after identifying the leading residual layer,
the current layer is inverted and finite recursion recovers the full defect measure.
    thm:cdim-defect-measure-recursive-layer-peeling -/
theorem paper_cdim_defect_measure_recursive_layer_peeling
    (residualFourierTransform decayGapEstimate layerInversion : Prop)
    (leadingLayerRecovered currentLayerRecovered fullMeasureRecovered : Prop)
    (hResidual : residualFourierTransform)
    (hDecay : decayGapEstimate)
    (hInversion : layerInversion)
    (recoverLeadingLayer :
      residualFourierTransform → decayGapEstimate → leadingLayerRecovered)
    (recoverCurrentLayer :
      leadingLayerRecovered → layerInversion → currentLayerRecovered)
    (recoverMeasure : currentLayerRecovered → fullMeasureRecovered) :
    leadingLayerRecovered ∧ currentLayerRecovered ∧ fullMeasureRecovered := by
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_layer_peeling
    residualFourierTransform decayGapEstimate layerInversion
    leadingLayerRecovered currentLayerRecovered fullMeasureRecovered
    hResidual hDecay hInversion recoverLeadingLayer recoverCurrentLayer recoverMeasure

end Omega.CircleDimension
