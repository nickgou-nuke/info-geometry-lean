import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingLayerPeeling

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the recursive defect-measure layer-peeling argument. It mirrors the
typed-address comoving package while renaming the recovered stages to the CircleDimension-facing
formulation. -/
structure DefectMeasureRecursiveLayerPeelingData where
  residualFourierTransform : Prop
  decayGapEstimate : Prop
  layerInversion : Prop
  residualFourierTransform_h : residualFourierTransform
  decayGapEstimate_h : decayGapEstimate
  layerInversion_h : layerInversion
  leadingLayerRecovered : Prop
  currentLayerRecovered : Prop
  fullMeasureRecovered : Prop
  recoverLeadingLayer :
    residualFourierTransform → decayGapEstimate → leadingLayerRecovered
  recoverCurrentLayer :
    leadingLayerRecovered → layerInversion → currentLayerRecovered
  recoverMeasure : currentLayerRecovered → fullMeasureRecovered

/-- Paper-facing recursive layer-peeling wrapper: after identifying the leading residual layer,
the current layer is inverted and finite recursion recovers the full defect measure.
    thm:cdim-defect-measure-recursive-layer-peeling -/
theorem paper_cdim_defect_measure_recursive_layer_peeling
    (D : DefectMeasureRecursiveLayerPeelingData) :
    D.leadingLayerRecovered ∧ D.currentLayerRecovered ∧ D.fullMeasureRecovered := by
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_layer_peeling
    D.residualFourierTransform D.decayGapEstimate D.layerInversion
    D.leadingLayerRecovered D.currentLayerRecovered D.fullMeasureRecovered
    D.residualFourierTransform_h D.decayGapEstimate_h D.layerInversion_h
    D.recoverLeadingLayer D.recoverCurrentLayer D.recoverMeasure

end Omega.CircleDimension
