import InfoGeometry.Canonical.SplitG2HodgeDualFourForm
import InfoGeometry.Canonical.SplitOctonionCanonicalThreeForm
import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions
import InfoGeometry.Canonical.SplitG2HodgeTransportBridge

namespace InfoGeometry.Canonical

/-!
# Native metric-oriented Hodge-star data

This file is an identification bridge, not a second Hodge implementation.
The native `LinearEquiv` packages the already-existing explicit `3 ↔ 4`
duality, while the metric/orientation readout is recorded separately and
reused by downstream calibration bridges.
-/

structure SplitG2MetricDerivedHodgeStar where
  metricOrientation : SplitOctonionMetricOrientation
  metricStar : SplitG2ThreeForms ≃ₗ[ℚ] SplitG2FourForms

/-!
## Restriction to the imaginary carrier

The ambient metric is already owned by
`SplitOctonionCanonicalThreeForm`.  The imaginary metric is its native
restriction; no new bilinear form is introduced here.
-/

noncomputable def imaginarySplitMetric :
    LinearMap.BilinForm ℚ imaginarySplitOctonion :=
  splitOctonionMetric.restrict imaginarySplitOctonion

@[simp] theorem imaginarySplitMetric_apply
    (x y : imaginarySplitOctonion) :
    imaginarySplitMetric x y = splitOctonionMetric x.1 y.1 := by
  rfl

theorem imaginarySplitMetric_quadratic
    (x : imaginarySplitOctonion) :
    imaginarySplitMetric x x = coordinateSplitNorm x.1 := by
  rw [imaginarySplitMetric_apply]
  exact splitOctonionMetric_quadratic x.1

namespace SplitG2MetricDerivedHodgeStar

def dualData (H : SplitG2MetricDerivedHodgeStar) : SplitG2HodgeDualData :=
  H.metricStar

def metricStar34 (H : SplitG2MetricDerivedHodgeStar) :
    SplitG2ThreeForms →ₗ[ℚ] SplitG2FourForms :=
  H.metricStar.toLinearMap

def metricStar43 (H : SplitG2MetricDerivedHodgeStar) :
    SplitG2FourForms →ₗ[ℚ] SplitG2ThreeForms :=
  H.metricStar.symm.toLinearMap

def metricDerivedCoassociativeFourForm
    (H : SplitG2MetricDerivedHodgeStar) (φ : SplitG2ThreeForms) :
    SplitG2FourForms :=
  H.metricStar34 φ

/-!
## Metric readout

The metric-orientation bundle is tied to the already existing coordinate norm
by its `metric_eq` field.  These lemmas expose the resulting finite signature
readout without asserting a separate `HasSignature` instance or introducing a
second metric model.
-/

theorem metricOrientation_quadratic
    (H : SplitG2MetricDerivedHodgeStar)
    (x : StandardRationalSplitOctonion) :
    H.metricOrientation.metric x x = coordinateSplitNorm x := by
  rw [H.metricOrientation.metric_eq]
  exact splitOctonionMetric_quadratic x

theorem metricOrientation_basis_quadratic
    (H : SplitG2MetricDerivedHodgeStar)
    (b : IntegralSplitBasis) (q : ℚ) :
    H.metricOrientation.metric (Pi.single b q) (Pi.single b q) =
      match b with
      | .one => q ^ 2
      | .l => -q ^ 2
      | .i => q ^ 2
      | .il => -q ^ 2
      | .j => q ^ 2
      | .jl => -q ^ 2
      | .k => q ^ 2
      | .kl => -q ^ 2 := by
  rw [metricOrientation_quadratic]
  exact coordinateSplitNorm_single_basis b q


theorem explicit_star34_eq_metricHodgeStar
    (H : SplitG2MetricDerivedHodgeStar) :
    (H.dualData).star34 = H.metricStar34 := rfl

theorem explicit_star43_eq_metricHodgeStar
    (H : SplitG2MetricDerivedHodgeStar) :
    (H.dualData).star43 = H.metricStar43 := rfl

/-- The metric-derived `3 → 4` star is the same as the explicit `star34`
map already stored in the dual-data owner. -/
theorem metricHodgeStar34_eq_explicitStar34
    (H : SplitG2MetricDerivedHodgeStar) :
    H.metricStar34 = (H.dualData).star34 := rfl

/-- The metric-derived `4 → 3` star is the same as the explicit `star43`
map already stored in the dual-data owner. -/
theorem metricHodgeStar43_eq_explicitStar43
    (H : SplitG2MetricDerivedHodgeStar) :
    H.metricStar43 = (H.dualData).star43 := rfl

theorem metricStar43_metricStar34
    (H : SplitG2MetricDerivedHodgeStar)
    (φ : SplitG2ThreeForms) :
    H.metricStar43 (H.metricStar34 φ) = φ := by
  simpa [metricStar43, metricStar34] using H.metricStar.symm_apply_apply φ

theorem metricStar34_metricStar43
    (H : SplitG2MetricDerivedHodgeStar)
    (ψ : SplitG2FourForms) :
    H.metricStar34 (H.metricStar43 ψ) = ψ := by
  simpa [metricStar43, metricStar34] using H.metricStar.apply_symm_apply ψ

theorem hodge_star_double_application_identity
    (H : SplitG2MetricDerivedHodgeStar) (φ : SplitG2ThreeForms) :
    H.metricStar43 (metricDerivedCoassociativeFourForm H φ) = φ := by
  exact H.metricStar43_metricStar34 φ

theorem metricDerivedCoassociativeFourForm_eq_explicit
    (H : SplitG2MetricDerivedHodgeStar) (φ : SplitG2ThreeForms) :
    metricDerivedCoassociativeFourForm H φ =
      (H.dualData).coassociativeFourForm φ := rfl

/-- The explicit coassociative four-form is the same data as the metric-derived one. -/
theorem coassociativeFourForm_eq_metricDerivedCoassociativeFourForm
    (H : SplitG2MetricDerivedHodgeStar) (φ : SplitG2ThreeForms) :
    (H.dualData).coassociativeFourForm φ =
      metricDerivedCoassociativeFourForm H φ := rfl

/-- The canonical coassociative form is the metric-derived `3 → 4`
transport of the split `G₂` three-form. -/
theorem coassociativeFourForm_eq_metricHodgeStar_threeForm
    (H : SplitG2MetricDerivedHodgeStar) (φ : SplitG2ThreeForms) :
    (H.dualData).coassociativeFourForm φ = H.metricStar34 φ := rfl

theorem metricDerivedCoassociativeFourForm_eq_metricHodgeStar_threeForm
    (H : SplitG2MetricDerivedHodgeStar) (φ : SplitG2ThreeForms) :
    metricDerivedCoassociativeFourForm H φ = H.metricStar34 φ := rfl

/-- The chosen Hodge data commutes with pullback whenever the transport
bridge witnesses compatibility with the explicit star. -/
theorem pullback_commutes_metricStar34
    (H : SplitG2MetricDerivedHodgeStar)
    (C : SplitG2HodgeCompatibleAutomorphism H.dualData)
    (φ : SplitG2ThreeForms) :
    pullbackForm 4 C.automorphism.toLinearEquiv (H.metricStar34 φ) =
      H.metricStar34 (pullbackForm 3 C.automorphism.toLinearEquiv φ) :=
  C.star34_compatible φ

theorem g2_compatible_preserves_metricDerivedCoassociativeFourForm
    (H : SplitG2MetricDerivedHodgeStar)
    (C : SplitG2HodgeCompatibleAutomorphism H.dualData)
    (φ : SplitG2ThreeForms)
    (hφ : pullbackForm 3 C.automorphism.toLinearEquiv φ = φ) :
    pullbackForm 4 C.automorphism.toLinearEquiv
        (metricDerivedCoassociativeFourForm H φ) =
      metricDerivedCoassociativeFourForm H φ := by
  exact C.preserves_coassociativeFourForm φ hφ

end SplitG2MetricDerivedHodgeStar

end InfoGeometry.Canonical
