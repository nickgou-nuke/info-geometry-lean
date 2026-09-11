import InfoGeometry.Canonical.SplitG2MetricCalibrationPrerequisites
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitG2VolumeAndGramPairing

namespace InfoGeometry.Canonical

abbrev SplitG2SevenForms := SplitForm7

/-!
# Split-G2 Hodge/wedge bridge surface

This module is a thin theorem-safe bridge over the native exterior product,
top-degree volume form, and Gram-determinant pairing already owned in the
split-G2 calibration prerequisites.  It reexports those pieces under a stable
split-G2 Hodge-facing namespace.

It does not assert the unresolved characterization identity
`α ∧ metricStar34 H β = formPairing α β • volume`.
-/

/-- Compatibility alias for the split `3 + 4` wedge product. -/
noncomputable abbrev splitG2HodgeWedge34 : SplitG2ThreeForms → SplitG2FourForms →
    SplitG2SevenForms :=
  wedge34

/-- Compatibility alias for the canonical top-degree volume form. -/
noncomputable abbrev splitG2HodgeVolumeForm : SplitG2SevenForms :=
  splitG2VolumeForm

/-- Compatibility alias for the decomposable 3-form Gram pairing. -/
noncomputable abbrev splitG2HodgePairing3 :
    (Fin 3 → imaginarySplitOctonion) →
    (Fin 3 → imaginarySplitOctonion) → ℚ :=
  decomposableExteriorMetricPairing 3

theorem splitG2HodgeWedge34_eq_wedge34 :
    splitG2HodgeWedge34 = wedge34 := rfl

theorem splitG2HodgeVolumeForm_basis :
    splitG2HodgeVolumeForm
        (fun i => imaginarySplitOctonionBasis i) = 1 := by
  simpa [splitG2HodgeVolumeForm] using splitG2VolumeForm_basis

theorem splitG2HodgePairing3_swap
    (v w : Fin 3 → imaginarySplitOctonion) :
    splitG2HodgePairing3 v w = splitG2HodgePairing3 w v := by
  simpa [splitG2HodgePairing3] using
    decomposableExteriorMetricPairing_swap 3 v w

theorem splitG2HodgeWedge34_swap_reindex
    (α : SplitG2ThreeForms) (β : SplitG2FourForms) :
    splitG2HodgeWedge34 α β =
      (scalarWedge34 α β).domDomCongr finSumFinEquiv := by
  simpa [splitG2HodgeWedge34] using wedge34_swap_reindex α β

end InfoGeometry.Canonical
