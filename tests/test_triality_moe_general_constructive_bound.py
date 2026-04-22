from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OWNER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_general_observer_defect_bound_is_theorem_backed() -> None:
    owner_text = OWNER.read_text(encoding="utf-8")
    triality_text = TRIALITY.read_text(encoding="utf-8")

    theorem_anchor = "theorem observerDefectResidual_norm_le_ZD\n"
    theorem_anchor_indented = "theorem observerDefectResidual_norm_le_ZD\r\n"

    assert theorem_anchor in owner_text or theorem_anchor in triality_text or theorem_anchor_indented in owner_text or theorem_anchor_indented in triality_text
    assert "def ObserverDeviationControlledByZD" in owner_text
    assert "theorem observerDefectResidual_eq_projectorCompression_commutator_deviation" in owner_text
    assert "theorem observerDeviationControlledByZD_iff_observerDefectResidual_norm_le_ZD" in owner_text
    assert "theorem observerDeviationControlledByZD_of_compressedDeviation_eq_zero" in owner_text
    assert "theorem observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in owner_text
    assert "noncomputable def ofZDControlledObserver" in triality_text
    assert "theorem ofZDControlledObserver_routerResidual_eq_zero_of_ZD_eq_zero" in triality_text
    assert "observerDefectResidual_norm_le_ZD (E := E) (CIK := CIK) (obs := obs) hControl" in triality_text
    assert "observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero" in triality_text
