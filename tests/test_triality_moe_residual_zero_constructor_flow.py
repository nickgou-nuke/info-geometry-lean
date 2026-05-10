from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OBSERVER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_residual_zero_constructor_exposes_zero_residual_flow_route() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")
    observer_text = OBSERVER.read_text(encoding="utf-8")

    assert "theorem observerDefectResidual_norm_le_ZD_of_residual_eq_zero" in observer_text
    assert "theorem observerDeviationControlledByZD_of_residual_eq_zero" in observer_text
    assert "noncomputable def ofResidualZeroObserver" in triality_text
    assert "theorem ofResidualZeroObserver_routerResidual" in triality_text
    assert "theorem ofResidualZeroObserver_sourcedGenerator_eq_flow" in triality_text
    assert "theorem ofResidualZeroObserver_sourcedGenerator_respects_cut" in triality_text
    assert "observerDefectResidual_norm_le_ZD_of_residual_eq_zero" in triality_text
    assert "observerDefectResidual_eq_zero_of_residual_eq_zero" not in observer_text
