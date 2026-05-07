from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"


def test_zd_controlled_observer_closes_sinkhorn_equilibrium_when_zd_vanishes() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "theorem ofZDControlledObserver_δ_odd_eq_zero_of_ZD_eq_zero" in text
    assert "theorem ofZDControlledObserver_isRouterEquilibrium_of_ZD_eq_zero" in text
    assert "ofZDControlledObserver_routerResidual_eq_zero_of_ZD_eq_zero" in text
    assert "equilibrium_of_δ_odd_eq_zero (E := E)" in text
    assert "ofZDControlledObserver (E := E) CIK obs flow hControl" in text
