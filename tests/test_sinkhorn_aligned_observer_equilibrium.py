from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"


def test_aligned_observer_closes_sinkhorn_equilibrium() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "theorem ofAlignedObserver_δ_odd_eq_zero" in text
    assert "theorem ofAlignedObserver_isRouterEquilibrium" in text
    assert "ofAlignedObserver_routerResidual" in text
    assert "equilibrium_of_δ_odd_eq_zero (E := E)" in text
    assert "ofAlignedObserver (E := E) CIK obs flow hAlign" in text
