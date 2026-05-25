from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"


def test_strain_zero_observer_closes_sinkhorn_equilibrium() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "theorem ofStrainZeroObserver_δ_odd_eq_zero" in text
    assert "theorem ofStrainZeroObserver_isRouterEquilibrium" in text
    assert "ofStrainZeroObserver_routerResidual" in text
    assert "equilibrium_of_δ_odd_eq_zero (E := E)" in text
    assert "ofStrainZeroObserver (E := E) CIK obs flow hStrain" in text
