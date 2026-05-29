from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"


def test_strain_zero_observer_routes_sinkhorn_sourced_generator_collapse() -> None:
    sinkhorn_text = SINKHORN.read_text(encoding="utf-8")
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem ofStrainZeroObserver_sourcedGenerator_eq_flow" in triality_text
    assert "theorem ofStrainZeroObserver_sourcedGenerator_eq_flow" in sinkhorn_text
    assert (
        "InfoGeometry.LLM.TrialityMoE.RouterDefectBoundBridge.ofStrainZeroObserver_sourcedGenerator_eq_flow"
        in sinkhorn_text
    )
    assert "(ofStrainZeroObserver (E := E) CIK obs flow hStrain).sourcedGenerator = flow.K0" in sinkhorn_text
