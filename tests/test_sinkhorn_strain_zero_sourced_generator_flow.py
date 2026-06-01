from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"


def test_strain_zero_observer_routes_sinkhorn_sourced_generator_collapse() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem ofStrainZeroObserver_sourcedGenerator_eq_flow" in triality_text
    assert "(ofStrainZeroObserver (E := E) CIK obs flow hStrain).sourcedGenerator = flow.K0" in triality_text
