from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"


def test_weyl_thermodynamic_nonempty_bridge_routes_through_explicit_control() -> None:
    text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem observerDefectResidualWeylThermodynamicBoundedByZD_iff_nonempty_control" in text
    assert "theorem nonempty_observerDefectResidualWeylThermodynamicControl_of_boundedByZD" in text
    assert "theorem observerDefectResidualWeylThermodynamicBoundedByZD_of_nonempty_control" in text
    assert (
        "ObserverDefectResidualWeylThermodynamicBoundedByZD (E := E) CIK obs ↔\n"
        "      Nonempty (ObserverDefectResidualWeylThermodynamicControl (E := E) CIK obs)"
        in text
    )
    assert "Classical.choice" in text
    assert "nonempty_observerDefectResidualWeylThermodynamicControl_of_boundedByZD" in text
    assert "ofWeylThermodynamicControl (E := E) CIK obs flow" in text
