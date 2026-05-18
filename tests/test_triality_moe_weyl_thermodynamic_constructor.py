from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"


def test_weyl_thermodynamic_bound_exposes_canonical_constructor() -> None:
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "def ObserverDefectResidualWeylThermodynamicBoundedByZD" in triality_text
    assert "theorem observerDefectResidualWeylThermodynamicBoundedByZD_of_comparison" in triality_text
    assert "noncomputable def ofWeylThermodynamicBoundedByZD" in triality_text
    assert "theorem ofWeylThermodynamicBoundedByZD_routerResidual" in triality_text
    assert "ObserverDefectResidualWeylThermodynamicBoundedByZD (E := E) CIK obs" in triality_text
    assert "ofCanonicalObserverDefect (E := E) CIK obs flow cmp" in triality_text
