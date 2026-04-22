from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
WEYL = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylKKTAnomalyIdentity.lean"


def test_zero_scale_structured_projector_hypotheses_have_theorem_backed_collapse() -> None:
    text = WEYL.read_text(encoding="utf-8")

    assert "theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero" in text
