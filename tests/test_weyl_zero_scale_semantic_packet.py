from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
WEYL = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylKKTAnomalyIdentity.lean"


def test_zero_scale_semantic_packet_has_theorem_backed_zero_readout() -> None:
    text = WEYL.read_text(encoding="utf-8")

    assert "theorem semanticCollapsePacket_of_structuredProjectorHypotheses_of_chiralScale_eq_zero" in text
