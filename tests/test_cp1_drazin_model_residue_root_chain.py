from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CP1 = REPO / "lean" / "InfoGeometry" / "GromovWittenErlangen" / "CP1DrazinModel.lean"


def test_cp1_edge_residue_zero_matches_current_minimal_bridge() -> None:
    text = CP1.read_text(encoding="utf-8")

    assert "def regularEdgeDrazin" in text
    assert "nilpotentPart := 0" in text
    assert "def bridge" in text
    assert "theorem edgeLocalizedDrazinResidue_line" in text
    assert "bridge.edgeLocalizedDrazinResidue Edge.line = 0" in text
    edge_block = text.split("theorem edgeLocalizedDrazinResidue_line", 1)[1].split("/-- Calibrated", 1)[0]
    assert "rfl" in edge_block
