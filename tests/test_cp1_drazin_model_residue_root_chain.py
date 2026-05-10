from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CP1 = REPO / "lean" / "InfoGeometry" / "GromovWittenErlangen" / "CP1DrazinModel.lean"


def test_cp1_edge_residue_zero_is_derived_from_regular_nilpotent_root() -> None:
    text = CP1.read_text(encoding="utf-8")

    assert "theorem regularEdgeDrazin_nilpotentPart" in text
    assert "regularEdgeDrazin.nilpotentPart = 0" in text
    assert "theorem regularEdgeDrazin_localizedDrazinResidue" in text
    assert "RelativeCoreNilpotentDecomposition.localizedDrazinResidue" in text
    assert "theorem edgeLocalizedDrazinResidue_line" in text
    assert "regularEdgeDrazin_localizedDrazinResidue" in text
    assert "rfl" not in text.split("theorem edgeLocalizedDrazinResidue_line", 1)[1].split("/-- Calibrated", 1)[0]
