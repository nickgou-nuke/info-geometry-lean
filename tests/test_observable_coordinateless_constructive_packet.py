from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def test_observable_coordinateless_constructive_packet_removes_explicit_sld_argument() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "theorem observable_coordinateless_constructive_packet" in text
    assert "let C := ω.toObservableCoordinatelessSouriauFisherContext beta J" in text
    assert "(sld : Tangent → Obs)" in text
    tail = text.split("theorem observable_coordinateless_constructive_packet", 1)[1]
    theorem_block = tail.split("theorem coordinateless_constructive_packet", 1)[0]
    assert "(sld : Tangent → Obs)" not in theorem_block
    assert "C.kms_identity A B" in theorem_block
