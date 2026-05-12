from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "DrazinPenroseDilationKKT.lean"


def test_drazin_penrose_dilation_kkt_gauge_surface_exists() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "abbrev P_D" in text
    assert "abbrev Q_D" in text
    assert "noncomputable abbrev GammaS" in text
    assert "abbrev leftSupercharge" in text
    assert "abbrev rightSupercharge" in text
    assert "def IsInRegularSector" in text
    assert "def IsInNullSector" in text
    assert "def PreservesP_D" in text
    assert "def PreservesQ_D" in text
    assert "def PreservesGammaS" in text
    assert "def FlipsGammaS" in text
    assert "theorem maps_regular_sector_of_preservesP_D" in text
    assert "theorem maps_null_sector_of_preservesQ_D" in text
    assert "theorem leftSupercharge_flipsGammaS" in text
    assert "theorem rightSupercharge_flipsGammaS" in text
