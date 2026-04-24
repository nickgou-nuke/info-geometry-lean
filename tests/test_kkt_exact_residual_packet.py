from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauLieThermoKKTBridge.lean"


def test_exact_residuals_construct_kkt_shadow() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "theorem mk_exact" in text
    assert "DimensionAgnosticKKTResiduals.toShadow DimensionAgnosticKKTResiduals.exact" in text
    assert "theorem exact_stationarity_packet" in text
