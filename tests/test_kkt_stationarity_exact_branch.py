from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauLieThermoKKTBridge.lean"


def test_kkt_stationarity_exact_branch_exists() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "theorem kktStationarity_packet_of_exact" in text
    assert "DimensionAgnosticKKTResiduals.toShadow DimensionAgnosticKKTResiduals.exact" in text
    assert "KKTEntropyStationarityShadow.mk_exact" in text
