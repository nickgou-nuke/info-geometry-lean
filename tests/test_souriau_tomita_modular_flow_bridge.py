from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauTomitaModularFlowBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "Canonical" / "All.lean"


def test_souriau_tomita_modular_flow_bridge_is_source_owned() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure SouriauTomitaLogContext" in text
    assert "OperatorSouriauMoment.thermalGenerator" in text
    assert "def toRealModularLogData" in text
    assert "def souriauAdditiveModularFlow" in text
    assert "theorem tomita_deltaLog_eq_thermalGenerator" in text
    assert "theorem tomita_flow_eq_souriau_modularTransportFlow" in text
    assert "theorem souriauAdditiveModularFlow_apply_eq_modular_shift" in text
    assert "theorem souriauModularGenerator_eq_moment_geometricTemperature" in text


def test_souriau_tomita_bridge_is_in_canonical_umbrella() -> None:
    text = ALL.read_text(encoding="utf-8")

    assert "import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge" in text
