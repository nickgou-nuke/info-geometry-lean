from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def test_minimal_cyclic_adapter_exports_kms_state_readback() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    start = text.rindex("namespace MinimalCyclicCoordinatelessSouriauContext")
    tail = text[start:]
    end = tail.index("end MinimalCyclicCoordinatelessSouriauContext")
    block = tail[:end]

    assert "def toCoordinatelessSouriauFisherContext :" in block
    assert "theorem toCoordinatelessSouriauFisherContext_state_eq" in block
    assert "theorem toCoordinatelessSouriauFisherContext_kms_state_eq" in block
    assert "C.toCoordinatelessSouriauFisherContext.kms.state =" in block
    assert "C.toCoordinatelessSouriauFisherContext.state :=" in block
