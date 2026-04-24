from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def test_cyclic_constructive_branch_removes_explicit_kms_packet() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure MinimalCyclicCoordinatelessSouriauContext" in text
    assert "def fisherMetric" in text
    assert "def weylGauge" in text
    assert "def toMinimalCyclicCoordinatelessSouriauContext" in text
    assert "structure ObservableMinimalCyclicCoordinatelessSouriauContext" in text
    assert "def fisherMetric" in text
    assert "def weylGauge" in text
    assert "def toObservableMinimalCyclicCoordinatelessSouriauContext" in text
    observable_block = text.split("structure ObservableMinimalCyclicCoordinatelessSouriauContext", 1)[1].split("namespace ObservableMinimalCyclicCoordinatelessSouriauContext", 1)[0]
    assert "kms : KMSState" not in observable_block
    assert "kms_state_eq" not in observable_block
    assert "fisherMetric : QuantumFisherSLDMetric" not in observable_block
    assert "weylGauge : WeylAlgebraGauge" not in observable_block
    assert "sld :" not in observable_block
    assert "theorem fisherMetric_sld_eq_id" in text
    assert "theorem kms_identity" in text
    assert "theorem coordinateless_constructive_packet" in text
    assert "def toCyclicCoordinatelessSouriauFisherContext" in text
    assert "def toCoordinatelessSouriauFisherContext" in text
