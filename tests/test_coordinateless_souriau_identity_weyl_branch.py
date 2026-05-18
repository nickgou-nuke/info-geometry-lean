from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def _structure_block(text: str, name: str) -> str:
    start = text.index(f"structure {name}")
    tail = text[start:]
    next_structure = tail.find("\nstructure ", 1)
    next_namespace = tail.find("\nnamespace ", 1)
    ends = [idx for idx in (next_structure, next_namespace) if idx != -1]
    end = min(ends) if ends else len(tail)
    return tail[:end]


def test_identity_weyl_constructive_branch_removes_explicit_weyl_packet() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    block = _structure_block(text, "MinimalIdentityWeylCoordinatelessSouriauContext")

    assert "def identityWeylAlgebraGauge" in text
    assert "structure MinimalIdentityWeylCoordinatelessSouriauContext" in text
    assert "kms : KMSState" in block
    assert "fisherMetric : QuantumFisherSLDMetric" in block
    assert "weylGauge : WeylAlgebraGauge" not in block
    assert "def toFull" in text
    assert "theorem toFull_weylGauge_eq_identity" in text
