from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def _structure_block(text: str, name: str) -> str:
    start = text.index(f"structure {name}")
    tail = text[start:]
    next_structure = tail.find("\nstructure ", 1)
    next_namespace = tail.find("\nnamespace ", 1)
    ends = [idx for idx in (next_structure, next_namespace) if idx != -1]
    end = min(ends) if ends else len(tail)
    return tail[:end]


def test_minimal_kms_moment_context_reduces_explicit_state_packet() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    block = _structure_block(text, "MinimalCoordinatelessSouriauKMSMomentContext")

    assert "structure MinimalCoordinatelessSouriauKMSMomentContext" in text
    assert "souriauMoment : OperatorSouriauMoment" in block
    assert "kms : KMSState" in block
    assert "state : AlgebraicState" not in block
    assert "kms_state_eq" not in block


def test_minimal_kms_moment_context_exposes_constructive_adapters() -> None:
    text = BRIDGE.read_text(encoding="utf-8")

    assert "def toModularTimeKMSContext" in text
    assert "theorem souriau_thermalGenerator_eq_moment" in text
    assert "theorem kms_identity" in text
