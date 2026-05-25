from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def _namespace_block(text: str, name: str) -> str:
    start = text.index(f"namespace {name}")
    tail = text[start:]
    end = tail.index(f"end {name}")
    return tail[:end]


def test_observable_minimal_branch_exports_identity_sld_adapter() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    block = _namespace_block(text, "ObservableMinimalCyclicCoordinatelessSouriauContext")

    assert "def toMinimalCyclicCoordinatelessSouriauContext :" in block
    assert "MinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry Obs" in block
    assert "sld := fun A => A" in block
    assert "theorem toMinimalCyclicCoordinatelessSouriauContext_sld_eq_id" in block
    assert "C.toMinimalCyclicCoordinatelessSouriauContext.sld A = A" in block
