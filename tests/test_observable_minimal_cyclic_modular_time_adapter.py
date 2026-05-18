from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def _observable_minimal_namespace_block(text: str) -> str:
    start = text.rindex("namespace ObservableMinimalCyclicCoordinatelessSouriauContext")
    tail = text[start:]
    end = tail.index("end ObservableMinimalCyclicCoordinatelessSouriauContext")
    return tail[:end]


def test_observable_minimal_cyclic_branch_exposes_modular_time_adapter() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    block = _observable_minimal_namespace_block(text)

    assert "def toModularTimeKMSContext :" in block
    assert "theorem toModularTimeKMSContext_sigma_eq" in block
    assert "theorem toModularTimeKMSContext_kms_eq" in block


def test_observable_minimal_cyclic_modular_time_adapter_uses_constructive_kms() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    block = _observable_minimal_namespace_block(text)

    assert "sigma := C.sigma" in block
    assert "kms := C.toIdentityKMSState" in block
    assert "This removes the remaining explicit `sigma` and `kms` packets" in block
