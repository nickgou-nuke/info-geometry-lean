from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
MODULE = REPO / "lean" / "InfoGeometry" / "Canonical" / "ChiralAction.lean"


def theorem_block(text: str, name: str) -> str:
    anchor = f"theorem {name}"
    start = text.index(anchor)
    tail = text[start:]
    end = tail.find("\n\ntheorem ")
    if end == -1:
        return tail
    return tail[:end]


def test_chiral_action_exposes_unit_relative_volume_bit_route() -> None:
    text = MODULE.read_text(encoding="utf-8")

    assert "import InfoGeometry.Canonical.IncompressibleBitBridge" in text
    assert "theorem chiralDirac_eq_of_unitRelativeVolumeBit" in text

    block = theorem_block(text, "chiralDirac_eq_of_unitRelativeVolumeBit")
    assert "UnitRelativeVolumeBit" in block
    assert "hUnitVolume :" not in block
    assert "isNormalInference_of_unitRelativeVolumeBit" in block
