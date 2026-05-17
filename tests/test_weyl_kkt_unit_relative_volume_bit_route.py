from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
MODULE = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylKKTAnomalyIdentity.lean"


def theorem_block(text: str, name: str) -> str:
    anchor = f"theorem {name}"
    start = text.index(anchor)
    tail = text[start:]
    end = tail.find("\n\n/--")
    if end == -1:
        end = tail.find("\n\ntheorem ")
    if end == -1:
        return tail
    return tail[:end]


def test_weyl_kkt_semantic_collapse_exposes_unit_relative_volume_bit_route() -> None:
    text = MODULE.read_text(encoding="utf-8")

    assert "import InfoGeometry.Canonical.IncompressibleBitBridge" in text
    assert (
        "theorem semanticCollapsePacket_of_unitRelativeVolumeBit_of_structuredProjectorHypotheses"
        in text
    )

    block = theorem_block(
        text,
        "semanticCollapsePacket_of_unitRelativeVolumeBit_of_structuredProjectorHypotheses",
    )
    assert "UnitRelativeVolumeBit" in block
    assert "hStationaryToScaleZero" not in block
    assert "chiralScale_eq_zero_of_unitRelativeVolumeBit" in block
