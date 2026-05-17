from pathlib import Path

FILE = Path("lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean")


def test_unit_relative_volume_bit_route_exists_for_flat_holonomy_collapse():
    text = FILE.read_text()
    assert "import InfoGeometry.Canonical.IncompressibleBitBridge" in text
    anchor = "theorem holonomy_eq_zero_of_flat_of_unitRelativeVolumeBit"
    assert anchor in text
    block = text[text.index(anchor): text.index("theorem holonomy_pos_of_flat_of_noncommute")]
    assert "(bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M)" in block
    assert "hUnitVolume" not in block
    assert "holonomy_eq_zero_of_flat_of_unitRelativeVolume" in block
    assert "bit.unit_relative_volume" in block
