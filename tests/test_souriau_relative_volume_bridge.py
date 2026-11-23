from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BIT_BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "IncompressibleBitBridge.lean"


def test_equilibrium_seed_should_force_unit_relative_volume_owner_theorem() -> None:
    text = BIT_BRIDGE.read_text(encoding="utf-8")

    assert "theorem relativeVolumeChangeRN_eq_one_of_unitRelativeVolumeBit" in text
    assert "theorem chiralScale_eq_zero_of_unitRelativeVolumeBit" in text
