from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
MODULE = REPO / "lean" / "InfoGeometry" / "Canonical" / "GrandSynthesisGeometry.lean"


def test_grand_synthesis_geometry_exposes_unit_relative_volume_bit_routes() -> None:
    text = MODULE.read_text(encoding="utf-8")

    assert "import InfoGeometry.Canonical.IncompressibleBitBridge" in text
    assert "theorem vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolumeBit" in text
    assert "theorem gravity_generated_by_rnEntropy_of_unitRelativeVolumeBit" in text
    assert "(bit : UnitRelativeVolumeBit n M)" in text
    assert "bit.unit_relative_volume" in text
    assert "unitRelativeVolumeBit_of_eq_one hUnit" in text
