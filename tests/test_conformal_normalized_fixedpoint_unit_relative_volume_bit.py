from pathlib import Path
import re

SRC = Path("lean/InfoGeometry/Canonical/ConformalAnomalySource.lean").read_text()


def test_fixedpoint_unit_relative_volume_bit_route_exists():
    assert "theorem projectors_commute_of_kahlerLogDet_normalized_fixedpoint_unitRelativeVolumeBit" in SRC
    assert re.search(
        r"theorem\s+projectors_commute_of_kahlerLogDet_normalized_fixedpoint_unitRelativeVolumeBit[\s\S]*?\(bit : UnitRelativeVolumeWitness n M\)",
        SRC,
    )
    assert "CI.anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized_unitRelativeVolumeBit" in SRC
