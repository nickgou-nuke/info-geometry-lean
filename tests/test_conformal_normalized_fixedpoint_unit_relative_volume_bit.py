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


def test_normalized_anomaly_flow_unit_relative_volume_witness_route_exists():
    assert "theorem anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized_unitRelativeVolumeWitness" in SRC
    assert re.search(
        r"theorem\s+anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized_unitRelativeVolumeWitness[\s\S]*?\(W : KahlerLogDetUnitRelativeVolumeWitness CI n M\)",
        SRC,
    )
    assert "W.scale_from_kahler W.unit_relative_volume" in SRC


def test_fixedpoint_unit_relative_volume_witness_route_exists():
    assert "theorem projectors_commute_of_kahlerLogDet_normalized_fixedpoint_unitRelativeVolumeWitness" in SRC
    assert re.search(
        r"theorem\s+projectors_commute_of_kahlerLogDet_normalized_fixedpoint_unitRelativeVolumeWitness[\s\S]*?\(W : KahlerLogDetUnitRelativeVolumeWitness CI n M\)",
        SRC,
    )
    assert "CI.projectors_commute_of_kahlerLogDet_normalized_fixedpoint_unitRelativeVolumeBit" in SRC
    assert "W.scale_from_kahler W.unit_relative_volume" in SRC
