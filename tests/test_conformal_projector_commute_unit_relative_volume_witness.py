from pathlib import Path
import re

SRC = Path("lean/InfoGeometry/Canonical/ConformalAnomalySource.lean").read_text()


def test_projector_commute_unit_relative_volume_witness_route_exists() -> None:
    assert "theorem projectors_commute_of_kahlerLogDet_unitRelativeVolumeWitness" in SRC
    assert re.search(
        r"theorem\s+projectors_commute_of_kahlerLogDet_unitRelativeVolumeWitness[\s\S]*?\(W : KahlerLogDetUnitRelativeVolumeWitness CI n M\)",
        SRC,
    )
    block_start = SRC.index(
        "theorem projectors_commute_of_kahlerLogDet_unitRelativeVolumeWitness"
    )
    block_tail = SRC[block_start:block_start + 500]
    assert "CI.projectors_commute_of_kahlerLogDet_unitRelativeVolume" in block_tail
    assert "hScaleFromKahler :" not in block_tail
    assert "hUnitVolume :" not in block_tail
