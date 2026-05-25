from pathlib import Path
import re

SRC = Path("lean/InfoGeometry/Canonical/ConformalAnomalySource.lean").read_text()


def test_logdet_mechanics_normal_inference_unit_relative_volume_bit_route_exists() -> None:
    assert "theorem isNormalInference_of_logDetBarrier_selfConcordance_mechanics_unitRelativeVolumeBit" in SRC
    assert re.search(
        r"theorem\s+isNormalInference_of_logDetBarrier_selfConcordance_mechanics_unitRelativeVolumeBit[\s\S]*?\(bit : UnitRelativeVolumeWitness n M\)",
        SRC,
    )
    block_start = SRC.index(
        "theorem isNormalInference_of_logDetBarrier_selfConcordance_mechanics_unitRelativeVolumeBit"
    )
    block_tail = SRC[block_start:block_start + 800]
    assert "logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolumeBit" in block_tail
    assert "hUnitVolume :" not in block_tail
