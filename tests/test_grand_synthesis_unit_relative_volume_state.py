from pathlib import Path
import re


def test_grand_synthesis_adds_unit_relative_volume_state_route() -> None:
    path = Path("lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean")
    text = path.read_text()

    assert re.search(
        r"theorem gravity_generated_by_unitRelativeVolumeState\s*\n\s*\(Kgeo : KaehlerInformationGeometry X\)",
        text,
    )
    assert "exact gravity_generated_by_unitRelativeVolumeState" in text
    assert "(hUnitState : UnitRelativeVolumeState Kgeo)" in text


def test_grand_synthesis_adds_ricci_flat_unit_relative_volume_bit_route() -> None:
    path = Path("lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean")
    text = path.read_text()

    assert re.search(
        r"theorem isRicciFlat_of_rnEntropySource_of_unitRelativeVolumeBit\s*\n\s*\(Kgeo : KaehlerInformationGeometry X\)",
        text,
    )
    block_start = text.index("theorem isRicciFlat_of_rnEntropySource_of_unitRelativeVolumeBit")
    block_tail = text[block_start:block_start + 900]
    assert "unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolumeBit" in block_tail
    assert "(bit : UnitRelativeVolumeBit n M)" in block_tail
    assert "(hUnit : relativeVolumeChangeRN n M = 1)" not in block_tail
