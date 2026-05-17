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
