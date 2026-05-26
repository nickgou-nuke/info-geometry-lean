from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
OBSERVER_DEFECT = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_control_nonempty_bridge_theorems_exist() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "theorem observerDeviationControlledByZD_iff_nonempty_control" in text
    assert "theorem nonempty_observerDeviationControl_of_deviationControlledByZD" in text
    assert "theorem observerDeviationControlledByZD_of_nonempty_control" in text


def test_control_nonempty_bridge_uses_explicit_witness_packet() -> None:
    text = OBSERVER_DEFECT.read_text(encoding="utf-8")

    assert "ObserverDeviationControlledByZD CIK obs ↔ Nonempty (ObserverDeviationControl CIK obs)" in text
    assert "observerDeviationControlledByZD_iff_nonempty_control" in text
    assert "ObserverDeviationControlledByZD.of_control c" in text
