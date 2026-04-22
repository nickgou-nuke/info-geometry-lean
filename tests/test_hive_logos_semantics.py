from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
HIVE = REPO / "lean" / "InfoGeometry" / "Meta" / "HiveLogos.lean"


def test_hive_logos_defines_distinct_partial_and_strict_paths() -> None:
    text = HIVE.read_text(encoding="utf-8")

    assert 'elab "hive_try_const "' in text
    assert 'elab "hive_annihilate "' in text
    assert "applyRetrievedConst name false" in text
    assert "applyRetrievedConst name true" in text
    assert "[HIVE APPLIED]" in text
    assert "strict && !newGoals.isEmpty" in text
    assert "saved.restore" in text
    assert "applied but left {newGoals.length} subgoal(s)" in text


def test_hive_logos_indexes_declaration_conclusions_via_forall_telescope() -> None:
    text = HIVE.read_text(encoding="utf-8")

    assert "forallTelescopeReducing info.type" in text
    assert "conclusionHashShapeCanonical" in text
    assert "fullTypeHashShapeCanonical" in text
