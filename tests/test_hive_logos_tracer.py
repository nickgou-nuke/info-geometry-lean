from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
HIVE = REPO / "lean" / "InfoGeometry" / "Meta" / "HiveLogos.lean"


def test_hive_logos_module_exposes_tracer_bullet_commands() -> None:
    text = HIVE.read_text(encoding="utf-8")

    assert "def canonicalizeShape" in text
    assert 'elab "hive_probe"' in text
    assert 'elab "#hive_index_decl "' in text
    assert 'elab "hive_try_const "' in text
    assert 'elab "hive_annihilate "' in text
    assert "[HIVE CLOSED]" in text
    assert "[HIVE APPLIED]" in text
    assert "[HIVE REFUSAL]" in text
