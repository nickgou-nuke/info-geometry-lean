from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "Spin44CharacterShadow.lean"


def test_spin44_character_shadow_is_explicitly_finite_shadow() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "Spin(4,4) Character Shadow" in text
    assert "finite D4 weight-sum shadow" in text
    assert "does not construct `Spin(4,4)`" in text
    assert "Dixmier trace" in text
    assert "Drazin-core Witten" in text


def test_spin44_character_shadow_exposes_weight_sum_formulas() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "def vectorCharacter" in text
    assert "theorem vectorCharacter_eq_two_sum_cosh" in text
    assert "def spinorEvenCharacter" in text
    assert "def spinorOddCharacter" in text
    assert "def vectorMinusDiracSupertraceShadow" in text
    assert "theorem vectorMinusDiracSupertraceShadow_eq" in text
    assert "theorem evenMinus_card" in text
    assert "theorem oddMinus_card" in text
