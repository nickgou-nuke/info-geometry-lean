from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean/InfoGeometry/Canonical/TheoryShadowRepresentation.lean"
ALL = ROOT / "lean/InfoGeometry/Canonical/All.lean"


def test_theory_shadow_representation_statuses_are_explicit():
    text = SOURCE.read_text()

    assert "structure TheoryShadowRepresentation" in text
    assert "spin44CharacterStatus := ShadowStatus.finiteShadow" in text
    assert "exactKKTResidualStatus := ShadowStatus.ownerOwned" in text
    assert "splitCl44TKKStatus := ShadowStatus.bridgeOwned" in text
    assert "drazinDixmierStatus := ShadowStatus.debt" in text
    assert "pfaffianWittenIndexStatus := ShadowStatus.debt" in text


def test_theory_shadow_representation_delegates_to_owned_surfaces():
    text = SOURCE.read_text()

    assert "vectorCharacter_eq_two_sum_cosh" in text
    assert "DimensionAgnosticKKTResiduals.exact_stationarity_packet" in text
    assert "structuredSouriauKKTTranslatorPacket_ofExactResiduals" in text
    assert "splitCl44_TKK_JordanLie_constructive_packet" in text


def test_theory_shadow_representation_has_no_fake_proof_stubs():
    text = SOURCE.read_text()

    forbidden = ["sorry", "admit", "axiom ", "postulate"]
    for needle in forbidden:
        assert needle not in text


def test_theory_shadow_representation_is_imported_by_all():
    text = ALL.read_text()

    assert "import InfoGeometry.Canonical.TheoryShadowRepresentation" in text
