from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauConformalKKTContext.lean"


def test_operatorial_weyl_character_and_supercharacter_are_source_owned() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "noncomputable def operatorWeylCharacter" in text
    assert "theorem operatorPartition_eq_operatorWeylCharacter" in text
    assert "structure OperatorialWeylSupercharacterContext" in text
    assert "readout_eq_bosonic_sub_fermionic" in text
    assert "noncomputable def ofFermionicCorrection" in text
    assert "noncomputable def ofPureBosonicReadout" in text
    assert "theorem operatorPartition_eq_operatorSupercharacter" in text
    assert "theorem operatorMassieu_eq_log_operatorSupercharacter" in text
    assert "theorem operatorPartition_eq_operatorSupercharacter_ofFermionicCorrection" in text
    assert "theorem operatorPartition_eq_operatorSupercharacter_ofPureBosonicReadout" in text
