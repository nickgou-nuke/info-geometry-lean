from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BOHM = REPO / "lean" / "InfoGeometry" / "Canonical" / "BohmMadelungOperatorialBridge.lean"
ONSAGER = REPO / "lean" / "InfoGeometry" / "Canonical" / "OnsagerReciprocity.lean"


def test_bohm_stateqgt_stationary_uses_equilibrium_seed_theorem() -> None:
    bohm_text = BOHM.read_text(encoding="utf-8")
    onsager_text = ONSAGER.read_text(encoding="utf-8")

    assert "theorem potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_equilibriumSeed" in bohm_text
    assert "potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_equilibriumSeed" in onsager_text
