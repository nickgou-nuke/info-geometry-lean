from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
ONSAGER = REPO / "lean" / "InfoGeometry" / "Canonical" / "OnsagerReciprocity.lean"


def test_onsager_stationary_uses_equilibrium_seed_theorem() -> None:
    text = ONSAGER.read_text(encoding="utf-8")

    assert "theorem toRelationalInformationDatum_bohmMadelung_stationary_of_equilibriumSeed" in text
    assert (
        "admissibleTemperature_of_equilibriumSeed" in text
        or "potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_equilibriumSeed" in text
    )
