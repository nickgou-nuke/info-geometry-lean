from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BOHM = REPO / "lean" / "InfoGeometry" / "Canonical" / "BohmMadelungOperatorialBridge.lean"
THERMO = REPO / "lean" / "InfoGeometry" / "Canonical" / "ThermodynamicGenerator.lean"


def test_bohm_stationary_k_split_uses_equilibrium_seed_theorem() -> None:
    bohm_text = BOHM.read_text(encoding="utf-8")
    thermo_text = THERMO.read_text(encoding="utf-8")

    assert "theorem potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_of_equilibriumSeed" in bohm_text
    assert "potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_equilibriumSeed" in bohm_text
    assert "theorem stateQGTReadout_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful" in thermo_text
    assert "admissibleTemperature_of_equilibriumSeed" not in bohm_text
    assert "isThermodynamicReadoutStationary_of_equilibriumSeed" in bohm_text
