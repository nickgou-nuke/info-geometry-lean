from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"
BOHM = REPO / "lean" / "InfoGeometry" / "Canonical" / "BohmMadelungOperatorialBridge.lean"


def test_equilibrium_seed_constructs_thermodynamic_readout_stationarity() -> None:
    souriau_text = SOURIAU.read_text(encoding="utf-8")
    bohm_text = BOHM.read_text(encoding="utf-8")

    assert "theorem isThermodynamicReadoutStationary_of_equilibriumSeed" in souriau_text
    assert "isThermodynamicReadoutStationary_of_equilibriumSeed" in bohm_text
