from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"


def test_souriau_conformal_equilibrium_seed_is_theorem_backed() -> None:
    text = SOURIAU.read_text(encoding="utf-8")

    assert "def AdmissibleTemperatureCone" in text
    assert "structure GibbsSouriauEquilibriumSeed" in text
    assert "theorem admissibleTemperature_of_equilibriumSeed" in text
    assert "theorem souriauEquilibrium_of_equilibriumSeed" in text
