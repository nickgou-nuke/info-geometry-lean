from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
THERMO = REPO / "lean" / "InfoGeometry" / "Canonical" / "ThermodynamicGenerator.lean"


def test_thermodynamic_generator_uses_first_variation_stationarity_theorems() -> None:
    text = THERMO.read_text(encoding="utf-8")

    assert "theorem isPotentialKillingOperator_of_firstVariation_eq_zero_of_probeFaithful" in text
    assert "theorem isThermodynamicReadoutStationary_of_firstVariation_eq_zero_of_probeFaithful" in text
