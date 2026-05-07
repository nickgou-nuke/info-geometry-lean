from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
THERMO = REPO / "lean" / "InfoGeometry" / "Canonical" / "ThermodynamicGenerator.lean"


def test_thermodynamic_generator_exposes_readout_pair_from_first_variation() -> None:
    text = THERMO.read_text(encoding="utf-8")

    assert "theorem comparisonReadout_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful" in text
    assert "theorem comparisonMetricReadout_eq_zero_of_firstVariation_eq_zero_of_probeFaithful" in text
    assert "theorem comparisonPhaseReadout_eq_zero_of_firstVariation_eq_zero_of_probeFaithful" in text
    assert "theorem isThermodynamicReadoutStationary_of_firstVariation_eq_zero_of_probeFaithful" in text
