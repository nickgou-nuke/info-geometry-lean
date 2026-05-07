from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
MAJORANA = REPO / "lean" / "InfoGeometry" / "Canonical" / "MajoranaKreinCartanSplit.lean"


def test_majorana_k_split_uses_equilibrium_seed_theorem() -> None:
    text = MAJORANA.read_text(encoding="utf-8")

    assert "theorem comparisonReadout_phasePart_eq_zero_of_equilibriumSeed" in text
    assert "comparisonReadout_pair_eq_zero_of_equilibriumSeed" in text
    assert (
        "theorem comparisonReadout_phasePart_eq_zero_of_firstVariation_eq_zero_of_probeFaithful"
        in text
    )
    assert (
        "isPotentialKillingOperator_of_firstVariation_eq_zero_of_probeFaithful"
        in text
    )
    assert "admissibleTemperature_of_equilibriumSeed" not in text
