from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "OnsagerReciprocity.lean"


def test_onsager_probe_faithful_first_variation_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure ProbeFaithfulFirstVariationZeroWitness" in text
    assert "theorem probeFaithful" in text
    assert "theorem firstVariation_eq_zero" in text
    assert (
        "theorem toRelationalInformationDatum_bohmMadelung_stationary_of_probeFaithfulFirstVariationZeroWitness"
        in text
    )
    assert "W.hFaithful W.hFirst" in text
