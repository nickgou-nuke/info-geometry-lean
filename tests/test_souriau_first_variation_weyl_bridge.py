from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"
WEYL = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylKKTAnomalyIdentity.lean"


def test_souriau_first_variation_bridge_is_theorem_backed() -> None:
    souriau_text = SOURIAU.read_text(encoding="utf-8")
    weyl_text = WEYL.read_text(encoding="utf-8")

    assert "theorem equilibriumSeed_of_probeFaithful_of_firstVariation_eq_zero" in souriau_text
    assert "theorem isThermodynamicReadoutStationary_of_firstVariation_eq_zero_of_probeFaithful" in souriau_text
    assert (
        "theorem semanticCollapsePacket_of_firstVariation_eq_zero_of_probeFaithful"
        in weyl_text
    )
