from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"
WEYL = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylKKTAnomalyIdentity.lean"


def test_equilibrium_seed_bridge_to_zero_scale_semantic_packet_exists() -> None:
    souriau_text = SOURIAU.read_text(encoding="utf-8")
    weyl_text = WEYL.read_text(encoding="utf-8")

    theorem_anchor = (
        "theorem semanticCollapsePacket_of_equilibriumSeed_of_structuredProjectorHypotheses\n"
    )

    assert "theorem isThermodynamicReadoutStationary_of_equilibriumSeed" in souriau_text
    assert theorem_anchor in weyl_text
    assert "semanticCollapsePacket_of_structuredProjectorHypotheses_of_chiralScale_eq_zero" in weyl_text
    assert "isThermodynamicReadoutStationary_of_equilibriumSeed" in weyl_text
