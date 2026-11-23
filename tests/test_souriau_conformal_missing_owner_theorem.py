from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"
WEYL_KKT = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylKKTAnomalyIdentity.lean"


def test_souriau_equilibrium_forces_chiral_scale_zero_owner_theorem_exists() -> None:
    souriau_text = SOURIAU.read_text(encoding="utf-8")
    weyl_text = WEYL_KKT.read_text(encoding="utf-8")

    assert "theorem isThermodynamicReadoutStationary_of_equilibriumSeed" in souriau_text
    assert (
        "theorem semanticCollapsePacket_of_equilibriumSeed_of_stationaryScaleZeroWitness_of_structuredProjectorHypotheses"
        in weyl_text
    )
