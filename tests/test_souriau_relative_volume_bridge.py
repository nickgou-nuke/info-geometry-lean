from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"


def test_equilibrium_seed_should_force_unit_relative_volume_owner_theorem() -> None:
    text = SOURIAU.read_text(encoding="utf-8")

    assert (
        "theorem relativeVolumeChangeRN_eq_one_of_gibbsSouriauEquilibriumSeed" in text
    ), (
        "Missing owner bridge: the SCC/owner audit shows the Souriau equilibrium, "
        "operatorial Cramer-Rao, and conformal zero-scale corridors lie in the same weak basin, "
        "but there is still no raw owner theorem forcing unit relative volume "
        "relativeVolumeChangeRN = 1 from GibbsSouriauEquilibriumSeed data."
    )
