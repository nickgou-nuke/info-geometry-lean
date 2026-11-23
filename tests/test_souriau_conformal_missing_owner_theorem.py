from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"


def test_souriau_equilibrium_forces_chiral_scale_zero_owner_theorem_exists() -> None:
    text = SOURIAU.read_text(encoding="utf-8")

    assert (
        "theorem chiralScale_eq_zero_of_gibbsSouriauEquilibriumSeed" in text
    ), (
        "Missing owner theorem: thermodynamic/Souriau stationarity currently "
        "bridges to vanishing thermodynamic readout, and Weyl/KKT collapse "
        "is proved only after an explicit hScaleZero : CI.chiralScale = 0. "
        "The honest infinite-dimensional bridge still needs a theorem forcing "
        "CI.chiralScale = 0 from GibbsSouriauEquilibriumSeed data."
    )
