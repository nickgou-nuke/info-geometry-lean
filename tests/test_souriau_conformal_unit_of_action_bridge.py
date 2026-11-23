from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURIAU = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauPlanckVector.lean"
CONFORMAL = REPO / "lean" / "InfoGeometry" / "Canonical" / "ConformalAnomalySource.lean"


def test_equilibrium_seed_should_force_zero_unit_of_action_owner_theorem() -> None:
    souriau_text = SOURIAU.read_text(encoding="utf-8")
    conformal_text = CONFORMAL.read_text(encoding="utf-8")

    assert "theorem unitOfAction_eq_chiralScale" in conformal_text
    assert "theorem unitOfAction_eq_zero_of_normalInference" in conformal_text
    assert (
        "theorem unitOfAction_eq_zero_of_gibbsSouriauEquilibriumSeed" in souriau_text
    ), (
        "Missing invariant-first owner theorem: the conformal lane already identifies "
        "unitOfAction with chiralScale and proves unitOfAction = 0 in the normal phase, "
        "but the thermodynamic/Souriau owner lane still lacks a theorem forcing "
        "unitOfAction = 0 from GibbsSouriauEquilibriumSeed data."
    )
