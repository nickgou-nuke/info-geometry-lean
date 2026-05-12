from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "TypeIIIModularCantorSystem.lean"


def test_type_iii_modular_cantor_system_mathlib_rooted_surface() -> None:
    text = FILE.read_text(encoding="utf-8")

    required = [
        "theorem closedCylinder_split",
        "theorem theta_sq",
        "theorem diagonal_selfDual",
        "theorem antiDiagonal_antiSelfDual",
        "theorem rightAsLeft_leftAsRight",
        "theorem leftAsRight_rightAsLeft",
        "theorem rightCylinder_split_of_eq",
        "theorem cylinderPotential_child",
    ]

    for token in required:
        assert token in text


def test_type_iii_modular_cantor_system_blocks_pseudolaw_witnesses() -> None:
    text = FILE.read_text(encoding="utf-8")

    forbidden = [
        "selfDualConeClaim",
        "selfDualConeClaim_holds",
        "score_is_cocycle_log_derivative",
        "score_is_cocycle_log_derivative_holds",
        "semifinite_density_shadow",
        "semifinite_density_shadow_holds",
        "noCanonicalTraceClaim",
        "noCanonicalTraceClaim_holds",
        "determinantBarrierOnlyAfterRegularizationClaim",
        "determinantBarrierOnlyAfterRegularizationClaim_holds",
        "weight_split",
        "theorem rightCylinder_split (",
        "structure NaturalConePacket",
        "structure DyadicProjectionTree",
        "structure ModularTwinCantorTree",
        "structure FaithfulCylinderWeight",
        "structure CylinderRelativeWeight",
        "structure ModularLogDerivativePacket",
        "structure ModularCartanCantorSystem",
        "J_fixed_on_cone",
        "cylinder_projection",
        "weight_pos",
    ]

    for token in forbidden:
        assert token not in text
