from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CONFORMAL = REPO / "lean" / "InfoGeometry" / "Canonical" / "ConformalAnomalySource.lean"
BIT_BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "IncompressibleBitBridge.lean"


def test_equilibrium_seed_should_force_zero_unit_of_action_owner_theorem() -> None:
    conformal_text = CONFORMAL.read_text(encoding="utf-8")
    bit_text = BIT_BRIDGE.read_text(encoding="utf-8")

    assert "theorem unitOfAction_eq_chiralScale" in conformal_text
    assert "theorem unitOfAction_eq_zero_of_normalInference" in conformal_text
    assert "theorem unitOfAction_eq_zero_of_unitRelativeVolumeBit" in bit_text
