from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "DensityWeightIntertwinerBridge.lean"


def test_zero_weight_density_readout_is_identified_with_comparison_readout() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    assert "theorem densityWeightLiftedReadout_zero_pair_eq_comparisonReadout_pair" in text


def test_equilibrium_seed_forces_zero_weight_density_readout_packet_to_vanish() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    assert "theorem densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed" in text
