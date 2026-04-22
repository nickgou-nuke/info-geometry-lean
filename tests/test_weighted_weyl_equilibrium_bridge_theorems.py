from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeightedWeylNormalizationBridge.lean"


def test_equilibrium_seed_now_forces_weighted_density_readout_to_pure_phase_axis_response() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    assert "theorem densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed" in text
