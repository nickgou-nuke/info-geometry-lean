from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeightedWeylNormalizationBridge.lean"


def test_phase_axis_equilibrium_theorem_exists() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    assert "theorem densityWeightLiftedReadout_phaseAxis_pair_eq_zero_of_equilibriumSeed" in text


def test_phase_axis_equilibrium_theorem_uses_reflexive_commutation() -> None:
    text = BRIDGE.read_text(encoding="utf-8")
    assert "Commute.refl" in text
    assert "densityWeightLiftedReadout_pair_eq_zero_of_equilibriumSeed_of_commute_phaseAxis" in text
