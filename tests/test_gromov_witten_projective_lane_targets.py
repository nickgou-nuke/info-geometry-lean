from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
LANE = REPO / "lean" / "InfoGeometry" / "GromovWittenProjectiveLane.lean"


def test_gw_and_quantum_projective_lane_targets_match_current_surface() -> None:
    text = LANE.read_text(encoding="utf-8")

    assert "def GWVirtualLocalizationPacketTarget (_P : GWVirtualLocalizationPacket) : Prop :=" in text
    assert "def QuantumMetricOperatorPacketTarget (_P : QuantumMetricOperatorPacket) : Prop :=" in text
    assert "def ErlangenLanglandsGromovLaneTarget" in text
    assert "theorem constructErlangenLanglandsGromovLaneTarget" in text
    assert "theorem constructErlangenLanglandsGWFromPacket" in text
