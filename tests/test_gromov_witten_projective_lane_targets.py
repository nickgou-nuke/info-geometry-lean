from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
LANE = REPO / "lean" / "InfoGeometry" / "GromovWittenProjectiveLane.lean"


def test_gw_and_quantum_projective_lane_targets_are_nonvacuous() -> None:
    text = LANE.read_text(encoding="utf-8")

    assert "def GWVirtualLocalizationPacketTarget (P : GWVirtualLocalizationPacket) : Prop :=" in text
    assert "Nonempty (P.FixedLocus → P.Moduli)" in text
    assert "Nonempty (P.FixedLocus → P.VirtualClass)" in text
    assert "Nonempty (P.FixedLocus → P.VirtualNormal)" in text
    assert "Nonempty (P.FixedLocus → P.EulerDenominator)" in text
    assert "Nonempty (P.FixedLocus → P.localizedContribution)" in text
    assert "theorem of_fixed_locus_data" in text

    assert "def QuantumMetricOperatorPacketTarget (P : QuantumMetricOperatorPacket) : Prop :=" in text
    assert "Nonempty (P.Algebra → P.LipNorm)" in text
    assert "Nonempty (P.StateSpace → P.StateSpace → P.quantumDistance)" in text
    assert "P.convergenceWitness" in text
    assert "theorem of_metric_data" in text
