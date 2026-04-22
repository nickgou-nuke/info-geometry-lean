from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "OperatorPartitionSupervolumeBridge.lean"


def test_operatorial_partition_should_have_exact_supervolume_bridge_theorem() -> None:
    assert BRIDGE.exists(), (
        "Missing owner/bridge file: need an explicit theorem surface connecting the operatorial "
        "Souriau/Weyl partition lane to the super-volume language already present in the repo."
    )
    text = BRIDGE.read_text(encoding="utf-8")
    assert (
        "theorem operatorMassieu_eq_log_generalizedBerezinianScale_of_operatorPartition_eq_generalizedBerezinianScale"
        in text
    ), (
        "Missing exact bridge theorem: the repo has operatorPartition/operatorMassieu and "
        "generalizedBerezinianScale on separate lanes, but still lacks the theorem that turns "
        "an explicit partition-to-Berezinian witness into a Massieu/log-supervolume identity."
    )
