from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauConformalKKTContext.lean"


def test_conformal_operator_admissibility_has_constructive_partition_witness():
    text = SOURCE.read_text()

    assert "structure ConformalPositivePartitionWitness" in text
    assert "operatorPartition_eq_floor_add_square" in text
    assert "theorem operatorPartition_pos" in text
    assert "structure ConformalOperatorAdmissibilityWitness" in text
    assert "theorem operatorAdmissible" in text
    assert "def toClosureContext" in text
