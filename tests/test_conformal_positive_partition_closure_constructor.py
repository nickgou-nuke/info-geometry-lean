from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauConformalKKTContext.lean"


def test_conformal_positive_partition_witness_has_direct_closure_constructor():
    text = SOURCE.read_text()

    assert "namespace ConformalPositivePartitionWitness" in text
    assert "noncomputable def toOperatorAdmissibilityWitness" in text
    assert "noncomputable def toClosureContext" in text
    assert "partitionWitness := W" in text
    assert "without re-supplying a separate `hOperatorAdmissible` packet" in text
