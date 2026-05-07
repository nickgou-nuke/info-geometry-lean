from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauConformalKKTContext.lean"


def test_selfdual_chiral_lightcone_partition_witness_surface():
    text = SOURCE.read_text()

    assert "structure SelfDualChiralLightConeCertificate" in text
    assert "theorem uPlus_mem_chiralCone" in text
    assert "theorem uMinus_mem_chiralCone" in text
    assert "theorem spectralCommutator_mem_spectralCompact" in text
    assert "theorem circularCommutator_isGZero" in text
    assert "structure ConformalCartanOddPartitionWitness" in text
    assert "theorem partitionFloor_pos" in text
    assert "def toPositivePartitionWitness" in text
    assert "theorem operatorAdmissible_of_cartanOddPartition" in text
    assert "def toOperatorAdmissibilityWitness" in text
    assert "def toClosureContext" in text
