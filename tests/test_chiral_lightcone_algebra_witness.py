from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
OWNER = REPO / "lean" / "InfoGeometry" / "Canonical" / "Cl11PolarizedBasis.lean"


def test_chiral_lightcone_algebra_witness_is_theorem_backed() -> None:
    text = OWNER.read_text(encoding="utf-8")

    assert "structure ChiralLightConeAlgebraWitness" in text
    assert "def chiralLightConeAlgebraWitness" in text
    assert "uPlus_isGOne : IsGOne X (uPlus X A)" in text
    assert "uMinus_isGNegOne : IsGNegOne X (uMinus X B)" in text
    assert "uPlus_nilpotent : uPlus X A * uPlus X A = 0" in text
    assert "uMinus_nilpotent : uMinus X B * uMinus X B = 0" in text
    assert "mixed_commutator_isGZero" in text
    assert "commutator_uPlus_uMinus_isGZero (X := X) A B" in text
    assert "def doubledChiralLightConeAlgebraWitness" in text


def test_chiral_lightcone_packet_does_not_claim_global_partition_positivity() -> None:
    text = OWNER.read_text(encoding="utf-8")

    assert "global positive" in text
    assert "partition theorem" in text
    assert "ConformalPositivePartitionWitness" not in text
    assert "central_charge" not in text
    assert "Complex.exp" not in text
