from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "KMSSinkhornSeedState.lean"


def test_structural_witness_surface_exists() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "structure ExpectationSeedStructuralWitness" in text
    assert "def ExpectationSeedStructuralWitness.ofPairwiseCommute" in text
    assert "theorem omegaSeed_kms_of_structuralWitness" in text
    assert "W.jointKernel" in text
    assert "W.commutatorOrthogonal" in text


def test_structural_witness_theorem_replaces_raw_hypotheses() -> None:
    text = FILE.read_text(encoding="utf-8")
    block = text.split("theorem omegaSeed_kms_of_structuralWitness", 1)[1].split("/--", 1)[0]

    assert "(W : ExpectationSeedStructuralWitness (F := F) K β)" in block
    assert "(hJointKernel : JointKernelOnOmega" not in block
    assert "(hCommOrthogonal : CommutatorOrthogonalOnOmega" not in block
    assert "(hΩ : Ω ≠ 0)" not in block
