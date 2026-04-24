from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean"


def test_square_dissipation_translator_branch_exists():
    text = SOURCE.read_text()

    assert "claimM_coadjointLeaf_Casimir_transverseOnsager_square_packet" in text
    assert "ofMomentImageSquareDissipation" in text
    assert "casimir_leaf_transverse_onsager_square_packet" in text


def test_square_dissipation_branch_removes_general_context_argument():
    text = SOURCE.read_text()
    start = text.index("theorem claimM_coadjointLeaf_Casimir_transverseOnsager_square_packet")
    block = text[start : text.index("/--\nLiterature-facing finite", start)]

    assert "C : InfiniteCoadjointOrbitMetriplecticContext" not in block
    assert "dissipationAmplitude : Orbit → ℝ" in block
    assert "0 ≤ C.metricEntropyRate x" in block
    assert "0 ≤ C.totalEntropyRate x" in block


def test_square_dissipation_branch_has_no_fake_proof_stubs():
    text = SOURCE.read_text()
    start = text.index("theorem claimM_coadjointLeaf_Casimir_transverseOnsager_square_packet")
    block = text[start : text.index("/--\nLiterature-facing finite", start)]

    forbidden = ["sorry", "admit", "axiom ", "postulate"]
    for needle in forbidden:
        assert needle not in block
