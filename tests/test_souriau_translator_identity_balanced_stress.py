from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauTheoremTranslatorPacket.lean"


def test_translator_threads_identity_balanced_stress_constructor() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "theorem claimF_superSouriauFermionGas_packet_ofIdentityBalancedStress" in text
    assert "WeylSupertraceFreeStressContext.ofIdentityBalanced" in text
    assert "claimF_superSouriauFermionGas_packet" in text
    assert "W.superTrace W.stress = 0" in text
    assert "W.weylInvariant" in text
