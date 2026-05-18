from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauTheoremTranslatorPacket.lean"


def test_translator_has_exact_residual_kkt_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "theorem structuredSouriauKKTTranslatorPacket_ofExactResiduals" in text
    assert "theorem structuredSouriauKKTTranslatorPacket_ofExactResiduals_det_nonneg" in text
    assert "DimensionAgnosticKKTResiduals.exact.toShadow" in text
    assert "DimensionAgnosticKKTResiduals.exact_stationarity_packet" in text
    assert "structuredSouriauTranslatorPacket_of_det_nonneg" in text


def test_exact_residual_route_does_not_reintroduce_explicit_kkt_hypotheses() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    theorem = text.split("theorem structuredSouriauKKTTranslatorPacket_ofExactResiduals", 1)[1]
    theorem = theorem.split("/--\nStage-2 theorem packet", 1)[0]

    assert "hCone" not in theorem
    assert "hStationarity" not in theorem
    assert "hSlack" not in theorem
    assert "hFinite" not in theorem


def test_exact_residual_det_route_uses_no_bare_psd_packet() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    theorem = text.split("theorem structuredSouriauKKTTranslatorPacket_ofExactResiduals_det_nonneg", 1)[1]
    theorem = theorem.split("/--\nStage-2 theorem packet", 1)[0]

    assert "hPSD" not in theorem
    assert "PositiveSemidefinite" not in theorem
    assert "hdet" in theorem


def test_claimK_has_exact_residual_constructive_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "theorem claimK_kktEntropyStationarity_packet_ofExactResiduals" in text
    theorem = text.split("theorem claimK_kktEntropyStationarity_packet_ofExactResiduals", 1)[1]
    theorem = theorem.split("/--\nClaim W:", 1)[0]

    assert "DimensionAgnosticKKTResiduals.exact_stationarity_packet" in theorem
    assert "hCone" not in theorem
    assert "hStationarity" not in theorem
    assert "hSlack" not in theorem
    assert "hFinite" not in theorem
