from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
CIK = REPO / "lean" / "InfoGeometry" / "Canonical" / "CertifiedInverseKernel.lean"


def test_selfadjoint_spectral_projector_requires_both_base_and_drazin_selfadjoint() -> None:
    text = CIK.read_text(encoding="utf-8")

    assert "theorem spectralProjector_star_of_selfAdjoint" in text
    assert "(hA : star CIK.A = CIK.A)" in text
    assert "(hAD : star CIK.A_D = CIK.A_D)" in text
    assert "theorem spectralProjector_isSelfAdjoint_of_selfAdjoint" in text
    assert "CIK.spectralProjector_star_of_selfAdjoint hA hAD" in text


def test_selfadjoint_adapters_from_IsSelfAdjoint_are_present() -> None:
    text = CIK.read_text(encoding="utf-8")

    assert "theorem spectralProjector_star_of_isSelfAdjoint" in text
    assert "hA.star_eq" in text
    assert "hAD.star_eq" in text
    assert "theorem spectralProjector_isSelfAdjoint_of_isSelfAdjoint" in text
