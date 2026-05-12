from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "HestenesPhaseSpectral.lean"


def test_hestenes_phase_spectral_exports_exist() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "theorem eigenvector_phaseAxis_of_hestenesLinear" in text
    assert "theorem eigenspace_phaseAxis_stable_of_hestenesLinear" in text
    assert "theorem commuting_antilinear_preserves_real_eigenspace" in text
    assert "theorem anticommuting_antilinear_flips_real_eigenvalue" in text