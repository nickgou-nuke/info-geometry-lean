from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "HestenesPhaseSemilinear.lean"


def test_hestenes_phase_semilinear_surface_exists() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "inductive PhaseTwist" in text
    assert "def IsHestenesSemilinear" in text
    assert "theorem modular_j_isHestenesAntilinear" in text
    assert "theorem comp_isHestenesSemilinear" in text
    assert "theorem comp_antilinear_antilinear_isHestenesLinear" in text
    assert "theorem isHestenesSemilinear_linear_iff_KLinear" in text
    assert "theorem isHestenesSemilinear_antilinear_iff_KAntilinear" in text


def test_hestenes_phase_semilinear_has_no_complex_owner_language() -> None:
    text = FILE.read_text(encoding="utf-8")

    # Existing repo identifiers such as `complex_i` are allowed: they denote the
    # internal real doubled phase axis. The forbidden surface is an external
    # scalar-complex owner lane.
    forbidden = [
        "→L[ℂ]",
        "→ₗ[ℂ]",
        "InnerProductSpace ℂ",
        "NormedSpace ℂ",
        "Complex.",
        "RCLike",
        "SemilinearMap",
        "RingHomCompTriple",
        "starRingEnd ℂ",
        "Complex.conj",
    ]

    for token in forbidden:
        assert token not in text
