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
    # Guard owner-lane drift: forbid Complex-typed owner language and RCLike polymorphism.
    assert ": Complex" not in text
    assert "[RCLike" not in text
    assert "RCLike" not in text
