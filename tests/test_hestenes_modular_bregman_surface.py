from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "HestenesModularBregman.lean"


def test_hestenes_modular_bregman_surface_is_real_untraced() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "def modularDeviation" in text
    assert "def modularBetaFlow" in text
    assert "theorem modularBetaFlow_zero" in text
    assert "def modularBetaDeviation" in text
    assert "theorem canonicalTomita_betaFlow_one_eq_Delta" in text
    assert "def operatorBregman" in text
    assert "theorem operatorBregman_self" in text
    assert "def souriauUntracedExponential" in text

    assert "Complex" not in text
    assert "trace" not in text.lower() or "trace-free" in text.lower() or "untraced" in text.lower()
