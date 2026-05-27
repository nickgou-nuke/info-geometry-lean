from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "BogoliubovTransport.lean"


def test_scale_zero_witness_derivation_exports_exist() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "theorem ModularScaleZeroWitness.modularDeriv_eq_modularGaugeDeriv" in text
    assert "theorem ModularScaleZeroWitness.modularDeriv_eq_zero_of_commute_gaugePart" in text
    assert "W.scalePart_eq_zero" in text
