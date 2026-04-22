from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauConformalKKTContext.lean"


def test_conformal_fisher_square_response_constructs_nonnegativity() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure ConformalSquareFisherOnsagerPositiveContext" in text
    assert "selfResponse_eq_square" in text
    assert "theorem selfResponse_nonneg" in text
    assert "def toPositiveContext" in text
    assert "theorem fisherOnsagerProduction_nonneg_of_squareResponse" in text
    assert "sq_nonneg" in text
