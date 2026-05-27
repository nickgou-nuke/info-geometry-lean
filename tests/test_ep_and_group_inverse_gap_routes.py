from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
MODULE = REPO / "lean" / "InfoGeometry" / "Canonical" / "EPAndGroupInverse.lean"


def test_inverse_kernel_gap_routes_exist() -> None:
    text = MODULE.read_text(encoding="utf-8")

    assert "theorem mpRangeProjector_eq_metricProjector_of_dilationGap_eq_zero" in text
    assert "theorem rightProjectorMismatch_eq_projectorMismatch_of_dilationGap_eq_zero" in text
    assert "IK.isEP_of_dilationGap_eq_zero hGap" in text


def test_certified_inverse_kernel_gap_routes_exist() -> None:
    text = MODULE.read_text(encoding="utf-8")

    assert "theorem mpRangeProjector_eq_metricProjector_of_dilationGap_eq_zero" in text
    assert "theorem rightProjectorMismatch_eq_projectorMismatch_of_dilationGap_eq_zero" in text
    assert "CIK.isEP_of_dilationGap_eq_zero hGap" in text
