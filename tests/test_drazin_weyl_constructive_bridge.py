from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "DrazinWeylConstructive.lean"


def test_constructive_riesz_weyl_bridge_exports_classical_and_infinite_wrappers() -> None:
    text = BRIDGE.read_text(encoding="utf-8")

    assert "def constructiveRieszWeylData_of_hasClassicalRieszDecompositionAtZero" in text
    assert "def constructiveRieszWeylData_of_drazinInfiniteAssumptions" in text
    assert "theorem exists_isDrazinInverse_isWeylCompatible_of_hasClassicalRieszDecompositionAtZero" in text
    assert "theorem exists_isDrazinInverse_isWeylCompatible_of_drazinInfiniteAssumptions" in text
    assert "exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData" in text
