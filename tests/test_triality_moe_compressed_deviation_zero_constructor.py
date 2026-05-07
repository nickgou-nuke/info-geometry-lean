from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TRIALITY = REPO / "lean" / "InfoGeometry" / "LLM" / "TrialityMoE.lean"
OWNER = REPO / "lean" / "InfoGeometry" / "Canonical" / "ObserverDefect.lean"


def test_compressed_deviation_zero_route_is_theorem_backed() -> None:
    owner_text = OWNER.read_text(encoding="utf-8")
    triality_text = TRIALITY.read_text(encoding="utf-8")

    assert "theorem observerDefectResidual_eq_zero_of_compressedDeviation_eq_zero" in owner_text
    assert "theorem observerDefectResidual_norm_le_ZD_of_compressedDeviation_eq_zero" in owner_text
    assert "noncomputable def ofCompressedDeviationZeroObserver" in triality_text
    assert "theorem ofCompressedDeviationZeroObserver_routerResidual" in triality_text
    assert "observerDefectResidual_norm_le_ZD_of_compressedDeviation_eq_zero" in triality_text
