from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"


def test_rn_barrier_comparison_has_theorem_backed_budget_constructor() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "noncomputable def SinkhornRNBarrierThermodynamicComparison.ofResidualReadoutEqBarrier" in text
    assert "theorem SinkhornRNBarrierThermodynamicComparison.ofResidualReadoutEqBarrier_central_readout_budget" in text
    assert "δ_odd_thermo_le_ZD (E := E) B" in text
    assert "central_readout_budget := by" in text
