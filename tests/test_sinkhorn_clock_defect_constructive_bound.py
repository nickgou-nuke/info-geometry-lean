from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SINKHORN = REPO / "lean" / "InfoGeometry" / "LLM" / "SinkhornDefectFlow.lean"


def test_detailed_equilibrium_uses_theorem_backed_clock_defect_bound() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "theorem nonEquilibriumClockDefect_norm_le_ZD_of_detailedEquilibrium" in text
    assert "noncomputable def ofDetailedEquilibrium" in text
    assert "theorem ofDetailedEquilibrium_routerResidual" in text
    assert "theorem ofDetailedEquilibrium_δ_odd_eq_zero" in text
    assert "theorem ofDetailedEquilibrium_isRouterEquilibrium" in text
    assert "nonEquilibriumClockDefect_norm_le_ZD_of_detailedEquilibrium (E := E)" in text
    assert "ofDetailedEquilibrium (E := E) CIK flow hMod hEq" in text
