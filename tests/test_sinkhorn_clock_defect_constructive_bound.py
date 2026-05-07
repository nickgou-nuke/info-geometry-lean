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


def test_router_equilibrium_chain_reaches_mathlib_norm_and_clock_defect_roots() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "theorem δ_odd_eq_zero_iff_routerResidual_eq_zero" in text
    assert "δ_odd B = 0 ↔ B.routerResidual = 0" in text
    assert "ContinuousLinearMap.opNorm_zero_iff" in text
    assert "theorem router_equilibrium_iff_clockDefect_eq_zero" in text
    assert "IsRouterEquilibrium B.bound ↔" in text
    assert "InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) B.hMod = 0" in text
    assert "δ_odd_eq_zero_iff_routerResidual_eq_zero" in text
    assert "B.residual_eq_clockDefect" in text
    assert "theorem router_equilibrium_iff_detailedEquilibrium" in text
    assert "nonEquilibriumClockDefect_eq_zero_iff_detailedEquilibrium" in text


def test_zero_residual_constructs_real_monotone_sinkhorn_step() -> None:
    text = SINKHORN.read_text(encoding="utf-8")

    assert "def SinkhornDefectStep.of_routerResidual_eq_zero" in text
    assert "hNext : next.routerResidual = 0" in text
    assert "ContinuousLinearMap.opNorm_zero" in text
    assert "norm_nonneg B.routerResidual" in text
    assert "theorem sourcedGenerator_deviation_next_le_of_routerResidual_eq_zero" in text
