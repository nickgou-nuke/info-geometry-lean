from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
WINDING = REPO / "lean" / "InfoGeometry" / "Canonical" / "WindingOrbitClosure.lean"


def test_has_clock_axis_forcing_seed_routes_through_cartan_grade_owner() -> None:
    text = WINDING.read_text(encoding="utf-8")

    assert "def HasClockAxisForcingSeed (hMod : EndH) : Prop :=" in text
    assert "HasCartanGradeForcingSeed (H := H) hMod" in text
    assert "exact modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium" in text
    assert "exact winding_orbit_periodicity_of_detailedEquilibrium" in text
    assert "theorem right_comp_clockAxis_eq_zero_iff" in text
    assert "theorem nonEquilibriumClockDefect_eq_zero_iff_detailedEquilibrium" in text
    assert "theorem nonEquilibriumClockDefect_eq_zero_of_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry" in text
    assert "theorem nonEquilibriumClockDefect_eq_zero_iff_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry" in text
    assert "show IsClockEquilibriumLane (H := H) hMod ↔" in text
    assert "exact clockEquilibrium_iff_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry" in text
    assert "theorem noncommutingScaleLane_iff_not_detailedEquilibrium" in text
