from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CONFORMAL = REPO / "lean" / "InfoGeometry" / "Canonical" / "ConformalAlgebra.lean"
HESTENES = REPO / "lean" / "InfoGeometry" / "Quantum" / "HestenesKahler.lean"
SUPERCHARGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SuperchargeCentralChargeClosure.lean"


def test_dilation_charge_response_mode_packet_exists() -> None:
    conformal_text = CONFORMAL.read_text(encoding="utf-8")
    hestenes_text = HESTENES.read_text(encoding="utf-8")
    supercharge_text = SUPERCHARGE.read_text(encoding="utf-8")

    assert "theorem D_in_weylDilation_of_cartan" in conformal_text
    assert "theorem weldedProjectorObstructionBerry_eq_zero_of_operatorialIncidence" in hestenes_text
    assert "theorem quasilatticeAnalyticalIndex_eq_operatorialCentralCharge_on_cpt_lane" in supercharge_text
    assert "theorem dilationChargeResponseMode_of_operatorialIncidence" in hestenes_text
    assert "CBA.IsWeylDilationPart CBA.D" in hestenes_text
    assert "weldedProjectorObstructionBerry (E := E) CCI = 0" in hestenes_text
    assert "operatorialCentralCharge (A := A) (B := B) (E := E) X hX" in hestenes_text
