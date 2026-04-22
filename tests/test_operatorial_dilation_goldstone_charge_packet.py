from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauKreinMetriplecticContext.lean"


def test_operatorial_dilation_goldstone_charge_packet_surface():
    text = SOURCE.read_text()

    assert "theorem operatorialDilationGoldstoneCharge_packet" in text
    assert "densityWeightPhaseAxis_eq_dilationOperator" in text
    assert "densityWeightLiftedTransportGenerator_eq_souriau_add_weighted_dilation" in text
    assert "weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis" in text
    assert "cptSuperchargeOp_eq_dilationOperator" in text
    assert "parity_modular_supercharge_car_zero" in text
    assert "parity_modular_supercharge_ccrBracket_eq_two_cpt" in text
