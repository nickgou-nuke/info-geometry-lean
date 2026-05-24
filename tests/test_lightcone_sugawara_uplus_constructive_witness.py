from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TARGET = REPO / "lean" / "InfoGeometry" / "OperatorAlgebra" / "LightConeSugawaraCalibration.lean"


def test_lightcone_uplus_route_has_constructive_witness_variant() -> None:
    text = TARGET.read_text(encoding="utf-8")

    assert "structure UsesLightConeAffineBridgeWitness" in text
    assert "theorem usesLightConeAffineBridge_of_witness" in text
    assert "theorem sugawara_virasoro_acts_on_uPlusCurrent_of_witness" in text
    assert "(W : S.UsesLightConeAffineBridgeWitness)" in text
    assert "S.sugawara_virasoro_acts_on_uPlusCurrent (W.use) m n" in text
