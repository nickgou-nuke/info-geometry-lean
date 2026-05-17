from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauTomitaModularFlowBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "Canonical" / "All.lean"


def test_souriau_tomita_modular_flow_bridge_is_source_owned() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure SouriauTomitaLogContext" in text
    assert "souriauMoment.thermalGenerator" in text
    assert "deltaLog : Obs" not in text
    assert "deltaLog_eq_thermalGenerator :\n    deltaLog =" not in text
    assert "def toRealModularLogData" in text
    assert "def souriauAdditiveModularFlow" in text
    assert "theorem tomita_deltaLog_eq_thermalGenerator" in text
    assert "theorem tomita_flow_eq_souriau_modularTransportFlow" in text
    assert "theorem souriauAdditiveModularFlow_apply_eq_modular_shift" in text
    assert "theorem souriauModularGenerator_eq_moment_geometricTemperature" in text
    assert "def modularHamiltonian" in text
    assert "theorem modularHamiltonian_eq_moment_geometricTemperature" in text
    assert "structure SouriauTomitaKMSContext" in text
    assert "structure MinimalSouriauTomitaKMSContext" in text
    minimal_block = text.split("structure MinimalSouriauTomitaKMSContext", 1)[1].split("namespace MinimalSouriauTomitaKMSContext", 1)[0]
    assert " state : AlgebraicState" not in minimal_block
    assert "kms_state_eq" not in minimal_block
    assert "def toMinimalSouriauTomitaKMSContext" in text
    assert "theorem toMinimalSouriauTomitaKMSContext_state_eq" in text
    assert "kms := C.kms" in text
    assert "def state" in text
    assert "theorem mk_of_kms" in text
    assert "def toSouriauTomitaKMSContext" in text
    assert "theorem toSouriauTomitaKMSContext_state_eq" in text
    assert "state := C.kms.state" in text
    assert "kms_state_eq := rfl" in text
    assert "theorem mk_of_state_kms" in text
    assert "theorem kms_eval_mul_souriau_modular_eq_eval_flip" in text
    assert "theorem sigma_add" in text
    assert "theorem sigma_zero" in text



def test_souriau_tomita_bridge_exposes_cyclic_standard_form_kms_owner_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure CyclicSouriauTomitaKMSContext" in text
    assert "def zeroThermalSouriauMoment" in text
    assert "def SouriauTomitaLogContext.ofZeroThermalMoment" in text
    assert "modularHamiltonian_zero" in text
    assert "modularHamiltonian_zero : logContext.modularHamiltonian = 0" not in text
    assert "theorem sigma_apply_eq_self" in text
    assert "theorem toStandardFormCarrier_Delta_eq_zero" in text
    assert "theorem toStandardFormCarrier_modularFlow_apply_eq_self" in text
    assert "theorem kms_eval_mul_souriau_modular_eq_eval_flip" in text
    assert "theorem constructive_kms_packet" in text



def test_souriau_tomita_bridge_exposes_standard_form_owner_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "import InfoGeometry.Canonical.StandardFormCore" in text
    assert "def toStandardFormSeed" in text
    assert "def toStandardFormCarrier" in text
    assert "theorem toStandardFormCarrier_Delta_eq_modularHamiltonian" in text
    assert "theorem toStandardFormCarrier_modularFlow_apply" in text
    assert "theorem tomita_flow_eq_souriau_modularTransportFlow" in text


def test_souriau_tomita_bridge_is_in_canonical_umbrella() -> None:
    text = ALL.read_text(encoding="utf-8")

    assert "import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge" in text
