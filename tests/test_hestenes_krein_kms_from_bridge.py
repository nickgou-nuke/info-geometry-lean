from pathlib import Path


def test_hestenes_krein_kms_from_bridge_surface():
    path = Path("/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Krein/HestenesKreinNaturalConeBridge.lean")
    text = path.read_text()

    assert "def HestenesKreinNaturalConeKMSBridge.fromKMSBridge" in text
    assert "theorem HestenesKreinNaturalConeKMSBridge.fromKMSBridge_state_eq" in text
    assert "state := B.kms.state" in text
