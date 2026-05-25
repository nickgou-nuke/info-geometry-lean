from pathlib import Path


LEAN = Path("lean/InfoGeometry/Canonical/NormalSemisimpleAgreement.lean")


def test_normal_semisimple_no_projector_anomaly_routes_exist():
    text = LEAN.read_text()
    assert "namespace ConstructiveNormalSemisimpleAgreementWitness" in text
    assert "theorem no_projector_anomaly" in text
    assert "theorem normalSemisimple_no_projector_anomaly" in text
    assert "theorem normalSemisimple_no_projector_anomaly_of_constructive" in text
    assert "ProjectorPair.hasProjectorAnomaly_iff_hasMismatch" in text
    assert "hMismatch W.no_mismatch" in text
