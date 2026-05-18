from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "CoordinatelessSouriauKMSBridge.lean"


def test_cyclic_constructive_branch_removes_explicit_kms_packet() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "structure MinimalCoordinatelessSouriauFisherContext" in text
    assert "def state : AlgebraicState" in text
    assert "theorem mk_of_kms" in text
    assert "def toMinimalCoordinatelessSouriauFisherContext" in text
    assert "def toCoordinatelessSouriauFisherContext" in text
    minimal_kms_block = text.split("structure MinimalCoordinatelessSouriauFisherContext", 1)[1].split("namespace MinimalCoordinatelessSouriauFisherContext", 1)[0]
    assert "state : AlgebraicState" not in minimal_kms_block
    assert "kms_state_eq" not in minimal_kms_block

    assert "structure MinimalCyclicCoordinatelessSouriauContext" in text
    assert "def fisherMetric" in text
    assert "def weylGauge" in text
    assert "def toMinimalCyclicCoordinatelessSouriauContext" in text
    assert "def toCyclicCoordinatelessSouriauFisherContext" in text
    assert "theorem toCyclicCoordinatelessSouriauFisherContext_fisherMetric_eq" in text
    assert "theorem toCyclicCoordinatelessSouriauFisherContext_weylGauge_eq" in text
    assert "theorem mk_minimal_of_cyclic" in text
    assert "theorem mk_broad_of_cyclic" in text
    minimal_block = text.split("structure MinimalCyclicCoordinatelessSouriauContext", 1)[1].split("namespace MinimalCyclicCoordinatelessSouriauContext", 1)[0]
    assert "fisherMetric : QuantumFisherSLDMetric" not in minimal_block
    assert "weylGauge : WeylAlgebraGauge" not in minimal_block
    assert "structure ObservableMinimalCyclicCoordinatelessSouriauContext" in text
    assert "def fisherMetric" in text
    assert "def weylGauge" in text
    assert "def toObservableMinimalCyclicCoordinatelessSouriauContext" in text
    observable_block = text.split("structure ObservableMinimalCyclicCoordinatelessSouriauContext", 1)[1].split("namespace ObservableMinimalCyclicCoordinatelessSouriauContext", 1)[0]
    assert "kms : KMSState" not in observable_block
    assert "kms_state_eq" not in observable_block
    assert "fisherMetric : QuantumFisherSLDMetric" not in observable_block
    assert "weylGauge : WeylAlgebraGauge" not in observable_block
    assert "sld :" not in observable_block
    assert "theorem fisherMetric_sld_eq_id" in text
    assert "theorem kms_identity" in text
    assert "theorem coordinateless_constructive_packet" in text
    assert "def toObservableCyclicCoordinatelessSouriauFisherContext :" in text
    assert "theorem toObservableCyclicCoordinatelessSouriauFisherContext_sigma_eq" in text
    assert "theorem toObservableCyclicCoordinatelessSouriauFisherContext_fisherMetric_eq" in text
    assert "theorem toObservableCyclicCoordinatelessSouriauFisherContext_weylGauge_eq" in text
    assert "def toObservableMinimalCoordinatelessSouriauFisherContext :" in text
    assert "def toObservableCoordinatelessSouriauFisherContext :" in text
    assert "theorem toObservableMinimalCoordinatelessSouriauFisherContext_sigma_eq" in text
    assert "theorem mk_observable_minimal_of_cyclic" in text
    assert "theorem toObservableCoordinatelessSouriauFisherContext_sigma_eq" in text
    assert "theorem mk_observable_broad_of_cyclic" in text
    assert "namespace ObservableCyclicCoordinatelessSouriauFisherContext" in text
    assert "def toIdentityKMSState" in text
    assert "theorem toIdentityKMSState_state_eq" in text
    assert "kms_identity := by" in text
    assert "namespace ObservableMinimalCyclicCoordinatelessSouriauContext" in text
    assert "ObservableCyclicCoordinatelessSouriauFisherContext.ofObservableMinimal (H := H) C" in text
    assert "C.toObservableCyclicCoordinatelessSouriauFisherContext.toIdentityKMSState" in text
    assert "theorem toObservableCyclicCoordinatelessSouriauFisherContext_toIdentityKMSState_state_eq" in text
    assert "def ofObservableMinimal" in text
    assert "theorem ofObservableMinimal_fisherMetric_eq" in text
    assert "theorem ofObservableMinimal_weylGauge_eq" in text
    assert "def toCyclicCoordinatelessSouriauFisherContext" in text
    assert "def toMinimalCoordinatelessSouriauFisherContext" in text
    assert "def toCoordinatelessSouriauFisherContext" in text
    assert "(ω.toMinimalCoordinatelessSouriauFisherContext beta J sld).toCoordinatelessSouriauFisherContext" in text
