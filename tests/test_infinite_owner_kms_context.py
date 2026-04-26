from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean"


def read_source() -> str:
    return SOURCE.read_text()


def block_between(text: str, start: str, end: str) -> str:
    i = text.index(start)
    j = text.index(end, i)
    return text[i:j]


def test_cyclic_modular_time_context_replaces_explicit_kms_packet():
    text = read_source()
    block = block_between(
        text,
        "structure CyclicModularTimeKMSContext",
        "namespace CyclicModularTimeKMSContext",
    )
    assert "state : CyclicAlgebraicState" in block
    assert "beta : ℝ" in block
    assert "kms : KMSState" not in block
    assert "kms_state_eq" not in block


def test_cyclic_modular_time_context_derives_kms_and_modular_time():
    text = read_source()
    for name in [
        "CyclicModularTimeKMSContext.sigma",
        "CyclicModularTimeKMSContext.modular_time_add",
        "CyclicModularTimeKMSContext.modular_time_zero",
        "CyclicModularTimeKMSContext.kms_eval_mul_modular_eq_eval_flip",
        "CyclicAlgebraicState.toCyclicModularTimeKMSContext",
    ]:
        short = name.split(".")[-1]
        assert short in text, f"missing constructive infinite owner declaration: {name}"


def test_observable_cyclic_fisher_context_replaces_metric_gauge_sld_packets():
    text = read_source()
    block = block_between(
        text,
        "structure ObservableCyclicCoordinatelessSouriauFisherContext",
        "namespace ObservableCyclicCoordinatelessSouriauFisherContext",
    )
    assert "state : CyclicAlgebraicState" in block
    assert "beta : ℝ" in block
    assert "souriauMoment : OperatorSouriauMoment" in block
    assert "fisherMetric :" not in block
    assert "weylGauge :" not in block
    assert "sld :" not in block
    assert "KMSState" not in block


def test_observable_cyclic_fisher_context_derives_metric_gauge_and_packet():
    text = read_source()
    for name in [
        "ObservableCyclicCoordinatelessSouriauFisherContext.sigma",
        "ObservableCyclicCoordinatelessSouriauFisherContext.fisherMetric",
        "ObservableCyclicCoordinatelessSouriauFisherContext.weylGauge",
        "ObservableCyclicCoordinatelessSouriauFisherContext.fisherMetric_sld_eq_id",
        "ObservableCyclicCoordinatelessSouriauFisherContext.kms_identity",
        "ObservableCyclicCoordinatelessSouriauFisherContext.coordinateless_constructive_packet",
        "CyclicAlgebraicState.toObservableCyclicCoordinatelessSouriauFisherContext",
    ]:
        short = name.split(".")[-1]
        assert short in text, f"missing constructive observable Fisher owner declaration: {name}"


def test_module_builds_with_infinite_owner_kms_context():
    import subprocess

    result = subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=240,
    )
    assert result.returncode == 0, result.stdout
