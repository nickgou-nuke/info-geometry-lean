from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean"


def read_source() -> str:
    return SOURCE.read_text()


def test_smooth_legendre_gram_owner_replaces_explicit_fisher_positivity_packets():
    text = read_source()
    assert "structure SmoothLegendreGramOwner" in text
    start = text.index("structure SmoothLegendreGramOwner")
    end = text.index("namespace SmoothLegendreGramOwner", start)
    block = text[start:end]
    assert "legendre : LegendreHessianInverseContext Θ" in block
    assert "feature : Θ → Feature" in block
    assert "fisher_eq_gram" in block
    assert "feature_nonzero" in block
    assert "fisher_symmetric :" not in block
    assert "fisher_nonnegative :" not in block
    assert "fisher_positive_of_nonzero :" not in block


def test_smooth_legendre_gram_readout_derives_fisher_laws_and_packet():
    text = read_source()
    for name in [
        "toInfiniteCoadjointOrbitHessianContext",
        "constructive_packet",
        "ofSmoothLegendreGramReadout",
        "full_smooth_legendre_gram_constructive_theorem",
        "fisher_eq_gram",
        "feature_nonzero",
        "inner ℝ (feature X) (feature Y)",
        "real_inner_self_nonneg",
        "real_inner_self_pos",
    ]:
        assert name in text, f"missing constructive infinite Hessian owner declaration/evidence: {name}"


def test_log_partition_fisher_covariance_owner_replaces_log_and_covariance_packets():
    text = read_source()
    assert "structure LogPartitionFisherCovarianceOwner" in text
    start = text.index("structure LogPartitionFisherCovarianceOwner")
    end = text.index("namespace LogPartitionFisherCovarianceOwner", start)
    block = text[start:end]
    assert "partitionFunction : LieAlg → ℝ" in block
    assert "fisherHessian : LieAlg → Tangent → Tangent → ℝ" in block
    assert "massieu_eq_log_partition :" not in block
    assert "fisher_eq_covariance :" not in block


def test_log_partition_fisher_covariance_owner_derives_context_packet():
    text = read_source()
    for name in [
        "LogPartitionFisherCovarianceOwner.toInfiniteCoadjointOrbitHessianContext",
        "LogPartitionFisherCovarianceOwner.constructive_packet",
        "massieuPotential β = Real.log (partitionFunction β)",
        "fisherHessian β = momentCovariance β",
    ]:
        short = name.split(".")[-1]
        assert short in text, f"missing log/covariance owner evidence: {name}"


def test_hessian_module_builds_with_smooth_legendre_gram_owner():
    import subprocess

    result = subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    assert result.returncode == 0, result.stdout
