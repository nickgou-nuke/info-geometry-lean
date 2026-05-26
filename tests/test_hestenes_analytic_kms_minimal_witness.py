from pathlib import Path


def test_hestenes_analytic_kms_minimal_witness_surface():
    path = Path("/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Krein/HestenesAnalyticKMSBridge.lean")
    text = path.read_text()

    assert "structure MinimalHestenesAnalyticKMSWitness where" in text
    assert "namespace MinimalHestenesAnalyticKMSWitness" in text
    namespace_block = text.split("namespace MinimalHestenesAnalyticKMSWitness", 1)[1].split(
        "end MinimalHestenesAnalyticKMSWitness", 1
    )[0]
    assert "def toBridge" in namespace_block
    assert "theorem toBridge_state_eq" in namespace_block
    assert "theorem toBridge_flow_invariant" in namespace_block
    assert "theorem toBridge_kms_boundary_condition" in namespace_block

    structure_block = text.split("structure MinimalHestenesAnalyticKMSWitness where", 1)[1].split(
        "namespace MinimalHestenesAnalyticKMSWitness", 1
    )[0]
    assert "flow_invariant" not in structure_block
    assert "kms_boundary_condition" not in structure_block
    assert "kms_boundary_condition_holds" not in structure_block
