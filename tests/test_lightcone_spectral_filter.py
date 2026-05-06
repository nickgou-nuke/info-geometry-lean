import json
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools" / "infra"))

from lightcone_spectral_filter import build_report, compute_drazin_from_schur


def test_compute_drazin_from_schur_keeps_off_diagonal_correction() -> None:
    a = np.array([[1.0, 1.0], [0.0, 0.0]])
    out = compute_drazin_from_schur(a)
    d = out["drazin"]
    assert d == pytest.approx(a)
    assert out["index"] == 1
    assert out["residuals"]["commutator_frobenius"] == pytest.approx(0.0, abs=1e-8)
    assert out["residuals"]["projector_idempotent_frobenius"] == pytest.approx(0.0, abs=1e-8)


def test_build_report_from_lean_graph_slice(tmp_path: Path) -> None:
    rows = [
        {"name": "A", "references": ["B", "C"]},
        {"name": "B", "references": ["D"]},
        {"name": "C", "references": ["D"]},
        {"name": "D", "references": []},
    ]
    path = tmp_path / "slice.json"
    path.write_text(json.dumps(rows), encoding="utf-8")

    report = build_report(path, tol=1e-9, max_nodes=10)

    assert report["schema"] == "info_geometry.local_lightcone_spectral_filter.v1"
    assert report["input_mode"] == "lean_graph_references_dependencies"
    assert report["orientation"] == "local matrix edges are dependency -> user causal-flow edges"
    assert report["node_count"] == 4
    assert report["edge_count"] == 4
    assert report["hodge"]["harmonic_dim"] == 1
    assert report["drazin"]["residuals"]["projector_idempotent_frobenius"] < 1e-7
    assert {node["name"] for node in report["nodes"]} == {"A", "B", "C", "D"}


def test_build_report_refuses_unbounded_dense_slice(tmp_path: Path) -> None:
    rows = [{"name": f"N{i}", "references": []} for i in range(4)]
    path = tmp_path / "slice.json"
    path.write_text(json.dumps(rows), encoding="utf-8")

    with pytest.raises(SystemExit, match="refusing dense local spectral filter"):
        build_report(path, tol=1e-9, max_nodes=3)


def test_recurrent_two_node_cycle_has_nonzero_spectral_core(tmp_path: Path) -> None:
    rows = [
        {"name": "A", "references": ["B"]},
        {"name": "B", "references": ["A"]},
    ]
    path = tmp_path / "cycle.json"
    path.write_text(json.dumps(rows), encoding="utf-8")

    report = build_report(path, tol=1e-9, max_nodes=10)

    assert report["drazin"]["nonzero_schur_dim"] > 0
    assert abs(report["drazin"]["projector_trace"]) > 0.5


def test_pure_dag_chain_has_trivial_drazin_core(tmp_path: Path) -> None:
    rows = [
        {"name": "A", "references": ["B"]},
        {"name": "B", "references": ["C"]},
        {"name": "C", "references": []},
    ]
    path = tmp_path / "dag.json"
    path.write_text(json.dumps(rows), encoding="utf-8")

    report = build_report(path, tol=1e-9, max_nodes=10)

    assert report["drazin"]["nonzero_schur_dim"] == 0
    assert report["drazin"]["projector_trace"] == 0.0
