import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
TOOL = REPO / "tools" / "infra" / "build_chiral_patch_hashes.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def test_build_chiral_patch_hashes_emits_three_patch_families(tmp_path: Path) -> None:
    nodes = tmp_path / "ig_nodes.jsonl"
    edges = tmp_path / "ig_edges.jsonl"
    fingerprints = tmp_path / "expr_fingerprints.jsonl"
    out = tmp_path / "out"

    write_jsonl(
        nodes,
        [
            {"id": "A.seed", "name": "A.seed", "typeFingerprint": {"shapeHash": "shape.alpha"}},
            {"id": "B.trunk", "name": "B.trunk", "typeFingerprint": {"shapeHash": "shape.beta"}},
            {"id": "C.leaf", "name": "C.leaf", "typeFingerprint": {"shapeHash": "shape.alpha"}},
            {"id": "D.peer", "name": "D.peer", "typeFingerprint": {"shapeHash": "shape.alpha"}},
        ],
    )
    write_jsonl(
        edges,
        [
            {
                "src": "A.seed",
                "dst": "B.trunk",
                "kind": "depends_on",
                "weight": 1.0,
                "action_weight": 0.3,
                "chiral_orientation": "forward",
            },
            {
                "src": "B.trunk",
                "dst": "A.seed",
                "kind": "used_by",
                "weight": 1.0,
                "chiral_orientation": "backward",
            },
            {
                "src": "B.trunk",
                "dst": "C.leaf",
                "kind": "proposed_beta_reduction",
                "weight": 2.0,
                "chiral_orientation": "mixed",
            },
            {
                "src": "C.leaf",
                "dst": "D.peer",
                "kind": "same_shape",
                "weight": 1.0,
                "chiral_orientation": "forward",
            },
        ],
    )
    write_jsonl(
        fingerprints,
        [
            {
                "decl_name": "A.seed",
                "feature_counts": {"token_count": 8, "redex_proxy": 0, "binder_depth_proxy": 1},
                "level_1_local_hash": "shape.alpha",
            },
            {
                "decl_name": "B.trunk",
                "feature_counts": {"token_count": 10, "redex_proxy": 1, "binder_depth_proxy": 2},
                "level_1_local_hash": "shape.beta",
            },
            {
                "decl_name": "C.leaf",
                "feature_counts": {"token_count": 12, "redex_proxy": 1, "binder_depth_proxy": 1},
                "level_1_local_hash": "shape.alpha",
            },
            {
                "decl_name": "D.peer",
                "feature_counts": {"token_count": 9, "redex_proxy": 0, "binder_depth_proxy": 1},
                "level_1_local_hash": "shape.alpha",
            },
        ],
    )

    result = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--nodes",
            str(nodes),
            "--edges",
            str(edges),
            "--fingerprints",
            str(fingerprints),
            "--output-dir",
            str(out),
            "--run-id",
            "patch_run_test",
            "--ego-limit",
            "4",
            "--print-json",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    summary = json.loads(result.stdout)
    patches = read_jsonl(out / "ig_chiral_patches.jsonl")
    members = read_jsonl(out / "ig_patch_members.jsonl")
    signatures = read_jsonl(out / "ig_patch_spectral_signatures.jsonl")
    patch_edges = read_jsonl(out / "ig_patch_edges.jsonl")
    run_rows = read_jsonl(out / "ig_patch_runs.jsonl")

    assert summary["patch_run_id"] == "patch_run_test"
    assert summary["scc_patch_count"] >= 1
    assert summary["ego_patch_count"] >= 1
    assert summary["binder_pattern_patch_count"] >= 1
    assert members
    assert signatures
    assert patch_edges
    assert run_rows[0]["schema_version"] == "ig.patch_run.v1"
    assert run_rows[0]["algorithm_version"] == "chiral_patch_hashes.v1.2"
    assert run_rows[0]["fingerprints_available"] is True
    assert run_rows[0]["source_graph_hash"].startswith("sha256:")

    required = {
        "schema_version",
        "patch_run_id",
        "patch_type",
        "level",
        "coarse_hash",
        "debruijn_histogram",
        "chiral_entropy",
        "chiral_bias",
        "cartan_proxy_histogram",
    }
    assert required <= set(patches[0])
    assert all(p["non_overclaim"] is True for p in patches)
    assert all(p["claim_scope"] == "derived_spectral_neighborhood_sidecar" for p in patches)
    assert all("pseudo_logdet" in sig for sig in signatures)
    assert all("spectral_status" in sig for sig in signatures)
    assert any(p["cartan_proxy_histogram"]["p_odd"] >= 1 for p in patches)
    assert any(e["edge_type"] == "PATCH_DEPENDS_ON" for e in patch_edges)

    out2 = tmp_path / "out2"
    subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--nodes",
            str(nodes),
            "--edges",
            str(edges),
            "--fingerprints",
            str(fingerprints),
            "--output-dir",
            str(out2),
            "--run-id",
            "patch_run_test_2",
            "--ego-limit",
            "4",
            "--print-json",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    hashes1 = sorted(p["coarse_hash"] for p in patches)
    hashes2 = sorted(p["coarse_hash"] for p in read_jsonl(out2 / "ig_chiral_patches.jsonl"))
    assert hashes1 == hashes2

    out_no_fp = tmp_path / "out_no_fp"
    result_no_fp = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--nodes",
            str(nodes),
            "--edges",
            str(edges),
            "--output-dir",
            str(out_no_fp),
            "--run-id",
            "patch_run_no_fp",
            "--ego-limit",
            "4",
            "--print-json",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    summary_no_fp = json.loads(result_no_fp.stdout)
    assert summary_no_fp["binder_pattern_patch_count"] == 0
    assert read_jsonl(out_no_fp / "ig_patch_runs.jsonl")[0]["fingerprints_available"] is False
