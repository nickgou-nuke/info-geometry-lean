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

    assert summary["patch_run_id"] == "patch_run_test"
    assert summary["scc_patch_count"] >= 1
    assert summary["ego_patch_count"] >= 1
    assert summary["binder_pattern_patch_count"] >= 1
    assert members
    assert signatures
    assert patch_edges

    required = {
        "patch_type",
        "level",
        "coarse_hash",
        "debruijn_histogram",
        "chiral_entropy",
        "chiral_bias",
        "cartan_proxy_histogram",
    }
    assert required <= set(patches[0])
    assert all("pseudo_logdet" in sig for sig in signatures)
    assert any(p["cartan_proxy_histogram"]["p_odd"] >= 1 for p in patches)
