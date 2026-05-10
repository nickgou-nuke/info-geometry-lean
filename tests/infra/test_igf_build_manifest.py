import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
CLI = REPO / "cli" / "igf_main.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(r) + "\n" for r in rows), encoding="utf-8")


def test_igf_build_writes_manifest_with_hashes_and_counts(tmp_path: Path) -> None:
    nodes = tmp_path / "ig_nodes.jsonl"
    edges = tmp_path / "ig_edges.jsonl"
    fps = tmp_path / "expr_fingerprints.jsonl"
    out = tmp_path / "out"

    write_jsonl(
        nodes,
        [
            {"id": "A.seed", "name": "A.seed", "typeFingerprint": {"shapeHash": "shape.alpha"}},
            {"id": "B.trunk", "name": "B.trunk", "typeFingerprint": {"shapeHash": "shape.beta"}},
            {"id": "C.leaf", "name": "C.leaf", "typeFingerprint": {"shapeHash": "shape.alpha"}},
        ],
    )
    write_jsonl(
        edges,
        [
            {"src": "A.seed", "dst": "B.trunk", "kind": "depends_on", "weight": 1.0, "chiral_orientation": "forward"},
            {"src": "B.trunk", "dst": "A.seed", "kind": "used_by", "weight": 1.0, "chiral_orientation": "backward"},
            {"src": "B.trunk", "dst": "C.leaf", "kind": "proposed_beta_reduction", "weight": 2.0, "chiral_orientation": "mixed"},
        ],
    )
    write_jsonl(
        fps,
        [
            {"decl_name": "A.seed", "feature_counts": {"token_count": 5, "redex_proxy": 0, "binder_depth_proxy": 1}, "level_1_local_hash": "shape.alpha"},
            {"decl_name": "B.trunk", "feature_counts": {"token_count": 7, "redex_proxy": 1, "binder_depth_proxy": 2}, "level_1_local_hash": "shape.beta"},
            {"decl_name": "C.leaf", "feature_counts": {"token_count": 6, "redex_proxy": 1, "binder_depth_proxy": 1}, "level_1_local_hash": "shape.alpha"},
        ],
    )

    result = subprocess.run(
        [
            sys.executable,
            str(CLI),
            "build",
            "--nodes",
            str(nodes),
            "--edges",
            str(edges),
            "--fingerprints",
            str(fps),
            "--output-dir",
            str(out),
            "--run-id",
            "patch_run_kernel_test",
            "--ego-limit",
            "4",
            "--print-json",
        ],
        check=False,
        text=True,
        capture_output=True,
        cwd=REPO,
    )

    assert result.returncode == 0, result.stderr
    payload = json.loads(result.stdout)
    assert payload["ok"] is True
    assert payload["run_id"] == "patch_run_kernel_test"

    manifest_path = out / "manifest.json"
    assert manifest_path.exists()
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    assert manifest["run_id"] == "patch_run_kernel_test"
    assert manifest["generator"] == "tools/infra/build_chiral_patch_hashes.py"
    assert manifest["generator_version"] == "chiral_patch_hashes.v1.2"
    assert manifest["schema_versions"]["ig_patch_runs.jsonl"] == "ig.patch_run.v1"
    assert manifest["input_hashes"]["nodes"].startswith("sha256:")
    assert manifest["input_hashes"]["edges"].startswith("sha256:")
    assert manifest["input_hashes"]["fingerprints"].startswith("sha256:")

    for key in [
        "ig_patch_runs.jsonl",
        "ig_chiral_patches.jsonl",
        "ig_patch_members.jsonl",
        "ig_patch_edges.jsonl",
        "ig_patch_spectral_signatures.jsonl",
    ]:
        assert key in manifest["output_hashes"]
        assert manifest["output_hashes"][key].startswith("sha256:")
        assert manifest["row_counts"][key] >= 0
