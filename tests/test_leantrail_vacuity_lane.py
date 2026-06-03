from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.leantrail.vacuity_audit import is_safe_lean_name
from tools.leantrail.vacuity_ingest import ingest_vacuity

ROOT = Path(__file__).resolve().parents[1]


def _node(
    node_id: str,
    *,
    name: str | None = None,
    kind: str = "Declaration",
    attrs: dict | None = None,
) -> dict:
    return {
        "id": node_id,
        "name": name or node_id,
        "kind": kind,
        "module": "Test.Module",
        "file": "Test/Module.lean",
        "line": 1,
        "rep_depth": None,
        "role": None,
        "module_family": "Test.Module",
        "commit_sha": "test",
        "toolchain": "test",
        "artifact_version": 1,
        "attrs": attrs or {},
    }


def _write_snapshot(path: Path, nodes: list[dict]) -> None:
    path.write_text(
        json.dumps({"metadata": {}, "nodes": nodes, "edges": []}, indent=2) + "\n",
        encoding="utf-8",
    )


def _run_surgery_plan(tmp_path: Path, snapshot: Path, *extra_args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(ROOT / "tools" / "leantrail" / "surgery_plan.py"),
            "--snapshot",
            str(snapshot),
            "--vacuum-out",
            str(tmp_path / "vacuum.jsonl"),
            "--bridge-out",
            str(tmp_path / "bridge.jsonl"),
            "--alignment-out",
            str(tmp_path / "alignment.jsonl"),
            "--proof-hole-out",
            str(tmp_path / "proof_hole.jsonl"),
            "--json-out",
            str(tmp_path / "surgery_report.json"),
            *extra_args,
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def test_vacuity_ingest_only_touches_declaration_nodes(tmp_path: Path) -> None:
    snapshot = tmp_path / "snapshot.json"
    audit = tmp_path / "audit.jsonl"
    out = tmp_path / "snapshot.vacuity.json"
    _write_snapshot(
        snapshot,
        [
            _node("Test.Decl"),
            _node("module:Test.Decl", name="Test.Decl", kind="Module"),
        ],
    )
    audit.write_text(
        json.dumps({
            "target": "Test.Decl",
            "audit_hash": "sha256:test",
            "attrs": {"vacuity": {"role": "pure_conductor"}},
        })
        + "\n",
        encoding="utf-8",
    )

    report = ingest_vacuity(snapshot, audit, out)
    payload = json.loads(out.read_text(encoding="utf-8"))
    by_id = {node["id"]: node for node in payload["nodes"]}

    assert report["rows"] == 1
    assert report["merged_nodes"] == 1
    assert report["missing_target_count"] == 0
    assert by_id["Test.Decl"]["attrs"]["vacuity"]["role"] == "pure_conductor"
    assert "vacuity" not in by_id["module:Test.Decl"]["attrs"]


def test_surgery_plan_rejects_snapshot_without_vacuity_evidence(tmp_path: Path) -> None:
    snapshot = tmp_path / "snapshot.json"
    _write_snapshot(snapshot, [_node("Test.Decl")])

    proc = _run_surgery_plan(tmp_path, snapshot)
    report = json.loads((tmp_path / "surgery_report.json").read_text(encoding="utf-8"))

    assert proc.returncode == 2
    assert report["ok"] is False
    assert report["error"] == "missing_vacuity_evidence"
    assert report["vacuity_evidence_nodes"] == 0
    assert not (tmp_path / "vacuum.jsonl").exists()


def test_surgery_plan_allows_unaudited_snapshot_only_with_flag(tmp_path: Path) -> None:
    snapshot = tmp_path / "snapshot.json"
    _write_snapshot(snapshot, [_node("Test.Decl")])

    proc = _run_surgery_plan(tmp_path, snapshot, "--allow-unaudited-snapshot")
    report = json.loads((tmp_path / "surgery_report.json").read_text(encoding="utf-8"))

    assert proc.returncode == 0
    assert report["ok"] is True
    assert report["vacuity_evidence_nodes"] == 0
    assert (tmp_path / "vacuum.jsonl").exists()


def test_vacuity_audit_rejects_unsafe_lean_command_names() -> None:
    assert is_safe_lean_name("InfoGeometry.Valid.Name")
    assert not is_safe_lean_name("InfoGeometry.Bad; #eval 1")
    assert not is_safe_lean_name("InfoGeometry.Bad\n#eval 1")
    assert not is_safe_lean_name(".InfoGeometry.Bad")
