from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sample_snapshot() -> dict:
    def decl(name: str, attrs: dict) -> dict:
        return {
            "id": name,
            "name": name,
            "kind": "Declaration",
            "module": "Test",
            "file": "Test.lean",
            "line": 1,
            "rep_depth": None,
            "role": None,
            "module_family": "Test",
            "commit_sha": "test",
            "toolchain": "test",
            "artifact_version": 1,
            "attrs": attrs,
        }

    clean_gate = {
        "vacuity": {"role": "gate"},
        "contamination": {"state": "clean"},
        "hole": {"state": "none"},
    }

    fake = {
        "vacuity": {"role": "fake_transport"},
        "contamination": {"state": "clean"},
        "hole": {"state": "none"},
    }

    critic_blocked = {
        **fake,
        "critic": {"severity": "high"},
    }

    return {
        "metadata": {
            "created_at": "test",
            "commit_sha": "test",
            "toolchain": "test",
            "artifact_version": 1,
        },
        "nodes": [
            decl("Test.Consumer", clean_gate),
            decl("Test.Wrapper", fake),
            decl("Test.Canonical", clean_gate),
            decl("Test.BadWrapper", critic_blocked),
            decl("Test.MissingReplacementWrapper", fake),
            decl("Test.CycleReplacement", clean_gate),
            decl("Test.OtherWrapper", fake),
            decl("Test.OtherCanonical", clean_gate),
        ],
        "edges": [
            {
                "src": "Test.Consumer",
                "dst": "Test.Wrapper",
                "kind": "depends_value",
                "weight": 1.0,
                "evidence_ref": "fixture",
                "attrs": {},
            },
            {
                "src": "Test.Wrapper",
                "dst": "Test.Canonical",
                "kind": "depends_value",
                "weight": 1.0,
                "evidence_ref": "fixture",
                "attrs": {},
            },
            {
                "src": "Test.CycleReplacement",
                "dst": "Test.MissingReplacementWrapper",
                "kind": "depends_value",
                "weight": 1.0,
                "evidence_ref": "fixture",
                "attrs": {},
            },
        ],
    }


def packet(
    packet_id: str,
    target: str,
    replacement: str,
    *,
    state: str = "certified",
    file: str = "Test.lean",
    start: int = 10,
    end: int = 20,
    stream: str = "vacuum",
    action_phase: str = "contract",
) -> dict:
    return {
        "packet_id": packet_id,
        "packet_stream": stream,
        "action_phase": action_phase,
        "state": state,
        "target": target,
        "module": "Test",
        "file": file,
        "scc_id": f"scc_{packet_id}",
        "scc_size": 1,
        "signature_class": "",
        "priority_score": 10.0,
        "certificate_ref": "cert.json",
        "snapshot_hash": "sha256:test",
        "audit_hash": "sha256:test",
        "toolchain": "test",
        "commit_sha": "test",
        "decl_span_kind": "top_level_decl",
        "patch_span_kind": "decl_body",
        "source_info_kind": "original",
        "topo_rank": 1,
        "reverse_topo_rank": 1,
        "payload": {
            "role": "fake_transport",
            "replacement": replacement,
            "rewrite_mode": "replace_decl_body",
            "replacement_body": f"by exact {replacement}",
            "destructive": False,
            "source_patch": {
                "file": file,
                "startByte": start,
                "endByte": end,
                "fileHash": "sha256:file",
            },
        },
    }


def run_shadow_ledger(tmp_path: Path, rows: list[dict]) -> tuple[list[dict], list[dict], dict]:
    snapshot = tmp_path / "graph_snapshot.vacuity.json"
    packets = tmp_path / "vacuum_packets.jsonl"
    approved = tmp_path / "shadow_approved_packets.jsonl"
    deferred = tmp_path / "shadow_deferred_packets.jsonl"
    manifest = tmp_path / "surgery_manifest.json"
    report = tmp_path / "shadow_ledger_report.json"

    write_json(snapshot, sample_snapshot())
    write_jsonl(packets, rows)

    subprocess.check_call(
        [
            sys.executable,
            "tools/leantrail/shadow_ledger.py",
            "--snapshot",
            str(snapshot),
            "--vacuum-packets",
            str(packets),
            "--approved-out",
            str(approved),
            "--deferred-out",
            str(deferred),
            "--manifest-out",
            str(manifest),
            "--json-out",
            str(report),
            "--epoch",
            "shadow-test",
        ],
        cwd=ROOT,
    )

    return read_jsonl(approved), read_jsonl(deferred), json.loads(manifest.read_text())


def test_shadow_ledger_smoke(tmp_path: Path) -> None:
    approved_rows, deferred_rows, manifest_payload = run_shadow_ledger(
        tmp_path,
        [
            packet("p_ok", "Test.Wrapper", "Test.Canonical"),
            packet("p_missing", "Test.MissingReplacementWrapper", "Test.DoesNotExist", start=30, end=40),
            packet("p_critic", "Test.BadWrapper", "Test.Canonical", start=50, end=60),
        ],
    )

    assert len(approved_rows) == 1
    assert approved_rows[0]["packet_id"] == "p_ok"
    assert approved_rows[0]["state"] == "shadow_approved"
    assert approved_rows[0]["shadow_state"] == "approved"
    assert approved_rows[0]["shadow_checks"]["state_transition"] == "certified -> shadow_approved"

    reasons = {row["packet_id"]: row["shadow_reason"] for row in deferred_rows}
    assert reasons["p_missing"] == "replacement_node_missing"
    assert reasons["p_critic"] == "high_severity_critic_block"

    assert manifest_payload["counts"]["approved"] == 1
    assert manifest_payload["counts"]["deferred"] == 2


def test_shadow_ledger_defer_non_candidate_and_cycle_risk(tmp_path: Path) -> None:
    approved_rows, deferred_rows, manifest_payload = run_shadow_ledger(
        tmp_path,
        [
            packet("p_not_certified", "Test.Wrapper", "Test.Canonical", state="proposed"),
            packet(
                "p_cycle",
                "Test.MissingReplacementWrapper",
                "Test.CycleReplacement",
                start=30,
                end=40,
            ),
        ],
    )

    assert approved_rows == []
    reasons = {row["packet_id"]: row["shadow_reason"] for row in deferred_rows}
    assert reasons["p_not_certified"] == "not_certified_vacuum_contract:vacuum:contract:proposed"
    assert reasons["p_cycle"] == "replacement_depends_on_target_cycle_risk"
    assert manifest_payload["counts"]["approved"] == 0
    assert manifest_payload["counts"]["deferred"] == 2


def test_shadow_ledger_defer_non_vacuum_and_non_contract(tmp_path: Path) -> None:
    approved_rows, deferred_rows, manifest_payload = run_shadow_ledger(
        tmp_path,
        [
            packet("p_bridge", "Test.Wrapper", "Test.Canonical", stream="bridge"),
            packet("p_align", "Test.Wrapper", "Test.Canonical", action_phase="align", start=30, end=40),
        ],
    )

    assert approved_rows == []
    reasons = {row["packet_id"]: row["shadow_reason"] for row in deferred_rows}
    assert reasons["p_bridge"] == "not_certified_vacuum_contract:bridge:contract:certified"
    assert reasons["p_align"] == "not_certified_vacuum_contract:vacuum:align:certified"
    assert manifest_payload["counts"]["approved"] == 0
    assert manifest_payload["counts"]["deferred"] == 2


def test_shadow_ledger_defer_macro_wall_source_info(tmp_path: Path) -> None:
    row = packet("p_macro", "Test.Wrapper", "Test.Canonical")
    row["source_info_kind"] = "syntheticOrNone"

    approved_rows, deferred_rows, _ = run_shadow_ledger(tmp_path, [row])

    assert approved_rows == []
    assert deferred_rows[0]["packet_id"] == "p_macro"
    assert deferred_rows[0]["shadow_reason"] == "source_patch_provenance_not_safe"


def test_shadow_ledger_defer_missing_source_patch_span(tmp_path: Path) -> None:
    row = packet("p_missing_span", "Test.Wrapper", "Test.Canonical")
    del row["payload"]["source_patch"]["startByte"]

    approved_rows, deferred_rows, _ = run_shadow_ledger(tmp_path, [row])

    assert approved_rows == []
    assert deferred_rows[0]["packet_id"] == "p_missing_span"
    assert deferred_rows[0]["shadow_reason"] == "source_patch_missing_startByte"


def test_shadow_ledger_defer_overlapping_same_file_spans(tmp_path: Path) -> None:
    approved_rows, deferred_rows, manifest_payload = run_shadow_ledger(
        tmp_path,
        [
            packet("p_first", "Test.Wrapper", "Test.Canonical", start=10, end=20),
            packet(
                "p_overlap",
                "Test.OtherWrapper",
                "Test.OtherCanonical",
                start=15,
                end=25,
            ),
        ],
    )

    assert len(approved_rows) == 1
    assert approved_rows[0]["packet_id"] in {"p_first", "p_overlap"}
    reasons = {row["packet_id"]: row["shadow_reason"] for row in deferred_rows}
    assert set(reasons) == ({"p_first", "p_overlap"} - {approved_rows[0]["packet_id"]})
    assert next(iter(reasons.values())) == "source_patch_span_overlaps_prior_packet"
    assert manifest_payload["counts"]["approved"] == 1
    assert manifest_payload["counts"]["deferred"] == 1


def test_shadow_ledger_allow_non_overlapping_same_file_spans(tmp_path: Path) -> None:
    approved_rows, deferred_rows, manifest_payload = run_shadow_ledger(
        tmp_path,
        [
            packet("p_first", "Test.Wrapper", "Test.Canonical", start=10, end=20),
            packet(
                "p_second",
                "Test.OtherWrapper",
                "Test.OtherCanonical",
                start=30,
                end=40,
            ),
        ],
    )

    assert {row["packet_id"] for row in approved_rows} == {"p_first", "p_second"}
    assert deferred_rows == []
    assert manifest_payload["counts"]["approved"] == 2
    assert manifest_payload["counts"]["deferred"] == 0


def test_shadow_ledger_critic_override_allows_high_severity(tmp_path: Path) -> None:
    row = packet("p_critic_override", "Test.BadWrapper", "Test.Canonical")
    row["payload"]["allow_high_severity_critic"] = True

    approved_rows, deferred_rows, manifest_payload = run_shadow_ledger(tmp_path, [row])

    assert len(approved_rows) == 1
    assert approved_rows[0]["packet_id"] == "p_critic_override"
    assert approved_rows[0]["state"] == "shadow_approved"
    assert deferred_rows == []
    assert manifest_payload["counts"]["approved"] == 1
