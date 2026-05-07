from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.infra.hive_local_packet_store import append_packet, read_store
from tools.infra.hive_motherbee import discover_tasks, run_once

SCRIPT = Path("tools/infra/hive_motherbee.py")

BASE = {
    "lineage_id": "lineage_motherbee_demo",
    "revision": 1,
    "origin_run_id": "run_motherbee_demo",
    "created_at": "2026-05-07T00:00:00Z",
    "updated_at": "2026-05-07T00:00:00Z",
}


def source_packet(packet_id: str, *, status: str = "captured") -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "SourceObservationPacket",
        "status": status,
        "authority": "navigation",
        "authority_origin": "source_observation",
        "epistemic_layer": "raw_source",
        "cognitive_function": "sensation",
        "jung_function": "sensation",
        "jung_attitude": "extraverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "source_type": "repo_file",
        "source_uri": f"docs/demo/{packet_id}.md",
        "capture_method": "test_fixture",
        "content_hash": f"sha256:{packet_id}",
        "summary": f"Observed source {packet_id}.",
        "allowed_uses": ["citation", "retrieval", "source_grounding"],
        "forbidden_uses": ["proof", "promotion", "authority_gate_bypass"],
    }


def run_cli(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def test_discover_tasks_routes_captured_source_observation_to_socratesbee(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    src = source_packet("src_a")
    append_packet(store, src)

    tasks = discover_tasks(read_store(store), store_path=store, dry_run_task=True)

    assert len(tasks) == 1
    task = tasks[0]
    assert task["kind"] == "BeeTask"
    assert task["assigned_role"] == "SocratesBee"
    assert task["task_kind"] == "socratic.question"
    assert task["target_packet_id"] == "src_a"
    assert task["input_packet_ids"] == ["src_a"]
    assert task["parent_refs"] == ["src_a"]
    assert task["authority_ceiling"] == "semantic"
    assert task["dry_run"] is True
    assert "PromotionDecisionPacket" in task["forbidden_output_kinds"]


def test_once_appends_beetask_as_append_only_routing_receipt(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_a"))

    result = run_once(store, limit=1, dry_run=False, dry_run_task=False)

    assert result["emitted_count"] == 1
    records = read_store(store)
    assert [record["kind"] for record in records] == ["SourceObservationPacket", "BeeTask"]
    task = records[1]
    assert task["target_packet_id"] == "src_a"
    assert task["dry_run"] is False
    assert task["motherbee_rule_id"] == "source-observation-to-socrates-v1"
    assert result["receipts"][0]["id"] == task["id"]


def test_once_is_idempotent_after_beetask_exists(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_a"))

    first = run_once(store, limit=1, dry_run=False, dry_run_task=False)
    second = run_once(store, limit=1, dry_run=False, dry_run_task=False)

    assert first["emitted_count"] == 1
    assert second["planned_count"] == 0
    assert second["emitted_count"] == 0
    assert [record["kind"] for record in read_store(store)] == ["SourceObservationPacket", "BeeTask"]


def test_dry_run_prints_tasks_without_mutating_store(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_a"))

    result = run_once(store, limit=1, dry_run=True, dry_run_task=True)

    assert result["planned_count"] == 1
    assert result["emitted_count"] == 0
    assert result["tasks"][0]["dry_run"] is True
    assert [record["kind"] for record in read_store(store)] == ["SourceObservationPacket"]


def test_limit_and_priority_are_deterministic(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, {**source_packet("src_b"), "created_at": "2026-05-07T00:00:02Z", "updated_at": "2026-05-07T00:00:02Z"})
    append_packet(store, source_packet("src_a"))

    result = run_once(store, limit=1, dry_run=True, dry_run_task=False)

    assert result["planned_count"] == 2
    assert len(result["tasks"]) == 1
    assert result["tasks"][0]["target_packet_id"] == "src_a"


def test_non_matching_status_is_not_scheduled(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_archived", status="archived"))

    result = run_once(store, limit=1, dry_run=True, dry_run_task=False)

    assert result["planned_count"] == 0
    assert result["tasks"] == []


def test_cli_once_appends_task(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_cli"))

    result = run_cli("once", "--store", str(store), "--limit", "1")

    assert result.returncode == 0, result.stderr
    payload = json.loads(result.stdout)
    assert payload["emitted_count"] == 1
    assert [record["kind"] for record in read_store(store)] == ["SourceObservationPacket", "BeeTask"]


def test_cli_dry_run_does_not_append_task(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_cli_dry"))

    result = run_cli("once", "--store", str(store), "--limit", "1", "--dry-run", "--task-dry-run")

    assert result.returncode == 0, result.stderr
    payload = json.loads(result.stdout)
    assert payload["dry_run"] is True
    assert payload["tasks"][0]["dry_run"] is True
    assert [record["kind"] for record in read_store(store)] == ["SourceObservationPacket"]
