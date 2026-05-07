from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.infra.hive_local_packet_store import append_packet, packet_hash, read_store

SCRIPT = Path("tools/infra/hive_local_packet_store.py")

BASE = {
    "status": "captured",
    "lineage_id": "lineage_demo",
    "revision": 1,
    "origin_run_id": "run_demo",
    "created_at": "2026-05-07T00:00:00Z",
    "updated_at": "2026-05-07T00:00:00Z",
}


def source_packet(packet_id: str, *, parent_refs: list[str] | None = None) -> dict:
    packet = {
        **BASE,
        "id": packet_id,
        "kind": "SourceObservationPacket",
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
    if parent_refs is not None:
        packet["parent_refs"] = parent_refs
    return packet


def write_packet(tmp_path: Path, packet: dict, name: str | None = None) -> Path:
    path = tmp_path / (name or f"{packet['id']}.json")
    path.write_text(json.dumps(packet, sort_keys=True), encoding="utf-8")
    return path


def run_cli(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def test_append_valid_packet_computes_hash_and_survives_reload(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    packet = source_packet("src_a")

    digest, status = append_packet(store, packet)

    assert status == "appended"
    assert digest == packet_hash(packet)
    records = read_store(store)
    assert len(records) == 1
    assert records[0]["id"] == "src_a"
    assert records[0]["packet_hash"] == digest


def test_append_rejects_invalid_packet(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    packet = source_packet("bad")
    packet.pop("summary")

    packet_path = write_packet(tmp_path, packet, "bad.json")
    result = run_cli("append", "--store", str(store), "--packet", str(packet_path))

    assert result.returncode == 1
    assert "failed schema validation" in result.stderr
    assert not store.exists()


def test_duplicate_hash_is_idempotently_ignored(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    packet = source_packet("src_dup")

    first = append_packet(store, packet)
    second = append_packet(store, packet)

    assert first[1] == "appended"
    assert second[1] == "duplicate_hash_ignored"
    assert len(read_store(store)) == 1


def test_duplicate_id_with_different_hash_rejected(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    packet = source_packet("src_same_id")
    append_packet(store, packet)
    changed = {**packet, "summary": "A changed source observation."}

    try:
        append_packet(store, changed)
    except Exception as exc:  # noqa: BLE001 - assert message from CLI-friendly StoreError
        assert "packet id already exists" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected duplicate id rejection")


def test_cli_list_filters_by_kind_authority_and_lineage(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_a"))
    other = {**source_packet("src_b"), "lineage_id": "lineage_other"}
    append_packet(store, other)

    result = run_cli(
        "list",
        "--store",
        str(store),
        "--kind",
        "SourceObservationPacket",
        "--authority",
        "navigation",
        "--lineage-id",
        "lineage_demo",
    )

    assert result.returncode == 0, result.stderr
    rows = json.loads(result.stdout)
    assert [row["id"] for row in rows] == ["src_a"]


def test_show_parents_children_and_lineage(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("parent"))
    append_packet(store, source_packet("child", parent_refs=["parent"]))

    show = run_cli("show", "--store", str(store), "--id", "child")
    assert show.returncode == 0
    assert json.loads(show.stdout)["id"] == "child"

    parents = run_cli("parents", "--store", str(store), "--id", "child")
    assert parents.returncode == 0
    assert json.loads(parents.stdout)[0]["id"] == "parent"

    children = run_cli("children", "--store", str(store), "--id", "parent")
    assert children.returncode == 0
    assert json.loads(children.stdout)[0]["id"] == "child"

    lineage = run_cli("lineage", "--store", str(store), "--id", "child")
    assert lineage.returncode == 0
    graph = json.loads(lineage.stdout)
    assert {node["id"] for node in graph["nodes"]} == {"parent", "child"}
    assert {tuple(edge.values()) for edge in graph["edges"]} == {("parent", "child")}
