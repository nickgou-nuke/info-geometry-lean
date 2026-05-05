import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.infra.build_predigestion_packets import make_packet
from tools.infra.hive_predigestion_ingest import make_task


REPO = Path(__file__).resolve().parents[1]
BUILD = REPO / "tools" / "infra" / "build_predigestion_packets.py"
INGEST = REPO / "tools" / "infra" / "hive_predigestion_ingest.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("\n".join(json.dumps(row) for row in rows) + "\n", encoding="utf-8")


def test_predigestion_packet_has_deterministic_id_and_boundary() -> None:
    row = {
        "id": "chunk-1",
        "source": "paper.pdf",
        "title": "Example",
        "text": "A finite primitive support defines a restricted zeta partition. More words.",
        "lang": "en",
        "definitions": ["primitive support"],
        "symbols": ["Z_A(beta)"],
    }
    a = make_packet(row, source_kind="paper")
    b = make_packet(row, source_kind="paper")

    assert a["schema"] == "info_geometry.predigested_claim.v1"
    assert a["id"] == b["id"]
    assert a["risk"] == "informal"
    assert a["authority"] == "semantic"
    assert a["authority_boundary"]["lean_remains_proof_authority"] is True


def test_invalid_enum_fails() -> None:
    with pytest.raises(SystemExit):
        make_packet({"text": "x"}, source_kind="dream")
    packet = make_packet({"text": "x"}, source_kind="paper")
    packet["authority"] = "promoted"
    with pytest.raises(SystemExit):
        make_task(packet, task_kind="formalize_claim")
    with pytest.raises(SystemExit):
        make_task(make_packet({"text": "x"}, source_kind="paper"), task_kind="invent_claim")


def test_hive_task_materializes_non_authoritative_queue_packet() -> None:
    packet = make_packet({"id": "c", "text": "Every count ray has a gauge section."}, source_kind="doc")
    task = make_task(packet, task_kind="map_claim_to_owner_surface")

    assert task["schema"] == "hive.packet.predigestion_task.v1"
    assert task["authority"] == "proposal"
    assert task["status"] == "queued"
    assert task["required_gates"] == ["lean_checked", "build_checked", "audit_checked"]
    assert task["authority_boundary"]["only_lean_checked_artifacts_can_assert"] is True


def test_cli_builds_claims_and_tasks(tmp_path: Path) -> None:
    chunks = tmp_path / "chunks.jsonl"
    claims = tmp_path / "claims.jsonl"
    claim_summary = tmp_path / "claims.summary.json"
    tasks = tmp_path / "tasks.jsonl"
    task_summary = tmp_path / "tasks.summary.json"
    write_jsonl(chunks, [{"id": "chunk-1", "text": "Claim one. Claim two.", "source": "doc.md"}])

    proc = subprocess.run(
        [
            sys.executable,
            str(BUILD),
            "--input",
            str(chunks),
            "--source-kind",
            "old_doc",
            "--out",
            str(claims),
            "--summary-out",
            str(claim_summary),
        ],
        cwd=REPO,
        check=False,
    )
    assert proc.returncode == 0
    claim_rows = [json.loads(line) for line in claims.read_text(encoding="utf-8").splitlines()]
    assert len(claim_rows) == 1
    assert json.loads(claim_summary.read_text(encoding="utf-8"))["records"] == 1

    proc = subprocess.run(
        [
            sys.executable,
            str(INGEST),
            "--claims",
            str(claims),
            "--out",
            str(tasks),
            "--summary-out",
            str(task_summary),
            "--task-kind",
            "formalize_claim",
        ],
        cwd=REPO,
        check=False,
    )
    assert proc.returncode == 0
    task_rows = [json.loads(line) for line in tasks.read_text(encoding="utf-8").splitlines()]
    assert task_rows[0]["claim_id"] == claim_rows[0]["id"]
    assert json.loads(task_summary.read_text(encoding="utf-8"))["by_task_kind"] == {"formalize_claim": 1}
