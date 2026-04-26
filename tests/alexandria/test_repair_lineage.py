from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.alexandria.repair_lineage import (
    GateResult,
    build_lineage_edges,
    build_repair_attempt,
    purified_chunk_from_broken,
)


REPO = Path(__file__).resolve().parents[2]
REPAIR_LINEAGE = REPO / "tools" / "alexandria" / "repair_lineage.py"


def broken_chunk() -> dict:
    return {
        "_key": "chunk_broken",
        "documentKey": "doc_1",
        "sectionKey": "sec_1",
        "ordinal": 1,
        "chunkKind": "definition",
        "chunkingStrategy": "python_ast_node",
        "title": "Python function broken",
        "text": "def f(:\n    pass\n",
        "tokens": ["def", "pass"],
        "provenance": {
            "sourceFormat": "python_ast",
            "chunkingStrategy": "python_ast_node",
            "path": "broken.py",
        },
    }


def test_repair_lineage_marks_purified_node_as_active_replacement() -> None:
    broken = broken_chunk()
    gate = GateResult(
        key="",
        attemptKey=None,
        gate="py_compile",
        command=["python", "-m", "py_compile", "candidate.py"],
        passed=True,
        returncode=0,
        stdout="",
        stderr="",
        elapsedSeconds=0.01,
    )
    purified = purified_chunk_from_broken(
        broken,
        "def f():\n    return 1\n",
        representation="python",
        agent="codex",
        gate_result=gate,
    )
    attempt = build_repair_attempt(
        broken,
        purified,
        candidate_text=purified["text"],
        representation="python",
        agent="codex",
        gate_result=gate,
    )
    edges = build_lineage_edges(broken, attempt, purified, gate_result=gate)

    assert purified["_key"] != broken["_key"]
    assert purified["active"] is True
    assert purified["replacesNodeKey"] == broken["_key"]
    assert purified["provenance"]["repairOf"] == broken["_key"]
    assert purified["provenance"]["repairGatePassed"] is True
    assert attempt.status == "verified"
    assert gate.attemptKey == attempt.key
    assert any(edge["kind"] == "replaces" and edge["activeReplacement"] is True for edge in edges)
    assert any(edge["_from"] == "alexandria_chunks/chunk_broken" for edge in edges)


def test_repair_lineage_failure_preserves_broken_node_without_purified_successor() -> None:
    broken = broken_chunk()
    gate = GateResult(
        key="",
        attemptKey=None,
        gate="py_compile",
        command=["python", "-m", "py_compile", "candidate.py"],
        passed=False,
        returncode=1,
        stdout="",
        stderr="SyntaxError",
        elapsedSeconds=0.01,
    )
    attempt = build_repair_attempt(
        broken,
        None,
        candidate_text="def f(:\n    pass\n",
        representation="python",
        agent="codex",
        gate_result=gate,
    )
    edges = build_lineage_edges(broken, attempt, None, gate_result=gate)

    assert attempt.status == "failed"
    assert attempt.purifiedNodeKey is None
    assert attempt.errorDigest
    assert len(edges) == 1
    assert edges[0]["kind"] == "attempted_repair"
    assert edges[0]["_from"] == "alexandria_chunks/chunk_broken"


def test_repair_lineage_cli_appends_attempt_and_purified_chunk(tmp_path: Path) -> None:
    broken_path = tmp_path / "broken.json"
    candidate_path = tmp_path / "candidate.py"
    out = tmp_path / "out"
    broken_path.write_text(json.dumps(broken_chunk()), encoding="utf-8")
    candidate_path.write_text("def f():\n    return 1\n", encoding="utf-8")

    existing = {"_key": "chunk_existing", "text": "keep me"}
    out.mkdir()
    (out / "alexandria_chunks.jsonl").write_text(json.dumps(existing) + "\n", encoding="utf-8")

    subprocess.run(
        [
            sys.executable,
            str(REPAIR_LINEAGE),
            "--broken-node-json",
            str(broken_path),
            "--candidate",
            str(candidate_path),
            "--output-dir",
            str(out),
            "--representation",
            "python",
            "--agent",
            "codex",
            "--gate",
            "py_compile",
            "--command",
            sys.executable,
            "-m",
            "py_compile",
            str(candidate_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    chunks = [json.loads(line) for line in (out / "alexandria_chunks.jsonl").read_text().splitlines()]
    attempts = [json.loads(line) for line in (out / "alexandria_repair_attempts.jsonl").read_text().splitlines()]
    gates = [json.loads(line) for line in (out / "alexandria_repair_gate_results.jsonl").read_text().splitlines()]
    edges = [json.loads(line) for line in (out / "alexandria_repair_lineage_edges.jsonl").read_text().splitlines()]

    assert chunks[0] == existing
    assert len(chunks) == 2
    assert chunks[1]["active"] is True
    assert chunks[1]["replacesNodeKey"] == "chunk_broken"
    assert attempts[0]["status"] == "verified"
    assert gates[0]["passed"] is True
    assert gates[0]["attemptKey"] == attempts[0]["key"]
    assert any(edge["kind"] == "superseded_by" and edge["activeReplacement"] is True for edge in edges)
