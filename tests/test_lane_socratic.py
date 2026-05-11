from __future__ import annotations

import json
from pathlib import Path

from tools.infra.lanes.lane_socratic import run as run_socratic


def write_json(path: Path, payload: dict | list) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=True, sort_keys=True), encoding="utf-8")


def read_jsonl(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            raw = raw.strip()
            if not raw:
                continue
            rows.append(json.loads(raw))
    return rows


def test_lane_socratic_marks_open_questions_as_soft_failures(tmp_path: Path) -> None:
    input_path = tmp_path / "socratic.jsonl"
    output_path = tmp_path / "out.jsonl"
    input_path.write_text(
        "\n".join(
            [
                json.dumps(
                    {
                        "schema": "info_geometry.hive_packet.v1",
                        "kind": "SocraticQuestionPacket",
                        "id": "socratic:InfoGeometry.Canonical.SomeTheorem",
                        "status": "open",
                        "authority": "semantic",
                        "question": "Where is the missing hypothesis?",
                        "question_type": "missing_hypothesis",
                        "target_packet_ids": ["InfoGeometry.Canonical.SomeTheorem"],
                    },
                    sort_keys=True,
                    ensure_ascii=True,
                ),
                json.dumps(
                    {
                        "schema": "info_geometry.hive_packet.v1",
                        "kind": "SocraticQuestionPacket",
                        "id": "socratic:InfoGeometry.Canonical.Done",
                        "status": "answered",
                        "authority": "semantic",
                        "question": "Can we close this route?",
                        "question_type": "counterexample_pressure",
                        "target_packet_ids": ["InfoGeometry.Canonical.Done"],
                    },
                    sort_keys=True,
                    ensure_ascii=True,
                ),
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    summary = run_socratic(input_path, output_path)
    assert summary["records"] == 2
    assert summary["failed"] == 1

    rows = read_jsonl(output_path)
    by_decl = {row["decl"]: row for row in rows}
    assert by_decl["InfoGeometry.Canonical.SomeTheorem"]["ok"] is False
    assert by_decl["InfoGeometry.Canonical.Done"]["ok"] is True
    assert by_decl["InfoGeometry.Canonical.SomeTheorem"]["lane"] == "bee_socratic"
    assert "status:open" in by_decl["InfoGeometry.Canonical.SomeTheorem"]["checks"]
