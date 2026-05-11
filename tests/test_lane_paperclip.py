from __future__ import annotations

import json
from pathlib import Path

from tools.infra.lanes.lane_paperclip import run as run_paperclip


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


def test_lane_paperclip_marks_blocking_controls_as_failures(tmp_path: Path) -> None:
    input_path = tmp_path / "paperclip.jsonl"
    output_path = tmp_path / "out.jsonl"
    write_json(
        input_path,
        [
            {
                "schema": "info_geometry.paperclip.v1",
                "source": "paperclip",
                "status": "blocked",
                "theorem": "Demo.blocked",
                "message": "Control lane flagged unresolved uncertainty.",
                "targets": ["Demo.blocked"],
            },
            {
                "schema": "info_geometry.paperclip.v1",
                "source": "paperclip",
                "status": "resolved",
                "declaration": "Demo.ok",
                "message": "All checks complete.",
            },
        ],
    )

    summary = run_paperclip(input_path, output_path)
    assert summary["records"] == 2
    assert summary["failed"] == 1

    rows = read_jsonl(output_path)
    by_decl = {row["decl"]: row for row in rows}
    assert by_decl["Demo.blocked"]["lane"] == "bee_paperclip"
    assert by_decl["Demo.blocked"]["ok"] is False
    assert by_decl["Demo.ok"]["ok"] is True
    assert by_decl["Demo.ok"]["evidence"][0]["declaration"] == "Demo.ok"


def test_lane_paperclip_parses_single_object_payload(tmp_path: Path) -> None:
    input_path = tmp_path / "paperclip_single.json"
    output_path = tmp_path / "out.jsonl"
    input_path.write_text(
        json.dumps(
            {
                "schema": "info_geometry.paperclip.v1",
                "source": "paperclip",
                "status": "blocked",
                "target_decl": "Demo.blocked",
                "target_name": "Demo.blocked",
                "message": "single payload should parse",
            }
        ),
        encoding="utf-8",
    )

    summary = run_paperclip(input_path, output_path)
    assert summary["records"] == 1
    assert summary["failed"] == 1

    rows = read_jsonl(output_path)
    assert len(rows) == 1
    assert rows[0]["lane"] == "bee_paperclip"
    assert rows[0]["decl"] == "Demo.blocked"
    assert rows[0]["ok"] is False
