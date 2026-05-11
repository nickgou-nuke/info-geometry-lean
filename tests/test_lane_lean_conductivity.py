from __future__ import annotations

import json
from pathlib import Path

from tools.infra.lanes.lane_lean_conductivity import run as run_conductivity


def write_json(path: Path, payload: dict | list) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=True, sort_keys=True), encoding="utf-8")


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("\n".join(json.dumps(row) for row in rows) + "\n", encoding="utf-8")


def read_jsonl(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            raw = raw.strip()
            if not raw:
                continue
            rows.append(json.loads(raw))
    return rows


def test_lean_conductivity_reads_representation_depth_report_rows(tmp_path: Path) -> None:
    input_path = tmp_path / "input.json"
    output_path = tmp_path / "out.jsonl"
    write_json(
        input_path,
        {
            "schema": "info_geometry.representation_depth_from_graph.v1",
            "declarations": [
                {
                    "name": "Demo.ok",
                    "module": "Demo",
                    "kind": "theorem",
                    "depth": "operator",
                    "depthNat": 2,
                    "targetDepthNat": 2,
                    "directTaggedDepCount": 1,
                    "judgment": "vertical",
                    "reachesAboveDirect": False,
                    "reachesBelowPrevDirect": False,
                    "reachesAboveClosure": False,
                    "reachesBelowPrevClosure": False,
                },
                {
                    "name": "Demo.bad",
                    "module": "Demo",
                    "kind": "theorem",
                    "depth": "operator",
                    "depthNat": 2,
                    "targetDepthNat": 2,
                    "directTaggedDepCount": 3,
                    "judgment": "wormhole",
                    "reachesAboveDirect": True,
                    "reachesBelowPrevDirect": False,
                    "reachesAboveClosure": True,
                    "reachesBelowPrevClosure": False,
                },
            ],
        },
    )

    summary = run_conductivity(input_path, output_path)
    assert summary["records"] == 2
    assert summary["failed"] == 1

    rows = read_jsonl(output_path)
    by_decl = {row["decl"]: row for row in rows}
    assert by_decl["Demo.ok"]["lane"] == "bee_lean_conductivity"
    assert by_decl["Demo.ok"]["ok"] is True
    assert by_decl["Demo.ok"]["score"] == {"earned": 1.0, "total": 1.0}
    assert by_decl["Demo.bad"]["ok"] is False


def test_lean_conductivity_reads_jsonl_rows(tmp_path: Path) -> None:
    input_path = tmp_path / "input.jsonl"
    output_path = tmp_path / "out.jsonl"
    write_jsonl(
        input_path,
        [
            {
                "name": "Demo.depth0",
                "module": "Demo",
                "targetDepthNat": 0,
                "directTaggedDepCount": 0,
                "judgment": "vertical",
            }
        ],
    )

    summary = run_conductivity(input_path, output_path)
    assert summary["records"] == 1
    assert summary["failed"] == 0
    rows = read_jsonl(output_path)
    assert rows[0]["decl"] == "Demo.depth0"
    assert rows[0]["ok"] is True
