import json
import subprocess
import sys
from pathlib import Path

from tools.infra.hive_multichecker_merge import merge_reports


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "hive_multichecker_merge.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("\n".join(json.dumps(row) for row in rows) + "\n", encoding="utf-8")


def test_merge_reports_combines_checker_rows(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    paranoia = tmp_path / "paranoia.jsonl"
    safe = tmp_path / "safe.jsonl"
    auto = tmp_path / "auto.jsonl"
    gate = tmp_path / "gate.json"

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(paranoia, [{"theorem": "Demo.ok", "success": True, "findings": [], "id": "p1"}])
    write_jsonl(
        safe,
        [
            {
                "declaration": "Demo.ok",
                "success": False,
                "failure_mode": "type mismatch",
                "id": "s1",
            }
        ],
    )
    write_jsonl(
        auto,
        [
            {
                "id": "a1",
                "problems": [
                    {"name": "Demo.ok", "passed": True, "earned": 1, "points": 1},
                    {"name": "Demo.extra", "passed": False, "earned": 0, "points": 2, "message": "bad"},
                ],
            }
        ],
    )
    gate.write_text(json.dumps({"spec_id": "spec", "submission_id": "sub", "promotion_allowed": True, "violations": []}), encoding="utf-8")

    report = merge_reports(
        decl_paths=[decls],
        leanparanoia_path=paranoia,
        safeverify_path=safe,
        autograder_path=auto,
        promotion_path=gate,
    )

    by_decl = {row["decl"]: row for row in report["declarations"]}
    assert by_decl["Demo.ok"]["ok"] is False
    assert by_decl["Demo.ok"]["tools"]["leanparanoia"]["ok"] is True
    assert by_decl["Demo.ok"]["tools"]["safeverify"]["ok"] is False
    assert by_decl["Demo.ok"]["score"] == {"earned": 1.0, "total": 1.0}
    assert by_decl["Demo.extra"]["tools"]["autograder"]["ok"] is False
    assert report["summary"]["by_tool"]["safeverify"]["failed"] == 1


def test_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    paranoia = tmp_path / "paranoia.jsonl"
    out = tmp_path / "report.json"
    md = tmp_path / "report.md"
    write_jsonl(decls, [{"name": "Demo.ok"}])
    write_jsonl(paranoia, [{"theorem": "Demo.ok", "success": True, "findings": [], "id": "p1"}])

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--decls",
            str(decls),
            "--leanparanoia-jsonl",
            str(paranoia),
            "--json-out",
            str(out),
            "--md-out",
            str(md),
        ],
        cwd=REPO,
        check=False,
    )

    assert proc.returncode == 0
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["schema"] == "info_geometry.hive_multichecker_report.v1"
    assert report["summary"]["passed_all"] == 1
    assert "Hive Multi-Checker Report" in md.read_text(encoding="utf-8")
