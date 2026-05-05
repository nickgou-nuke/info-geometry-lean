import json
import subprocess
import sys
from pathlib import Path

from tools.infra.leanparanoia_audit_bridge import normalize_paranoia_payload


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "leanparanoia_audit_bridge.py"


def test_normalize_paranoia_payload_flattens_failures() -> None:
    row = normalize_paranoia_payload(
        {
            "success": False,
            "failures": {
                "CustomAxioms": ["Uses disallowed axiom: Lean.trustCompiler"],
                "Replay": ["Replay verification failed"],
            },
        },
        theorem="Demo.bad",
        command=["lake", "exe", "paranoia", "Demo.bad"],
        returncode=2,
    )

    assert row["schema"] == "info_geometry.leanparanoia_audit.v1"
    assert row["success"] is False
    assert row["finding_count"] == 2
    assert row["findings"][0]["check"] == "CustomAxioms"
    assert row["authority"]["lean_remains_proof_authority"] is True


def test_cli_normalizes_existing_json_report(tmp_path: Path) -> None:
    report = tmp_path / "paranoia.json"
    out = tmp_path / "out"
    report.write_text(
        json.dumps(
            {
                "theorem": "Demo.ok",
                "success": True,
                "failures": {},
            }
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(report),
            "--output-dir",
            str(out),
        ],
        cwd=REPO,
        check=False,
    )

    assert proc.returncode == 0
    rows = (out / "leanparanoia_audit.jsonl").read_text(encoding="utf-8").splitlines()
    summary = json.loads((out / "leanparanoia_audit_summary.json").read_text(encoding="utf-8"))
    assert len(rows) == 1
    assert summary["successes"] == 1
