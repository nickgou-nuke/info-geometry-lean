import json
import subprocess
import sys
from pathlib import Path

from tools.infra.rethlas_verification_bridge import normalize_rethlas_payload, run_bridge, validate_rethlas_payload


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "rethlas_verification_bridge.py"


def _wrong_payload() -> dict:
    return {
        "verification_report": {
            "summary": "The proof skips a key implication.",
            "critical_errors": [{"location": "Lemma 1", "issue": "Uses a theorem without its hypotheses."}],
            "gaps": [{"location": "Main theorem", "issue": "Final implication is not justified."}],
        },
        "verdict": "wrong",
        "repair_hints": "Add the missing hypotheses and prove the final implication.",
    }


def test_validate_rethlas_payload_enforces_verdict_contract() -> None:
    assert validate_rethlas_payload(_wrong_payload()) == []

    bad = {
        "verification_report": {"summary": "", "critical_errors": [], "gaps": []},
        "verdict": "wrong",
        "repair_hints": "",
    }
    errors = validate_rethlas_payload(bad)
    assert "verdict='wrong' requires at least one critical error or gap" in errors
    assert "repair_hints must be non-empty when verdict='wrong'" in errors


def test_normalize_rethlas_payload_marks_audit_not_proof(tmp_path: Path) -> None:
    source = tmp_path / "verification.json"

    row = normalize_rethlas_payload(_wrong_payload(), source)

    assert row["schema"] == "info_geometry.rethlas_verification_report.v1"
    assert row["valid_contract"] is True
    assert row["finding_count"] == 2
    assert row["authority"]["nl_verification_is_audit_signal"] is True
    assert row["authority"]["lean_remains_proof_authority"] is True


def test_rethlas_verification_bridge_cli_writes_summary(tmp_path: Path) -> None:
    src_dir = tmp_path / "results" / "run1"
    out = tmp_path / "out"
    src_dir.mkdir(parents=True)
    (src_dir / "verification.json").write_text(json.dumps(_wrong_payload()), encoding="utf-8")

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(tmp_path / "results"),
            "--output-dir",
            str(out),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    rows = (out / "rethlas_verification_bridge.jsonl").read_text(encoding="utf-8").splitlines()
    summary = json.loads((out / "rethlas_verification_bridge_summary.json").read_text(encoding="utf-8"))
    assert len(rows) == 1
    assert summary["records"] == 1
    assert summary["wrong_verdicts"] == 1
    assert summary["findings"] == 2


def test_run_bridge_counts_invalid_contracts(tmp_path: Path) -> None:
    src = tmp_path / "verification.json"
    out = tmp_path / "out"
    src.write_text(
        json.dumps(
            {
                "verification_report": {"summary": "", "critical_errors": [], "gaps": []},
                "verdict": "wrong",
                "repair_hints": "",
            }
        ),
        encoding="utf-8",
    )

    summary = run_bridge(src, out)

    assert summary["records"] == 1
    assert summary["valid_contracts"] == 0
