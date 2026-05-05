import json
import subprocess
import sys
from pathlib import Path

from tools.infra.aria_scorer_lite import extract_lean_identifiers, score_alignment


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "aria_scorer_lite.py"


def _write_records(path: Path) -> None:
    rows = [
        {
            "schema": "info_geometry.leansearch_local.record.v1",
            "name": "InfoGeometry.Canonical.PositiveRay",
            "kind": "structure",
            "module": "InfoGeometry.Canonical",
            "file": "lean/InfoGeometry/Canonical/PositiveRay.lean",
            "line": 10,
            "doc": "Positive projective ray for scale-invariant geometry.",
            "type": "Type",
            "snippet": "structure PositiveRay where",
            "nameTokens": ["positive", "ray"],
            "searchTokens": ["positive", "projective", "ray", "scale", "invariant", "geometry"],
        }
    ]
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_extract_lean_identifiers_skips_keywords() -> None:
    code = "theorem t : InfoGeometry.Canonical.PositiveRay := by sorry"

    identifiers = extract_lean_identifiers(code)

    assert "InfoGeometry.Canonical.PositiveRay" in identifiers
    assert "theorem" not in identifiers
    assert "by" not in identifiers
    assert "sorry" not in identifiers


def test_score_alignment_exact_grounds_identifier(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    _write_records(records)

    payload = score_alignment(
        informal_statement="A positive projective ray exists.",
        agent_output="theorem t : InfoGeometry.Canonical.PositiveRay := by sorry",
        records=records,
    )

    assert payload["schema"] == "info_geometry.aria_scorer_lite.v1"
    assert payload["authority"]["not_a_proof"] is True
    assert payload["authority"]["lean_remains_proof_authority"] is True
    assert payload["grounded_terms"][0]["grounding"] == "InfoGeometry.Canonical.PositiveRay"
    assert payload["grounded_terms"][0]["method"] == "exact_record_name"


def test_aria_scorer_lite_cli_writes_report(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    out = tmp_path / "score.json"
    _write_records(records)

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--informal-statement",
            "A positive projective ray exists.",
            "--agent-output",
            "theorem t : InfoGeometry.Canonical.PositiveRay := by sorry",
            "--records",
            str(records),
            "--out",
            str(out),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["semantic_status"] in {"match", "partial"}
    assert payload["grounding_coverage"] > 0
