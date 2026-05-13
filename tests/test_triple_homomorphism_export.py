import json
import subprocess
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def read_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def run_checker(tmp_path: Path, target_rows: list[dict]) -> tuple[subprocess.CompletedProcess, dict, list[dict]]:
    source = tmp_path / "source.jsonl"
    target = tmp_path / "target.jsonl"
    maps = tmp_path / "maps.jsonl"
    audit = tmp_path / "audit.json"
    missing = tmp_path / "missing.jsonl"

    write_jsonl(
        source,
        [
            {"subject": "expr_1", "predicate": "bound_by", "object": "binder_1"},
            {"subject": "expr_1", "predicate": "uses_const", "object": "Nat.add"},
        ],
    )
    write_jsonl(target, target_rows)
    write_jsonl(
        maps,
        [
            {"kind": "object", "source": "expr_1", "target": "expr_A"},
            {"kind": "object", "source": "binder_1", "target": "binder_A"},
            {"kind": "object", "source": "Nat.add", "target": "Nat.add"},
            {"kind": "relation", "source": "bound_by", "target": "bound_by"},
            {"kind": "relation", "source": "uses_const", "target": "uses_const"},
        ],
    )

    result = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            "--run",
            "lean/DAG/TripleHomomorphismExport.lean",
            str(source),
            str(target),
            str(maps),
            str(audit),
            str(missing),
        ],
        cwd=REPO,
        check=False,
    )
    return result, read_json(audit), read_jsonl(missing)


def test_triple_homomorphism_export_accepts_preserved_triples(tmp_path: Path) -> None:
    result, audit, missing = run_checker(
        tmp_path,
        [
            {"subject": "expr_A", "predicate": "bound_by", "object": "binder_A"},
            {"subject": "expr_A", "predicate": "uses_const", "object": "Nat.add"},
        ],
    )

    assert result.returncode == 0
    assert audit["leanVerified"] is True
    assert audit["checkedTriples"] == 2
    assert audit["preservedTriples"] == 2
    assert audit["missingTriples"] == 0
    assert audit["verificationTier"] == "lean_native_finite_triple_homomorphism"
    assert missing == []


def test_triple_homomorphism_export_reports_missing_mapped_triples(tmp_path: Path) -> None:
    result, audit, missing = run_checker(
        tmp_path,
        [
            {"subject": "expr_A", "predicate": "bound_by", "object": "binder_A"},
        ],
    )

    assert result.returncode == 2
    assert audit["leanVerified"] is False
    assert audit["checkedTriples"] == 2
    assert audit["preservedTriples"] == 1
    assert audit["missingTriples"] == 1
    assert missing == [
        {
            "subject": "expr_1",
            "predicate": "uses_const",
            "object": "Nat.add",
            "mappedSubject": "expr_A",
            "mappedPredicate": "uses_const",
            "mappedObject": "Nat.add",
        }
    ]
