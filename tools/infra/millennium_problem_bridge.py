#!/usr/bin/env python3
"""Build local retrieval records for LeanMillenniumPrizeProblems.

The LeanMillenniumPrizeProblems repo is a statement corpus, not a solution
corpus.  This bridge indexes its problem statements as external context records
for local retrieval/Hive prompts without importing the external Lean project.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.leansearch_local import tokenize


SCHEMA = "info_geometry.millennium_problem_record.v1"
SUMMARY_SCHEMA = "info_geometry.millennium_problem_bridge.summary.v1"


DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:def|theorem|structure|class|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
STATUS_ROW_RE = re.compile(
    r"^\|\s*(?P<problem>[^|]+?)\s*\|\s*`(?P<statement>[^`]+)`\s*\|\s*`(?P<location>[^`]+)`\s*\|\s*(?P<status>[^|]+?)\s*\|\s*(?P<fidelity>[^|]+?)\s*\|"
)


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        if needle in line:
            return idx
    return None


def extract_status_table(readme: Path) -> dict[str, dict[str, str]]:
    if not readme.exists():
        return {}
    out: dict[str, dict[str, str]] = {}
    for line in readme.read_text(encoding="utf-8").splitlines():
        m = STATUS_ROW_RE.match(line)
        if not m:
            continue
        problem = m.group("problem").strip()
        if problem == "Problem":
            continue
        out[problem] = {
            "problem": problem,
            "main_statement": m.group("statement").strip(),
            "location": m.group("location").strip(),
            "status": m.group("status").strip(),
            "clay_fidelity": m.group("fidelity").strip(),
        }
    return out


def extract_declarations(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    decls = []
    for idx, line in enumerate(text.splitlines(), start=1):
        m = DECL_RE.match(line)
        if not m:
            continue
        kind = line.strip().split()[0]
        if kind == "noncomputable":
            kind = line.strip().split()[1]
        decls.append(
            {
                "name": m.group(1),
                "kind": kind,
                "line": idx,
                "snippet": line.strip(),
            }
        )
    return decls


def problem_from_path(path: Path) -> str:
    parts = path.parts
    if "Problems" in parts:
        idx = parts.index("Problems")
        if idx + 1 < len(parts):
            return parts[idx + 1]
    return path.parent.name


def make_record(*, repo_root: Path, lean_file: Path, decl: dict[str, Any], status_by_problem: dict[str, dict[str, str]]) -> dict[str, Any]:
    rel = lean_file.relative_to(repo_root)
    problem_key = problem_from_path(rel)
    status_by_folder = {
        problem_from_path(Path(row["location"])): row
        for row in status_by_problem.values()
    }
    status = next(
        (row for row in status_by_problem.values() if row["location"] == str(rel)),
        None,
    ) or status_by_folder.get(problem_key)
    problem = status["problem"] if status else problem_key
    statement = status["main_statement"] if status else decl["name"]
    doc = (
        f"Lean Millennium Prize Problem statement context for {problem}. "
        f"Main statement: {statement}."
    )
    if status:
        doc += f" Status: {status['status']}. Clay fidelity: {status['clay_fidelity']}."
    full_name = decl["name"]
    if "." not in full_name and status and "." in statement:
        namespace = statement.rsplit(".", 1)[0]
        full_name = f"{namespace}.{full_name}"
    text_for_tokens = " ".join(
        [
            problem,
            statement,
            full_name,
            decl["snippet"],
            doc,
            str(rel),
        ]
    )
    return {
        "schema": SCHEMA,
        "name": full_name,
        "kind": decl["kind"],
        "module": str(rel).removesuffix(".lean").replace("/", "."),
        "file": str(lean_file),
        "line": decl["line"],
        "doc": doc,
        "type": "external_millennium_statement_context",
        "snippet": decl["snippet"],
        "nameTokens": tokenize(full_name),
        "searchTokens": tokenize(text_for_tokens),
        "external": {
            "source": "lean-dojo/LeanMillenniumPrizeProblems",
            "problem": problem,
            "main_statement": statement,
            "status": status["status"] if status else "unknown",
            "clay_fidelity": status["clay_fidelity"] if status else "unknown",
            "imported_into_current_repo": False,
            "context_only": True,
        },
        "authority": {
            "external_record_is_retrieval_context": True,
            "not_a_proof_in_current_repo": True,
            "lean_remains_proof_authority": True,
        },
    }


def build_records(repo_root: Path) -> list[dict[str, Any]]:
    status = extract_status_table(repo_root / "README.md")
    records: list[dict[str, Any]] = []
    for lean_file in sorted((repo_root / "Problems").rglob("*.lean")):
        for decl in extract_declarations(lean_file):
            records.append(make_record(repo_root=repo_root, lean_file=lean_file, decl=decl, status_by_problem=status))
    return records


def run_bridge(repo_root: Path, output_dir: Path) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    records = build_records(repo_root)
    out = output_dir / "millennium_problem_records.jsonl"
    with out.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=True, sort_keys=True) + "\n")
    by_problem: dict[str, int] = {}
    for record in records:
        problem = record["external"]["problem"]
        by_problem[problem] = by_problem.get(problem, 0) + 1
    summary = {
        "schema": SUMMARY_SCHEMA,
        "repo_root": str(repo_root),
        "output": str(out),
        "records": len(records),
        "by_problem": dict(sorted(by_problem.items())),
    }
    summary_path = output_dir / "millennium_problem_bridge_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("external_refs/LeanMillenniumPrizeProblems"))
    parser.add_argument("--output-dir", type=Path, default=Path("artifacts/millennium_problems"))
    args = parser.parse_args()
    summary = run_bridge(args.repo_root, args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
