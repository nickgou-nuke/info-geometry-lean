#!/usr/bin/env python3
"""Normalize SafeVerify target/submission verification into Hive telemetry.

SafeVerify compares compiled target/submission `.olean` files and checks that
submitted declarations implement the target declarations with matching kind,
type, and permitted value changes, while auditing axioms and unsafe/partial
definitions.  This bridge treats SafeVerify as an optional audit sidecar, not
as Lean proof authority or as a replacement for this repo's build gates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.hashing import stable_hash


SCHEMA = "info_geometry.safeverify_audit.v1"
SUMMARY_SCHEMA = "info_geometry.safeverify_audit.summary.v1"


def iter_json_docs(path: Path) -> Iterable[tuple[dict[str, Any], Path]]:
    if path.is_dir():
        for child in sorted(path.rglob("*.json")):
            yield from iter_json_docs(child)
        return
    if not path.exists() or path.suffix.lower() != ".json":
        return
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return
    if isinstance(payload, list):
        for row in payload:
            if isinstance(row, dict):
                yield row, path
    elif isinstance(payload, dict):
        rows = payload.get("outcomes")
        if isinstance(rows, list):
            for row in rows:
                if isinstance(row, dict):
                    yield row, path
        else:
            yield payload, path


def const_kind(info: Any) -> str:
    if not isinstance(info, dict):
        return ""
    const_info = info.get("constInfo")
    if isinstance(const_info, dict):
        return str(const_info.get("kind") or "")
    return ""


def axioms_of(info: Any) -> list[str]:
    if not isinstance(info, dict):
        return []
    axioms = info.get("axioms")
    if not isinstance(axioms, list):
        return []
    return [str(ax) for ax in axioms]


def normalize_safeverify_outcome(
    outcome: dict[str, Any],
    *,
    source_path: Path | None = None,
    target_olean: str | None = None,
    submission_olean: str | None = None,
    index: int = 0,
) -> dict[str, Any]:
    failure = outcome.get("failureMode")
    success = failure in {None, "", False}
    target_info = outcome.get("targetInfo")
    solution_info = outcome.get("solutionInfo")
    row = {
        "schema": SCHEMA,
        "id": "",
        "source": "safeverify",
        "source_path": str(source_path) if source_path else None,
        "target_olean": target_olean,
        "submission_olean": submission_olean,
        "success": bool(success),
        "failure_mode": None if success else str(failure),
        "target_kind": const_kind(target_info),
        "solution_kind": const_kind(solution_info),
        "target_axioms": axioms_of(target_info),
        "solution_axioms": axioms_of(solution_info),
        "target_info": target_info,
        "solution_info": solution_info,
        "raw": outcome,
        "authority": {
            "safeverify_is_audit_signal": True,
            "not_a_lean_kernel_proof_replacement": True,
            "lean_remains_proof_authority": True,
            "promotion_requires_hive_gates": True,
        },
    }
    row["id"] = stable_hash(
        {
            "source_path": str(source_path) if source_path else None,
            "target_olean": target_olean,
            "submission_olean": submission_olean,
            "index": index,
            "failure_mode": row["failure_mode"],
            "target_kind": row["target_kind"],
            "solution_kind": row["solution_kind"],
        }
    )
    return row


def write_outputs(
    rows: list[dict[str, Any]],
    output_dir: Path,
    *,
    input_ref: str | None = None,
    command: list[str] | None = None,
    returncode: int | None = None,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out = output_dir / "safeverify_audit.jsonl"
    with out.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    summary = {
        "schema": SUMMARY_SCHEMA,
        "input": input_ref,
        "output": str(out),
        "command": command or [],
        "returncode": returncode,
        "records": len(rows),
        "successes": sum(1 for row in rows if row["success"]),
        "failures": sum(1 for row in rows if not row["success"]),
        "failure_modes": sorted({str(row["failure_mode"]) for row in rows if row["failure_mode"]}),
    }
    (output_dir / "safeverify_audit_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return summary


def normalize_existing_reports(input_path: Path, output_dir: Path) -> dict[str, Any]:
    rows = [
        normalize_safeverify_outcome(outcome, source_path=source_path, index=idx)
        for idx, (outcome, source_path) in enumerate(iter_json_docs(input_path))
    ]
    return write_outputs(rows, output_dir, input_ref=str(input_path))


def run_safeverify(
    *,
    target_olean: Path,
    submission_olean: Path,
    output_dir: Path,
    repo_root: Path,
    safeverify_cmd: str,
    verbose: bool = False,
    disallow_partial: bool = False,
    timeout: int = 120,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    raw_json = output_dir / "safeverify_raw.json"
    command = [safeverify_cmd]
    if verbose:
        command.append("--verbose")
    if disallow_partial:
        command.append("--disallow-partial")
    command.extend(["--save", str(raw_json), str(target_olean), str(submission_olean)])
    proc = subprocess.run(
        command,
        cwd=repo_root,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    if raw_json.exists():
        rows = [
            normalize_safeverify_outcome(
                outcome,
                source_path=raw_json,
                target_olean=str(target_olean),
                submission_olean=str(submission_olean),
                index=idx,
            )
            for idx, (outcome, _source_path) in enumerate(iter_json_docs(raw_json))
        ]
    else:
        rows = [
            normalize_safeverify_outcome(
                {
                    "targetInfo": None,
                    "solutionInfo": None,
                    "failureMode": (proc.stderr or proc.stdout or f"SafeVerify exited {proc.returncode}").strip(),
                },
                target_olean=str(target_olean),
                submission_olean=str(submission_olean),
            )
        ]
    summary = write_outputs(
        rows,
        output_dir,
        input_ref=f"{target_olean}::{submission_olean}",
        command=command,
        returncode=proc.returncode,
    )
    (output_dir / "safeverify_stdout.txt").write_text(proc.stdout, encoding="utf-8")
    (output_dir / "safeverify_stderr.txt").write_text(proc.stderr, encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--input", type=Path, help="Existing SafeVerify --save JSON file or directory")
    mode.add_argument("--target-olean", type=Path, help="Target .olean file; requires --submission-olean")
    parser.add_argument("--submission-olean", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--safeverify-cmd", default=".lake/build/bin/safe_verify")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--disallow-partial", action="store_true")
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()

    if args.input:
        summary = normalize_existing_reports(args.input, args.output_dir)
    else:
        if not args.submission_olean:
            raise SystemExit("--submission-olean is required with --target-olean")
        summary = run_safeverify(
            target_olean=args.target_olean,
            submission_olean=args.submission_olean,
            output_dir=args.output_dir,
            repo_root=args.repo_root,
            safeverify_cmd=args.safeverify_cmd,
            verbose=args.verbose,
            disallow_partial=args.disallow_partial,
            timeout=args.timeout,
        )
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0 if int(summary["failures"]) == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
