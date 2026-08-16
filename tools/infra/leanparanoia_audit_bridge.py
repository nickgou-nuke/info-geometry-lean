#!/usr/bin/env python3
"""Normalize LeanParanoia proof-soundness audits into Hive telemetry.

LeanParanoia is an exploit-oriented Lean verification layer that can run checks
such as sorry/metavariable/unsafe/partial/axiom/native-computation/source-pattern
and environment replay checks.  This bridge keeps it optional and evidence-only:
Lean remains the proof authority, and Hive promotion still requires its normal
verification/build/audit gates.
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


SCHEMA = "info_geometry.leanparanoia_audit.v1"
SUMMARY_SCHEMA = "info_geometry.leanparanoia_audit.summary.v1"


def normalize_failure_map(value: Any) -> dict[str, list[str]]:
    if not isinstance(value, dict):
        return {}
    out: dict[str, list[str]] = {}
    for key, rows in value.items():
        if isinstance(rows, list):
            out[str(key)] = [str(row) for row in rows]
        elif rows:
            out[str(key)] = [str(rows)]
    return out


def finding_rows(failures: dict[str, list[str]]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for check_name, messages in sorted(failures.items()):
        for message in messages:
            rows.append(
                {
                    "check": check_name,
                    "message": message,
                    "severity": "error",
                }
            )
    return rows


def normalize_paranoia_payload(
    payload: dict[str, Any],
    *,
    theorem: str,
    command: list[str] | None = None,
    returncode: int | None = None,
    source_path: str | None = None,
) -> dict[str, Any]:
    failures = normalize_failure_map(payload.get("failures"))
    success = bool(payload.get("success")) and not failures and (returncode in {None, 0})
    findings = finding_rows(failures)
    row = {
        "schema": SCHEMA,
        "id": "",
        "source": "leanparanoia",
        "theorem": theorem,
        "success": success,
        "returncode": returncode,
        "command": command or [],
        "source_path": source_path,
        "failures": failures,
        "findings": findings,
        "finding_count": len(findings),
        "raw": payload,
        "authority": {
            "leanparanoia_is_audit_signal": True,
            "not_a_lean_kernel_proof": True,
            "lean_remains_proof_authority": True,
            "promotion_requires_hive_gates": True,
        },
    }
    row["id"] = stable_hash(
        {
            "theorem": theorem,
            "success": success,
            "returncode": returncode,
            "failures": failures,
        }
    )
    return row


def parse_json_from_stdout(stdout: str) -> dict[str, Any]:
    text = stdout.strip()
    if not text:
        return {"success": False, "failures": {"Bridge": ["LeanParanoia produced empty stdout"]}}
    try:
        payload = json.loads(text)
    except Exception:
        start = text.find("{")
        end = text.rfind("}")
        if start >= 0 and end > start:
            try:
                payload = json.loads(text[start : end + 1])
            except Exception as exc:  # noqa: BLE001
                return {"success": False, "failures": {"Bridge": [f"failed to parse LeanParanoia JSON: {exc}"]}}
        else:
            return {"success": False, "failures": {"Bridge": ["failed to locate LeanParanoia JSON object"]}}
    return payload if isinstance(payload, dict) else {"success": False, "failures": {"Bridge": ["LeanParanoia JSON root is not an object"]}}


def run_paranoia(
    theorem: str,
    *,
    repo_root: Path,
    lake_exe: str = "lake",
    extra_args: list[str] | None = None,
    timeout: int = 120,
) -> dict[str, Any]:
    command = [lake_exe, "exe", "paranoia", *(extra_args or []), theorem]
    try:
        proc = subprocess.run(
            command,
            cwd=repo_root,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001
        payload = {"success": False, "failures": {"Bridge": [repr(exc)]}}
        return normalize_paranoia_payload(payload, theorem=theorem, command=command, returncode=None)
    payload = parse_json_from_stdout(proc.stdout)
    if proc.returncode != 0 and not payload.get("failures"):
        payload = {
            **payload,
            "success": False,
            "failures": {"LeanParanoiaProcess": [(proc.stderr or proc.stdout or f"exit {proc.returncode}").strip()]},
        }
    return normalize_paranoia_payload(payload, theorem=theorem, command=command, returncode=proc.returncode)


def iter_payloads(path: Path) -> Iterable[tuple[dict[str, Any], Path]]:
    if path.is_dir():
        for child in sorted(path.rglob("*.json")):
            yield from iter_payloads(child)
        return
    if not path.exists() or path.suffix.lower() != ".json":
        return
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return
    if isinstance(payload, dict):
        yield payload, path
    elif isinstance(payload, list):
        for row in payload:
            if isinstance(row, dict):
                yield row, path


def normalize_existing_reports(input_path: Path, output_dir: Path, *, theorem_fallback: str = "") -> dict[str, Any]:
    rows = []
    for payload, source_path in iter_payloads(input_path):
        theorem = str(payload.get("theorem") or payload.get("declaration") or theorem_fallback or source_path.stem)
        rows.append(
            normalize_paranoia_payload(
                payload,
                theorem=theorem,
                source_path=str(source_path),
            )
        )
    return write_outputs(rows, output_dir, input_ref=str(input_path))


def write_outputs(rows: list[dict[str, Any]], output_dir: Path, *, input_ref: str | None = None) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    out = output_dir / "leanparanoia_audit.jsonl"
    with out.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    summary = {
        "schema": SUMMARY_SCHEMA,
        "input": input_ref,
        "output": str(out),
        "records": len(rows),
        "successes": sum(1 for row in rows if row["success"]),
        "failures": sum(1 for row in rows if not row["success"]),
        "findings": sum(int(row["finding_count"]) for row in rows),
    }
    summary_path = output_dir / "leanparanoia_audit_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--theorem", help="Run `lake exe paranoia <theorem>` and normalize its JSON output")
    mode.add_argument("--input", type=Path, help="Normalize existing LeanParanoia JSON file or directory")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--lake-exe", default="lake")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--paranoia-arg", action="append", default=[], help="Extra argument passed before theorem")
    args = parser.parse_args()

    if args.theorem:
        row = run_paranoia(
            args.theorem,
            repo_root=args.repo_root,
            lake_exe=args.lake_exe,
            extra_args=list(args.paranoia_arg or []),
            timeout=args.timeout,
        )
        summary = write_outputs([row], args.output_dir, input_ref=args.theorem)
    else:
        summary = normalize_existing_reports(args.input, args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0 if int(summary["failures"]) == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
