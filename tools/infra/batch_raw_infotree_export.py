#!/usr/bin/env python3
"""Batch RawInfoTree export with LeanDojo-style safety gates.

The single-file Lean exporter is intentionally final-forest based: it runs the
frontend, then walks ``commandState.infoState.trees`` so tactic surfaces are not
missed. That is the right compiler-memory source, but it must not be driven over
a real codebase as one opaque giant job.

This wrapper runs the exporter per file, validates each per-file artifact, and
merges only validated rows into a combined export directory. Failed or timed-out
files remain explicit in the manifest instead of poisoning the merged graph.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
EXPORTER = ROOT / "lean" / "DAG" / "RawInfoTreeExport.lean"
VALIDATOR = ROOT / "tools" / "infra" / "validate_raw_infotree_export.py"

JSONL_FILES = [
    "raw_infotree_roots.jsonl",
    "raw_infotree_nodes.jsonl",
    "raw_infotree_edges.jsonl",
    "raw_infotree_contexts.jsonl",
    "raw_infotree_payloads.jsonl",
    "raw_infotree_payload_fields.jsonl",
    "raw_infotree_decl_links.jsonl",
    "raw_infotree_env_refs.jsonl",
    "raw_infotree_mctx_refs.jsonl",
    "raw_infotree_mctx_decls.jsonl",
    "raw_infotree_lctx_refs.jsonl",
    "raw_infotree_lctx_decls.jsonl",
    "raw_infotree_projection_leakage.jsonl",
]


@dataclass(frozen=True)
class FileResult:
    file: str
    out_dir: str
    status: str
    returncode: int | None
    duration_sec: float
    validation: dict[str, Any] | None
    stdout_tail: str
    stderr_tail: str


def tail_text(text: str, limit: int = 8000) -> str:
    return text[-limit:] if len(text) > limit else text


def safe_slug(path: Path) -> str:
    text = str(path)
    return "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in text)


def olean_path_for(path: Path) -> Path | None:
    try:
        rel = path.resolve().relative_to((ROOT / "lean").resolve())
    except ValueError:
        return None
    return ROOT / ".lake" / "build" / "lib" / "lean" / rel.with_suffix(".olean")


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            yield row


def jsonl_count(path: Path) -> int:
    return sum(1 for _ in iter_jsonl(path))


def discover_files(args: argparse.Namespace) -> list[Path]:
    files: list[Path] = []
    for item in args.files:
        files.append(Path(item))
    if args.file_list:
        for line in args.file_list.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line and not line.startswith("#"):
                files.append(Path(line))
    for root in args.roots:
        root_path = Path(root)
        if root_path.is_file() and root_path.suffix == ".lean":
            files.append(root_path)
        elif root_path.is_dir():
            files.extend(sorted(root_path.rglob("*.lean")))
    seen: set[str] = set()
    result: list[Path] = []
    for path in files:
        if not path.is_absolute():
            path = ROOT / path
        try:
            rel = str(path.resolve().relative_to(ROOT))
        except ValueError:
            rel = str(path.resolve())
        if rel not in seen:
            seen.add(rel)
            result.append(path)
    if args.limit is not None:
        result = result[: max(0, args.limit)]
    return result


def validate_export(out_dir: Path) -> tuple[int, dict[str, Any], str, str]:
    proc = subprocess.run(
        [sys.executable, str(VALIDATOR), "--input-dir", str(out_dir)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    try:
        report = json.loads(proc.stdout)
    except json.JSONDecodeError:
        report = {
            "ok": False,
            "errors": ["validator did not emit JSON"],
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
    return proc.returncode, report, proc.stdout, proc.stderr


def export_one(
    path: Path,
    per_file_dir: Path,
    timeout_sec: int,
    lake: str,
    *,
    require_olean: bool,
) -> FileResult:
    start = time.monotonic()
    olean_path = olean_path_for(path)
    if require_olean and (olean_path is None or not olean_path.exists()):
        return FileResult(
            file=str(path),
            out_dir=str(per_file_dir),
            status="missing_olean",
            returncode=None,
            duration_sec=time.monotonic() - start,
            validation=None,
            stdout_tail="",
            stderr_tail=f"corresponding .olean not found: {olean_path}",
        )
    if per_file_dir.exists():
        shutil.rmtree(per_file_dir)
    per_file_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        lake,
        "env",
        "lean",
        "--run",
        str(EXPORTER.relative_to(ROOT)),
        str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path),
        str(per_file_dir.relative_to(ROOT) if per_file_dir.is_relative_to(ROOT) else per_file_dir),
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired as exc:
        return FileResult(
            file=str(path),
            out_dir=str(per_file_dir),
            status="timeout",
            returncode=None,
            duration_sec=time.monotonic() - start,
            validation=None,
            stdout_tail=tail_text(exc.stdout or ""),
            stderr_tail=tail_text(exc.stderr or ""),
        )
    if proc.returncode != 0:
        return FileResult(
            file=str(path),
            out_dir=str(per_file_dir),
            status="export_failed",
            returncode=proc.returncode,
            duration_sec=time.monotonic() - start,
            validation=None,
            stdout_tail=tail_text(proc.stdout),
            stderr_tail=tail_text(proc.stderr),
        )
    validation_rc, validation, validation_stdout, validation_stderr = validate_export(per_file_dir)
    status = "ok" if validation_rc == 0 and validation.get("ok") is True else "validation_failed"
    return FileResult(
        file=str(path),
        out_dir=str(per_file_dir),
        status=status,
        returncode=proc.returncode,
        duration_sec=time.monotonic() - start,
        validation=validation,
        stdout_tail=tail_text(proc.stdout + validation_stdout),
        stderr_tail=tail_text(proc.stderr + validation_stderr),
    )


def merge_valid_exports(valid_dirs: list[Path], merged_dir: Path) -> dict[str, Any]:
    if merged_dir.exists():
        shutil.rmtree(merged_dir)
    merged_dir.mkdir(parents=True, exist_ok=True)
    counts: dict[str, int] = {}
    for name in JSONL_FILES:
        out_path = merged_dir / name
        total = 0
        with out_path.open("w", encoding="utf-8") as out:
            for export_dir in valid_dirs:
                in_path = export_dir / name
                with in_path.open("r", encoding="utf-8") as src:
                    for line in src:
                        if line.strip():
                            out.write(line)
                            total += 1
        counts[name] = total

    metadata_rows = [
        json.loads((export_dir / "metadata.json").read_text(encoding="utf-8"))
        for export_dir in valid_dirs
    ]
    merged_metadata = {
        "schema": "info_geometry.raw_infotree_batch_export.v1",
        "stage": "stage_2_tactic_lctx_bridge_batch",
        "file_count": len(valid_dirs),
        "fully_lossless": False,
        "loss_audited": True,
        "source_metadata": metadata_rows,
        "counts": counts,
    }
    (merged_dir / "metadata.json").write_text(
        json.dumps(merged_metadata, indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )
    return merged_metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", help="Lean files to export.")
    parser.add_argument("--root", dest="roots", action="append", default=[], help="Directory or file to scan; repeatable.")
    parser.add_argument("--file-list", type=Path, help="Newline-delimited file list.")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "artifacts" / "infotree" / "raw-infotree-batch")
    parser.add_argument("--timeout-sec", type=int, default=120)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--lake", default="/home/goutev/.elan/bin/lake")
    parser.add_argument("--allow-failures", action="store_true")
    parser.add_argument(
        "--allow-missing-olean",
        action="store_true",
        help="Disable the LeanDojo-style build gate. Use only for synthetic probes.",
    )
    parser.add_argument("--no-merge", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    files = discover_files(args)
    if not files:
        print("No Lean files selected.", file=sys.stderr)
        return 1

    output_dir = args.output_dir.resolve()
    per_file_root = output_dir / "per_file"
    merged_dir = output_dir / "merged"
    per_file_root.mkdir(parents=True, exist_ok=True)

    results: list[FileResult] = []
    for idx, path in enumerate(files):
        if not path.exists():
            results.append(
                FileResult(
                    file=str(path),
                    out_dir="",
                    status="missing",
                    returncode=None,
                    duration_sec=0.0,
                    validation=None,
                    stdout_tail="",
                    stderr_tail="file does not exist",
                )
            )
            continue
        rel = path.resolve().relative_to(ROOT) if path.resolve().is_relative_to(ROOT) else path.resolve()
        per_file_dir = per_file_root / f"{idx:05d}_{safe_slug(Path(rel))}"
        print(f"start {idx + 1}/{len(files)}: {rel}", flush=True)
        result = export_one(
            path.resolve(),
            per_file_dir,
            max(1, args.timeout_sec),
            args.lake,
            require_olean=not args.allow_missing_olean,
        )
        results.append(result)
        print(f"{result.status}: {rel} ({result.duration_sec:.2f}s)", flush=True)

    valid_dirs = [Path(row.out_dir) for row in results if row.status == "ok"]
    merged_metadata = None
    merged_validation = None
    if valid_dirs and not args.no_merge:
        print(f"merge: {len(valid_dirs)} valid exports -> {merged_dir}", flush=True)
        merged_metadata = merge_valid_exports(valid_dirs, merged_dir)
        print(f"validate merged export: {merged_dir}", flush=True)
        validation_rc, merged_validation, _, _ = validate_export(merged_dir)
        if validation_rc != 0 or merged_validation.get("ok") is not True:
            results.append(
                FileResult(
                    file="<merged>",
                    out_dir=str(merged_dir),
                    status="merged_validation_failed",
                    returncode=validation_rc,
                    duration_sec=0.0,
                    validation=merged_validation,
                    stdout_tail="",
                    stderr_tail="",
                )
            )

    failures = [row for row in results if row.status != "ok"]
    report = {
        "schema": "info_geometry.raw_infotree_batch_export_report.v1",
        "output_dir": str(output_dir),
        "merged_dir": str(merged_dir) if valid_dirs and not args.no_merge else None,
        "selected_file_count": len(files),
        "valid_file_count": len(valid_dirs),
        "failure_count": len(failures),
        "timeout_sec": max(1, args.timeout_sec),
        "merged_metadata": merged_metadata,
        "merged_validation": merged_validation,
        "results": [row.__dict__ for row in results],
    }
    report_path = output_dir / "batch_report.json"
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(f"batch report: {report_path}")
    if failures and not args.allow_failures:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
