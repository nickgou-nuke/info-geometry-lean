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
import hashlib
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
if __package__ in (None, ""):
    sys.path.insert(0, str(ROOT))
    sys.path.insert(0, str(ROOT / "src"))

from tools.infra.pantograph_environment import build_lean_context_manifest  # noqa: E402
from tools.infra.run_locked_lean import execute_locked_lean  # noqa: E402

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
    "raw_infotree_goal_states.jsonl",
    "raw_infotree_fvar_lineage.jsonl",
    "raw_infotree_tactic_arguments.jsonl",
    "raw_infotree_messages.jsonl",
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
    source_provenance: dict[str, Any] | None = None


def tail_text(text: str | bytes, limit: int = 8000) -> str:
    # TimeoutExpired carries bytes even when subprocess uses text=True.
    if isinstance(text, bytes):
        text = text.decode("utf-8", errors="replace")
    return text[-limit:] if len(text) > limit else text


def safe_slug(path: Path) -> str:
    text = str(path)
    return "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in text)


def olean_path_for(path: Path) -> Path | None:
    root = Path(os.path.abspath(os.fspath(ROOT / "lean")))
    source = path if path.is_absolute() else ROOT / path
    source = Path(os.path.abspath(os.fspath(source)))
    try:
        rel = source.relative_to(root)
    except ValueError:
        return None
    return ROOT / ".lake" / "build" / "lib" / "lean" / rel.with_suffix(".olean")


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


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
    root_absolute = Path(os.path.abspath(os.fspath(ROOT)))
    for path in files:
        if not path.is_absolute():
            path = root_absolute / path
        path = Path(os.path.abspath(os.fspath(path)))
        try:
            rel = str(path.relative_to(root_absolute))
        except ValueError:
            rel = str(path)
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


def _capture_bundle_sha256(out_dir: Path) -> str:
    """Hash the raw row bundle using the shared InfoTree DNA contract."""
    from tools.repository_evolution.infotree_dna import (
        capture_bundle_fingerprint, capture_file_digests,
    )

    digests = capture_file_digests(out_dir)
    missing = sorted(set(JSONL_FILES) - set(digests))
    if missing:
        raise ValueError(f"capture is missing raw InfoTree row files: {', '.join(missing)}")
    return capture_bundle_fingerprint(digests)


def reuse_existing_export(
    path: Path, per_file_dir: Path, source_sha256: str,
    source_context: dict[str, Any] | None,
) -> FileResult:
    """Reuse only a validated capture bound to current source, context, and row bytes."""
    start = time.monotonic()
    if source_context is None:
        return FileResult(
            file=str(path), out_dir=str(per_file_dir), status="resume_unbound_context",
            returncode=None, duration_sec=0.0, validation=None, stdout_tail="",
            stderr_tail="safe resume requires a source and Lean-context receipt",
        )
    validation_rc, validation, stdout, stderr = validate_export(per_file_dir)
    if validation_rc != 0 or validation.get("ok") is not True:
        return FileResult(
            file=str(path), out_dir=str(per_file_dir), status="resume_invalid_existing",
            returncode=validation_rc, duration_sec=time.monotonic() - start,
            validation=validation, stdout_tail=tail_text(stdout), stderr_tail=tail_text(stderr),
        )
    try:
        metadata = json.loads((per_file_dir / "metadata.json").read_text(encoding="utf-8"))
        provenance = metadata.get("sourceProvenance")
        if not isinstance(provenance, dict):
            raise ValueError("capture lacks source provenance")
        if provenance.get("exporterSourceSha256") != hashlib.sha256(EXPORTER.read_bytes()).hexdigest():
            raise ValueError("capture exporter source receipt is missing or no longer matches")
        if (provenance.get("sourcePath") != source_context.get("sourcePath")
                or provenance.get("sourceSha256") != source_sha256
                or provenance.get("leanContextFingerprint") != source_context.get("fingerprint")):
            raise ValueError("capture source or Lean context no longer matches")
        observed_bundle_sha = _capture_bundle_sha256(per_file_dir)
        if provenance.get("rawCaptureSha256") != observed_bundle_sha:
            raise ValueError("capture row-bundle digest is missing or mismatched")
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        return FileResult(
            file=str(path), out_dir=str(per_file_dir), status="resume_unverified_existing",
            returncode=None, duration_sec=time.monotonic() - start,
            validation=validation, stdout_tail=tail_text(stdout),
            stderr_tail=f"preserved existing output; cannot safely reuse: {exc}",
        )
    return FileResult(
        file=str(path), out_dir=str(per_file_dir), status="reused",
        returncode=0, duration_sec=time.monotonic() - start,
        validation=validation, stdout_tail=tail_text(stdout), stderr_tail=tail_text(stderr),
        source_provenance=provenance,
    )


def export_one(
    path: Path,
    per_file_dir: Path,
    timeout_sec: int,
    lake: str,
    *,
    require_olean: bool,
    resume: bool = False,
) -> FileResult:
    start = time.monotonic()
    source_sha256 = hashlib.sha256(path.read_bytes()).hexdigest()
    exporter_sha256 = hashlib.sha256(EXPORTER.read_bytes()).hexdigest() if EXPORTER.is_file() else None
    source_context = None
    if require_olean:
        try:
            source_context = build_lean_context_manifest(ROOT, path)
        except Exception as exc:
            return FileResult(
                file=str(path), out_dir=str(per_file_dir), status="provenance_failed",
                returncode=None, duration_sec=time.monotonic() - start, validation=None,
                stdout_tail="", stderr_tail=f"could not fingerprint Lean context: {exc}",
            )
        if source_context["sourceSha256"] != source_sha256:
            return FileResult(
                file=str(path), out_dir=str(per_file_dir), status="source_changed",
                returncode=None, duration_sec=time.monotonic() - start, validation=None,
                stdout_tail="", stderr_tail="source changed while its context fingerprint was computed",
            )
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
        if resume:
            return reuse_existing_export(path, per_file_dir, source_sha256, source_context)
        return FileResult(
            file=str(path), out_dir=str(per_file_dir), status="output_exists",
            returncode=None, duration_sec=time.monotonic() - start, validation=None,
            stdout_tail="", stderr_tail=(
                "refusing to replace an existing InfoTree capture; choose a new output directory"
            ),
        )
    per_file_dir.mkdir(parents=True, exist_ok=True)
    source_arg = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
    output_arg = per_file_dir.relative_to(ROOT) if per_file_dir.is_relative_to(ROOT) else per_file_dir
    diagnostic_path = per_file_dir / "export.stderr.log"
    def diagnostic_tail() -> str:
        with diagnostic_path.open("rb") as stream:
            stream.seek(0, os.SEEK_END)
            stream.seek(max(0, stream.tell() - 32000))
            return tail_text(stream.read())

    try:
        with diagnostic_path.open("xb") as diagnostic_stream:
            proc = execute_locked_lean(
                EXPORTER.relative_to(ROOT),
                [str(source_arg), str(output_arg)],
                lake=lake,
                root=ROOT,
                run_script=True,
                text=True,
                stdout=subprocess.PIPE,
                stderr=diagnostic_stream,
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
            stderr_tail=diagnostic_tail() or tail_text(exc.stderr or ""),
        )
    proc.stderr = diagnostic_tail() or proc.stderr or ""
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
    provenance = ({
        "sourcePath": source_context["sourcePath"],
        "sourceSha256": source_sha256,
        "leanContextFingerprint": source_context["fingerprint"],
        "leanContext": source_context,
        "exporterSourceSha256": exporter_sha256,
    } if source_context else None)
    if hashlib.sha256(path.read_bytes()).hexdigest() != source_sha256:
        status = "source_changed"
        provenance = None
    elif provenance is not None and (
        exporter_sha256 is None or not EXPORTER.is_file()
        or hashlib.sha256(EXPORTER.read_bytes()).hexdigest() != exporter_sha256
    ):
        status = "exporter_changed"
        provenance = None
    elif provenance is not None:
        metadata_path = per_file_dir / "metadata.json"
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        provenance["rawCaptureSha256"] = _capture_bundle_sha256(per_file_dir)
        metadata["sourceProvenance"] = provenance
        metadata_path.write_text(json.dumps(metadata, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    return FileResult(
        file=str(path),
        out_dir=str(per_file_dir),
        status=status,
        returncode=proc.returncode,
        duration_sec=time.monotonic() - start,
        validation=validation,
        stdout_tail=tail_text(proc.stdout + validation_stdout),
        stderr_tail=tail_text(proc.stderr + validation_stderr),
        source_provenance=provenance,
    )


def merge_valid_exports(valid_dirs: list[Path], merged_dir: Path) -> dict[str, Any]:
    if merged_dir.exists():
        raise FileExistsError(
            f"refusing to replace existing merged InfoTree export: {merged_dir}"
        )
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
    parser.add_argument(
        "--merge", action="store_true",
        help="Create a second combined copy of all validated per-file rows (opt-in).",
    )
    parser.add_argument(
        "--resume", action="store_true",
        help="Reuse existing per-file exports only when source, Lean context, row digest, and validation match.",
    )
    parser.add_argument(
        "--no-merge", action="store_true",
        help=argparse.SUPPRESS,
    )
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
    batch_report_path = output_dir / "batch_report.json"
    planned_dirs = [
        per_file_root / (f"{idx:05d}_" + safe_slug(Path(
            path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        )))
        for idx, path in enumerate(files)
    ]
    existing_outputs = ([] if args.resume else
                        [str(path) for path in planned_dirs if path.exists()])
    if args.merge and not args.no_merge and merged_dir.exists():
        existing_outputs.append(str(merged_dir))
    report_path = (output_dir / f"batch_report_resume_{time.time_ns()}.json"
                   if args.resume and batch_report_path.exists() else batch_report_path)
    if report_path.exists():
        existing_outputs.append(str(report_path))
    if existing_outputs:
        print(
            "Refusing to overwrite existing batch outputs; choose a new --output-dir: "
            + ", ".join(existing_outputs[:8]),
            file=sys.stderr,
        )
        return 2
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
        lexical_path = Path(os.path.abspath(os.fspath(path)))
        root_absolute = Path(os.path.abspath(os.fspath(ROOT)))
        rel = lexical_path.relative_to(root_absolute) if lexical_path.is_relative_to(root_absolute) else lexical_path
        per_file_dir = per_file_root / f"{idx:05d}_{safe_slug(Path(rel))}"
        print(f"start {idx + 1}/{len(files)}: {rel}", flush=True)
        result = export_one(
            lexical_path,
            per_file_dir,
            max(1, args.timeout_sec),
            args.lake,
            require_olean=not args.allow_missing_olean,
            resume=args.resume,
        )
        results.append(result)
        print(f"{result.status}: {rel} ({result.duration_sec:.2f}s)", flush=True)

    valid_dirs = [Path(row.out_dir) for row in results if row.status in {"ok", "reused"}]
    merged_metadata = None
    merged_validation = None
    if valid_dirs and args.merge and not args.no_merge:
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

    failures = [row for row in results if row.status not in {"ok", "reused"}]
    report = {
        "schema": "info_geometry.raw_infotree_batch_export_report.v1",
        "output_dir": str(output_dir),
        "merged_dir": str(merged_dir)
        if valid_dirs and args.merge and not args.no_merge else None,
        "selected_file_count": len(files),
        "valid_file_count": len(valid_dirs),
        "failure_count": len(failures),
        "timeout_sec": max(1, args.timeout_sec),
        "merged_metadata": merged_metadata,
        "merged_validation": merged_validation,
        "results": [row.__dict__ for row in results],
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(
        json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8"
    )
    print(f"batch report: {report_path}")
    if failures and not args.allow_failures:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
