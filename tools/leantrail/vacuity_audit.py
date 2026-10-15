#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import uuid
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[2]
if __package__ in (None, ""):
    sys.path.insert(0, str(REPO_ROOT))

from tools.build_lock import acquire_build_lock

MAX_SNAPSHOT_BYTES = 128 * 1024 * 1024
MAX_COMPILER_OUTPUT_BYTES = 16 * 1024 * 1024


INFO_JSON_RE = re.compile(r"(?:information|info):\s*(\{.*\})\s*$")
UNSAFE_LEAN_NAME_FRAGMENTS = (
    "\n", "\r", "\t", " ", ";", "(", ")", "{", "}", "[", "]", "\"", "`", "\\",
    "--", "/-", "-/",
)


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_snapshot(path: Path) -> dict[str, Any]:
    if path.stat().st_size > MAX_SNAPSHOT_BYTES:
        raise ValueError("snapshot exceeds the 128 MiB safety bound; provide a compact declaration-only JSONL snapshot")
    if path.suffix == ".jsonl":
        nodes = []
        with path.open(encoding="utf-8") as handle:
            for line in handle:
                if len(line) > 1024 * 1024:
                    raise ValueError("snapshot JSONL row exceeds the 1 MiB safety bound")
                if not line.strip():
                    continue
                node = json.loads(line)
                if not isinstance(node, dict):
                    raise ValueError("declaration snapshot JSONL rows must be objects")
                if node.get("kind") == "Declaration":
                    nodes.append({k: node.get(k) for k in ("kind", "id", "name", "module")})
        return {"nodes": nodes}
    return json.loads(path.read_text(encoding="utf-8"))


def iter_decl_nodes(snapshot: dict[str, Any]) -> Iterable[dict[str, Any]]:
    for node in snapshot.get("nodes", []):
        if isinstance(node, dict) and node.get("kind") == "Declaration":
            name = str(node.get("name") or node.get("id") or "").strip()
            module = str(node.get("module") or "").strip()
            if name and module and not name.startswith("module:"):
                yield node


def select_decls(
    snapshot: dict[str, Any],
    *,
    module_prefix: str | None,
    decl_prefix: str | None,
    explicit_decls: set[str],
    limit: int | None,
) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    seen: set[str] = set()
    for node in iter_decl_nodes(snapshot):
        name = str(node.get("name") or node.get("id") or "")
        module = str(node.get("module") or "")
        if explicit_decls and name not in explicit_decls:
            continue
        if module_prefix and not module.startswith(module_prefix):
            continue
        if decl_prefix and not name.startswith(decl_prefix):
            continue
        if name in seen:
            continue
        seen.add(name)
        selected.append(node)
        if limit is not None and len(selected) >= limit:
            break
    return selected


def is_safe_lean_name(name: str) -> bool:
    stripped = name.strip()
    if not stripped or stripped != name:
        return False
    if stripped.startswith(".") or stripped.endswith(".") or ".." in stripped:
        return False
    return not any(fragment in stripped for fragment in UNSAFE_LEAN_NAME_FRAGMENTS)


def module_script(module: str, decls: list[str]) -> str:
    lines = [
        "import InfoGeometry.Lint.NonTriviality",
        f"import {module}",
        "",
        "set_option autoImplicit false",
        "",
    ]
    for decl in decls:
        lines.append(f"#biopsy_non_triviality {decl}")
    lines.append("")
    return "\n".join(lines)


def parse_biopsy_json(output: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in output.splitlines():
        match = INFO_JSON_RE.search(line)
        if not match:
            stripped = line.strip()
            if stripped.startswith("{") and stripped.endswith("}"):
                raw = stripped
            else:
                continue
        else:
            raw = match.group(1)
        try:
            obj = json.loads(raw)
        except Exception:
            continue
        if isinstance(obj, dict) and (obj.get("target") or obj.get("name")):
            rows.append(obj)
    return rows


def process_group_has_live_members(group_id: int) -> bool:
    """Check Linux process-group lifetime, ignoring unreaped zombies."""
    proc_root = Path("/proc")
    if not proc_root.is_dir():
        raise RuntimeError("compiler lifetime supervision requires Linux /proc")
    for entry in proc_root.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == group_id and fields[0] != "Z":
                return True
        except (FileNotFoundError, ProcessLookupError):
            continue
    return False


def wait_for_process_group(group_id: int) -> None:
    while process_group_has_live_members(group_id):
        try:
            time.sleep(0.2)
        except KeyboardInterrupt:
            continue


def run_lean_script(script: str, *, timeout: int) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", encoding="utf-8", delete=False) as handle:
        tmp = Path(handle.name)
        handle.write(script)
    lock = None
    proc = None
    output_file = tempfile.TemporaryFile(mode="w+b")
    try:
        lock = acquire_build_lock(None, f"leantrail-biopsy:{os.getpid()}", block=True)
        active = subprocess.run(
            ["pgrep", "-af", r"(^|/)(lake|lean)( |$)"],
            text=True, capture_output=True, check=False,
        )
        if active.returncode != 1:
            raise RuntimeError("compiler precheck failed or another compiler is active; refusing biopsy batch")
        proc = subprocess.Popen(
            ["lake", "env", "lean", str(tmp)],
            cwd=REPO_ROOT,
            stdout=output_file,
            stderr=subprocess.STDOUT,
            start_new_session=True,
            pass_fds=(lock.fileno(),),
        )
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            print(f"[biopsy] observation timeout after {timeout}s; retaining lock and waiting without killing the compiler", file=sys.stderr, flush=True)
            proc.wait()
        wait_for_process_group(proc.pid)
        output_file.seek(0, os.SEEK_END)
        if output_file.tell() > MAX_COMPILER_OUTPUT_BYTES:
            raise RuntimeError("compiler output exceeds the 16 MiB reporting bound; audit incomplete")
        output_file.seek(0)
        output = output_file.read().decode("utf-8")
        return proc.returncode, output
    finally:
        # Never release the build lane or delete the input beneath a live child.
        if proc is not None:
            while proc.poll() is None:
                try:
                    proc.wait()
                except KeyboardInterrupt:
                    continue
            # Lake can exit before an orphaned Lean grandchild. Keep ownership
            # until the whole new-session group has drained, without killing it.
            wait_for_process_group(proc.pid)
        if lock is not None:
            lock.release()
        output_file.close()
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass


def enrich_row(row: dict[str, Any]) -> dict[str, Any]:
    stable = json.dumps(row, sort_keys=True, ensure_ascii=True)
    out = dict(row)
    out.setdefault("certificate_ref", "")
    out["audit_hash"] = sha256_text(stable)
    out["artifact_version"] = 1
    return out


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def atomic_report(path: Path, report: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", dir=path.parent, encoding="utf-8", delete=False) as handle:
        temporary = Path(handle.name)
        json.dump(report, handle, ensure_ascii=True, indent=2)
        handle.write("\n")
    temporary.replace(path)


def run(
    *,
    snapshot_path: Path,
    out_path: Path,
    json_out: Path,
    module_prefix: str | None,
    decl_prefix: str | None,
    decls: list[str],
    limit: int | None,
    module_batch_size: int,
    timeout: int,
    keep_going: bool,
) -> dict[str, Any]:
    if len({snapshot_path.resolve(), out_path.resolve(), json_out.resolve()}) != 3:
        raise ValueError("snapshot, audit output, and report paths must be distinct")
    run_id = uuid.uuid4().hex
    atomic_report(json_out, {"status": "running", "run_id": run_id,
                            "ok": False, "execution_ok": False,
                            "semantic_clearance": False})
    snapshot = load_snapshot(snapshot_path)
    selected = select_decls(
        snapshot,
        module_prefix=module_prefix,
        decl_prefix=decl_prefix,
        explicit_decls=set(decls),
        limit=limit,
    )
    if not selected:
        raise ValueError("snapshot selection contains no declarations; no audit coverage")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    partial = out_path.with_name(f"{out_path.name}.{run_id}.partial")
    partial.write_text("", encoding="utf-8")
    written = 0
    unresolved = []
    failures: list[dict[str, Any]] = []
    modules_run = 0
    by_module: dict[str, list[str]] = defaultdict(list)
    for node in selected:
        module = str(node["module"])
        name = str(node.get("name") or node.get("id"))
        if not is_safe_lean_name(module) or not is_safe_lean_name(name):
            failures.append({
                "module": module,
                "decls": [name],
                "returncode": "invalid_lean_name",
                "output_tail": "Snapshot module/declaration name is not safe Lean command syntax.",
            })
            if not keep_going:
                break
            continue
        by_module[module].append(name)

    if not failures or keep_going:
        for module in sorted(by_module):
            names = by_module[module]
            for start in range(0, len(names), module_batch_size):
                batch = names[start : start + module_batch_size]
                modules_run += 1
                code = module_script(module, batch)
                try:
                    rc, output = run_lean_script(code, timeout=timeout)
                except (OSError, UnicodeError, ValueError, RuntimeError) as exc:
                    failures.append({
                        "module": module,
                        "decls": batch,
                        "returncode": "execution_error",
                        "output_tail": str(exc)[-4000:],
                    })
                    if not keep_going:
                        break
                    continue
                parsed = parse_biopsy_json(output)
                targets = [str(row.get("target") or row.get("name")) for row in parsed]
                schema_ok = all(
                    isinstance(row.get("attrs"), dict)
                    and isinstance(row["attrs"].get("vacuity"), dict)
                    and isinstance(row["attrs"].get("contamination"), dict)
                    and isinstance(row["attrs"]["contamination"].get("state"), str)
                    for row in parsed)
                if rc != 0 or sorted(targets) != sorted(batch) or not schema_ok:
                    failures.append({
                        "module": module,
                        "decls": batch,
                        "returncode": rc,
                        "expected_rows": len(batch),
                        "parsed_rows": len(parsed),
                        "output_tail": output[-4000:],
                        "parsed_targets": targets,
                    })
                    if not keep_going:
                        break
                    continue
                with partial.open("a", encoding="utf-8") as handle:
                    for row in parsed:
                        enriched = enrich_row(row)
                        enriched["run_id"] = run_id
                        handle.write(json.dumps(enriched, ensure_ascii=True, sort_keys=True) + "\n")
                        written += 1
                        vacuity = row["attrs"]["vacuity"]
                        contamination = row["attrs"]["contamination"]
                        if (vacuity.get("role") in {"closure_debt", "contaminated", "fake_transport"}
                                or vacuity.get("contains_sorry")
                                or contamination.get("state") != "clean"):
                            unresolved.append({"target": row.get("target"),
                                               "role": vacuity.get("role"),
                                               "contamination": contamination.get("state")})
                print(f"[biopsy] completed batch {modules_run}; published rows={written}, failures={len(failures)}", flush=True)
            if failures and not keep_going:
                break

    partial.replace(out_path)
    report = {
        "status": "incomplete" if failures else "review_required" if unresolved else "execution_complete",
        "run_id": run_id,
        "ok": not failures and not unresolved,
        "execution_ok": not failures,
        "semantic_clearance": False,
        "current_repository_coverage_complete": False,
        "unresolved_findings": unresolved,
        "unresolved_finding_count": len(unresolved),
        "snapshot": str(snapshot_path),
        "out": str(out_path),
        "selected_decls": len(selected),
        "modules": len(by_module),
        "module_batches_run": modules_run,
        "rows_written": written,
        "failures": failures[:50],
        "failure_count": len(failures),
    }
    atomic_report(json_out, report)
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the Lean NonTriviality biopsy command over declarations from a LeanTrail snapshot and emit vacuity_audit.jsonl."
    )
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.json")
    parser.add_argument("--out", default="artifacts/leantrail/vacuity_audit.jsonl")
    parser.add_argument("--json-out", default="artifacts/leantrail/vacuity_audit_report.json")
    parser.add_argument("--module-prefix")
    parser.add_argument("--decl-prefix")
    parser.add_argument("--decl", action="append", default=[], help="Specific fully-qualified declaration to audit. Repeatable.")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--module-batch-size", type=int, default=25)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--keep-going", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        report = run(
        snapshot_path=Path(args.snapshot).resolve(),
        out_path=Path(args.out).resolve(),
        json_out=Path(args.json_out).resolve(),
        module_prefix=args.module_prefix,
        decl_prefix=args.decl_prefix,
        decls=list(args.decl),
        limit=args.limit,
        module_batch_size=max(1, args.module_batch_size),
        timeout=max(1, args.timeout),
        keep_going=bool(args.keep_going),
        )
    except (OSError, UnicodeError, ValueError, RuntimeError) as exc:
        report = {"status": "failed", "ok": False, "execution_ok": False,
                  "semantic_clearance": False, "error_kind": type(exc).__name__,
                  "error": str(exc)}
        # Do not overwrite an input when invalid output paths caused the error.
        if Path(args.json_out).resolve() not in {Path(args.snapshot).resolve(), Path(args.out).resolve()}:
            atomic_report(Path(args.json_out), report)
    print(json.dumps(report, indent=2, ensure_ascii=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
