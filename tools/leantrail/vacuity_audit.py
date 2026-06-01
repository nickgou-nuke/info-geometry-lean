#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[2]


INFO_JSON_RE = re.compile(r"information:\s*(\{.*\})\s*$")


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_snapshot(path: Path) -> dict[str, Any]:
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


def lean_string(s: str) -> str:
    return json.dumps(s)


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


def run_lean_script(script: str, *, timeout: int) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=REPO_ROOT, encoding="utf-8", delete=False) as handle:
        tmp = Path(handle.name)
        handle.write(script)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=REPO_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        return proc.returncode, proc.stdout
    finally:
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
    snapshot = load_snapshot(snapshot_path)
    selected = select_decls(
        snapshot,
        module_prefix=module_prefix,
        decl_prefix=decl_prefix,
        explicit_decls=set(decls),
        limit=limit,
    )
    by_module: dict[str, list[str]] = defaultdict(list)
    for node in selected:
        by_module[str(node["module"])].append(str(node.get("name") or node.get("id")))

    rows: list[dict[str, Any]] = []
    failures: list[dict[str, Any]] = []
    modules_run = 0

    for module in sorted(by_module):
        names = by_module[module]
        for start in range(0, len(names), module_batch_size):
            batch = names[start : start + module_batch_size]
            modules_run += 1
            code = module_script(module, batch)
            try:
                rc, output = run_lean_script(code, timeout=timeout)
            except subprocess.TimeoutExpired as exc:
                failures.append({
                    "module": module,
                    "decls": batch,
                    "returncode": "timeout",
                    "output_tail": str(exc)[-4000:],
                })
                if not keep_going:
                    break
                continue
            parsed = parse_biopsy_json(output)
            rows.extend(enrich_row(row) for row in parsed)
            if rc != 0 or len(parsed) != len(batch):
                failures.append({
                    "module": module,
                    "decls": batch,
                    "returncode": rc,
                    "expected_rows": len(batch),
                    "parsed_rows": len(parsed),
                    "output_tail": output[-4000:],
                })
                if not keep_going:
                    break
        if failures and not keep_going:
            break

    written = write_jsonl(out_path, rows)
    report = {
        "ok": not failures,
        "snapshot": str(snapshot_path),
        "out": str(out_path),
        "selected_decls": len(selected),
        "modules": len(by_module),
        "module_batches_run": modules_run,
        "rows_written": written,
        "failures": failures[:50],
        "failure_count": len(failures),
    }
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
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
    print(json.dumps(report, indent=2, ensure_ascii=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
