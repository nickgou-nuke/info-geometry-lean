#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


ROOT = repo_root()


def iter_lean_files(root: Path) -> list[Path]:
    skip_dirs = {".git", ".lake", "lake-packages", ".cache", "node_modules", ".venv", ".venv-py312"}
    if root.is_file():
        return [root] if root.suffix == ".lean" else []
    files: list[Path] = []
    for path in sorted(root.rglob("*.lean")):
        if not path.is_file():
            continue
        if any(part in skip_dirs for part in path.parts):
            continue
        files.append(path)
    return files


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def output_stem(path: Path) -> str:
    relative = rel(path)
    return (
        relative.removesuffix(".lean")
        .replace("/", "__")
        .replace("\\", "__")
        .replace(" ", "_")
        .replace(":", "_")
    )


def load_summary(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    summary = payload.get("summary", {})
    return summary if isinstance(summary, dict) else {}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run agentic closure-debt audit one Lean file at a time. "
            "This wraps tools/quality/closure_debt_crawler.py --coding-agent-command "
            "with resumable per-file outputs."
        )
    )
    parser.add_argument("--root", default="lean", help="Lean file or directory to audit.")
    parser.add_argument(
        "--coding-agent-command",
        default="codex exec --json",
        help="External coding-agent command. It receives the audit prompt on stdin and must return JSON.",
    )
    parser.add_argument("--out-dir", default="reports/audit/agentic-closure-debt")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--max-chars", type=int, default=60000)
    parser.add_argument("--limit", type=int, default=0, help="Audit at most N files after filtering.")
    parser.add_argument("--start-after", default="", help="Skip files up to and including this repo-relative path.")
    parser.add_argument("--force", action="store_true", help="Re-run files with existing per-file JSON output.")
    parser.add_argument("--fail-fast", action="store_true", help="Stop at first nonzero crawler exit.")
    parser.add_argument("--print-progress", action="store_true")
    parser.add_argument(
        "--no-summary",
        action="store_true",
        help="Do not write aggregate agentic-summary.json.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = normalize_user_path(args.root, ROOT)
    out_dir = normalize_user_path(args.out_dir, ROOT)
    out_dir.mkdir(parents=True, exist_ok=True)

    agent_command = shlex.split(args.coding_agent_command)
    if not agent_command:
        raise SystemExit("--coding-agent-command parsed to an empty command")

    files = iter_lean_files(root)
    if args.start_after:
        start_after = args.start_after.strip()
        files = [path for path in files if rel(path) > start_after]
    if args.limit > 0:
        files = files[: args.limit]

    rows: list[dict[str, Any]] = []
    failures = 0
    skipped = 0
    completed = 0
    total = len(files)

    for idx, path in enumerate(files, start=1):
        stem = output_stem(path)
        json_out = out_dir / f"{stem}.json"
        md_out = out_dir / f"{stem}.md"

        if json_out.exists() and not args.force:
            skipped += 1
            summary = load_summary(json_out)
            rows.append(
                {
                    "path": rel(path),
                    "status": "skipped-existing",
                    "json": rel(json_out),
                    "md": rel(md_out),
                    "summary": summary,
                }
            )
            if args.print_progress:
                print(f"[agentic-closure] {idx}/{total} skip {rel(path)}", flush=True)
            continue

        if args.print_progress:
            print(f"[agentic-closure] {idx}/{total} audit {rel(path)}", flush=True)

        cmd = [
            sys.executable,
            "tools/quality/closure_debt_crawler.py",
            "--root",
            rel(path),
            "--json-out",
            rel(json_out),
            "--md-out",
            rel(md_out),
            "--coding-agent-command",
            args.coding_agent_command,
            "--coding-agent-timeout",
            str(args.timeout),
            "--coding-agent-max-chars",
            str(args.max_chars),
            "--coding-agent-limit",
            "1",
            "--no-repo-wide-laundering-audit",
            "--print-summary",
        ]

        proc = subprocess.run(cmd, cwd=ROOT, check=False)
        if proc.returncode == 0:
            completed += 1
        else:
            failures += 1
        summary = load_summary(json_out)
        rows.append(
            {
                "path": rel(path),
                "status": "ok" if proc.returncode == 0 else "failed",
                "exit_code": proc.returncode,
                "json": rel(json_out),
                "md": rel(md_out),
                "summary": summary,
            }
        )
        if proc.returncode != 0 and args.fail_fast:
            break

    aggregate = {
        "schema": "info_geometry.agentic_closure_debt_audit.v1",
        "root": rel(root),
        "coding_agent_command": agent_command,
        "out_dir": rel(out_dir),
        "total_selected": total,
        "completed": completed,
        "skipped_existing": skipped,
        "failures": failures,
        "rows": rows,
    }
    if not args.no_summary:
        summary_out = out_dir / "agentic-summary.json"
        summary_out.write_text(json.dumps(aggregate, indent=2), encoding="utf-8")
        print(f"[agentic-closure] summary={rel(summary_out)}", flush=True)

    print(
        f"[agentic-closure] selected={total} completed={completed} "
        f"skipped={skipped} failures={failures}",
        flush=True,
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
