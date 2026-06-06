#!/usr/bin/env python3
"""Seed ArangoDB hive queue with sorry-based goals for self-evolution.

Reads the lean/ directory, finds files with `sorry`, and enqueues each
as a goal in the hive_tasks queue for the evolution loop to process.

Usage:
    python3 tools/infra/seed_goals_from_sorries.py [--limit 10] [--priority-threshold 3]
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

# Ensure tools/ is importable
_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.hive_arango_queue import enqueue_goal


def find_sorries(lean_dir: Path, max_per_file: int = 30) -> list[dict]:
    """Find sorry statements in .lean files.

    Returns sorted list of dicts with file, line, context, module.
    """
    results = []
    for f in sorted(lean_dir.rglob("*.lean")):
        if not f.is_file():
            continue
        rel = f.relative_to(_REPO)
        parts = rel.parts

        # Skip known non-source directories
        skip = {".git", "lake-packages", "_target", ".lake"}
        if any(p in skip for p in parts):
            continue

        text = f.read_text(errors="replace")
        if "sorry" not in text:
            continue

        lines = text.split("\n")
        sorry_count = 0
        in_block_comment = False
        for i, line in enumerate(lines, 1):
            # Track block comments / docstrings `/- ... -/`
            trimmed = line.strip()
            if in_block_comment:
                if "-/" in trimmed:
                    in_block_comment = False
                continue
            if trimmed.startswith("/-"):
                if "-/" in trimmed:
                    # single-line block comment — skip
                    continue
                in_block_comment = True
                continue

            # Strip inline comments and string literals to find real `sorry`
            stripped = line.split("--")[0]                      # remove inline comment
            stripped = re.sub(r'"[^"]*"', '', stripped)         # remove string literals
            if not re.search(r'(?<![`\w])sorry(?![`\w])', stripped):
                continue
            sorry_count += 1
            if sorry_count > max_per_file:
                break

            # Extract module path from the file path
            module_parts = list(rel.parts)
            if module_parts[0] == "lean":
                module_parts[0] = "lean"
            module = ".".join(module_parts).replace(".lean", "")

            # Extract context (the theorem/lemma/def name on or above this line)
            context = _find_context(lines, i)

            # Build a goal hash from file+line+context for dedup
            raw = f"{rel}:{i}:{context.get('name', '')}"
            goal_hash = hashlib.sha256(raw.encode()).hexdigest()[:24]

            results.append({
                "file": str(rel),
                "line": i,
                "module": module,
                "context": context,
                "goal_hash": goal_hash,
                "target_pretty": f"Prove `{context.get('name', '?')}` in {rel}:{i}",
                "priority": max(0.1, 1.0 / max(1, sorry_count)),
            })

    return results


def _find_context(lines: list[str], line_no: int) -> dict:
    """Scan upward from line_no to find the enclosing theorem/lemma/def."""
    name = "?"
    kind = "theorem"
    for i in range(line_no - 2, max(line_no - 20, 0), -1):
        m = re.match(r"\s*(theorem|lemma|def)\s+(\w+)", lines[i])
        if m:
            kind = m.group(1)
            name = m.group(2)
            break
    return {"name": name, "kind": kind, "line": line_no - (line_no - i)}


def main() -> None:
    parser = argparse.ArgumentParser(description="Seed sorry-based goals into ArangoDB")
    parser.add_argument("--limit", type=int, default=5, help="Max goals to enqueue")
    parser.add_argument("--max-sorries", type=int, default=5,
                        help="Max sorrys per file to include (fewer = easier)")
    parser.add_argument("--queue", default="proof-search")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    load_repo_arango_env(_REPO)
    ep = arango_endpoint()
    db = arango_database("hive_live")
    usr = arango_username()
    pwd = arango_password("alexandria_root")

    # Find all sorries, sorted by difficulty (fewest sorrys per file first)
    all_sorries = find_sorries(_REPO / "lean", max_per_file=args.max_sorries)
    # Sort by priority descending (easier = higher priority)
    all_sorries.sort(key=lambda x: (-x["priority"], x["file"], x["line"]))

    # Dedup: skip files that already have tasks in the queue
    from tools.infra.hive_arango_queue import aql
    existing = set()
    try:
        rows = aql(ep, db, usr, pwd,
            "FOR t IN hive_tasks FILTER t.queue_name == @q RETURN t.runtime_goal_packet.formal_target",
            {"q": args.queue})
        for r in rows:
            existing.add(r)
    except Exception:
        pass

    to_enqueue = [s for s in all_sorries if s["target_pretty"] not in existing][:args.limit]
    skipped = len(all_sorries) - len([s for s in all_sorries if s["target_pretty"] not in existing])
    print(f"Found {len(all_sorries)} sorry locations, {skipped} already queued, seeding {len(to_enqueue)}...")

    for i, s in enumerate(to_enqueue, 1):
        ctx = s["context"]
        if args.dry_run:
            print(f"  [{i}/{len(to_enqueue)}] {ctx['kind']} `{ctx['name']}` "
                  f"in {s['file']}:{s['line']} "
                  f"(priority={s['priority']:.2f})")
            continue

        try:
            enqueue_goal(
                ep, db, usr, pwd,
                queue_name=args.queue,
                goal_hash_shape=s["goal_hash"],
                canonical_shape=s["goal_hash"],
                target_pretty=s["target_pretty"],
                module=s["module"],
                goal_index=s["line"],
                priority=s["priority"],
                task_kind="proof.search",
            )
            print(f"  ✓ [{i}/{len(to_enqueue)}] {ctx['name']} "
                  f"({s['file']}:{s['line']})")
        except Exception as exc:
            print(f"  ✗ [{i}/{len(to_enqueue)}] {ctx['name']}: {exc}")

    print("\nDone.")
    print(f"  Queue: {args.queue}")
    if not args.dry_run:
        print(f"  Seeded {len(to_enqueue)} goals for evolution loop.")
        print(f"  Run: python3 tools/infra/hermes_self_evolver.py "
              f"--skill lean-proof --generations 3 --tasks-per-gen {len(to_enqueue)}")


if __name__ == "__main__":
    main()
