#!/usr/bin/env python3
from __future__ import annotations

import argparse
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
CANONICAL = REPO_ROOT / "skills" / "lean-dag-wire-refactor" / "SKILL.md"

OPENAI_YAML = """interface:
  display_name: "Lean DAG Wire Refactor"
  short_description: "LeanTrail graph-guided redundancy cleanup"
  default_prompt: "Use $lean-dag-wire-refactor to find and safely remove redundant Lean wires in info-geometry-lean."
  brand_color: "#2563EB"
"""

AGENT_POINTER = """# Lean DAG Wire Refactor

For repo-wide redundancy cleanup, namespace deduplication, stale dropin removal,
pure forwarding module collapse, Arango/DAG/Hodge/de Bruijn/WL candidate
analysis, or LeanTrail vacuum/critic-lane refactoring, load:

`skills/lean-dag-wire-refactor/SKILL.md`

Core law:

```text
Graph tools identify candidate wires.
Lean owner files decide truth.
Only kernel-checked source edits count.
```

Keep this file short. The full SOP lives in the skill file.
"""

COPILOT_AGENT = """---
name: lean-dag-wire-refactor
description: Graph-guided LeanTrail redundancy cleanup for info-geometry-lean.
tools: ["codebase", "search", "terminal"]
---

# Lean DAG Wire Refactor

Use this agent for repo-wide redundancy cleanup in `info-geometry-lean`.

Before acting, read `skills/lean-dag-wire-refactor/SKILL.md` and follow it as
the source of truth. Keep graph, Arango, Hodge, WL, hash, de Bruijn, and critic
data as evidence only. Lean owner files and kernel checks decide source edits.
"""


def write_text(path: Path, text: str, *, dry_run: bool) -> None:
    if dry_run:
        print(f"would write {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    print(f"wrote {path}")


def copy_skill(dst: Path, *, dry_run: bool) -> None:
    if dry_run:
        print(f"would copy {CANONICAL} -> {dst}")
        return
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(CANONICAL, dst)
    print(f"copied {dst}")


def sync(*, dry_run: bool = False) -> None:
    if not CANONICAL.exists():
        raise SystemExit(f"canonical skill missing: {CANONICAL}")

    home = Path.home()
    copies = [
        home / ".codex" / "skills" / "lean-dag-wire-refactor" / "SKILL.md",
        home / ".gemini" / "skills" / "lean-dag-wire-refactor" / "SKILL.md",
        home / ".gemini" / "antigravity" / "skills" / "lean-dag-wire-refactor" / "SKILL.md",
        home / ".openclaw" / "plugin-skills" / "lean-dag-wire-refactor" / "SKILL.md",
        REPO_ROOT / ".gemini" / "skills" / "lean-dag-wire-refactor" / "skill.md",
    ]
    for dst in copies:
        copy_skill(dst, dry_run=dry_run)

    write_text(
        home / ".codex" / "skills" / "lean-dag-wire-refactor" / "agents" / "openai.yaml",
        OPENAI_YAML,
        dry_run=dry_run,
    )
    write_text(REPO_ROOT / ".agents" / "workflows" / "lean-dag-wire-refactor.md", AGENT_POINTER, dry_run=dry_run)
    write_text(REPO_ROOT / ".opencode" / "lean-dag-wire-refactor.md", AGENT_POINTER, dry_run=dry_run)
    write_text(REPO_ROOT / ".github" / "agents" / "lean-dag-wire-refactor.agent.md", COPILOT_AGENT, dry_run=dry_run)


def main() -> int:
    parser = argparse.ArgumentParser(description="Sync the Lean DAG wire refactor SOP to local agent skill stores.")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    sync(dry_run=args.dry_run)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
