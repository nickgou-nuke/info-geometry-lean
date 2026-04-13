#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import repo_root
else:
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import repo_root


DEFAULT_MD_OUT = "reports/dag/repository-surface-index.md"
DEFAULT_JSON_OUT = "reports/dag/repository-surface-index.json"

MARKDOWN_SUFFIXES = {".md", ".markdown"}
PYTHON_SUFFIXES = {".py", ".pyi"}
CONFIG_SUFFIXES = {".toml", ".yaml", ".yml", ".ini", ".cfg", ".conf", ".json", ".jsonl", ".cff"}
CONFIG_JSON_PREFIXES = (
    ".github/",
    ".tasks/",
    "tools/schema/",
    "tools/infra/manifests/",
)
CONFIG_JSON_KEYWORDS = (
    "config",
    "manifest",
    "schema",
    "policy",
    "toolchain",
    "settings",
    "packet",
    "task",
    "lock",
)
CONFIG_FILENAMES = {
    ".gitignore",
    ".gitattributes",
    ".editorconfig",
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.lean",
    "pyproject.toml",
    "dag-toolchain.json",
    "dag-toolchain.local.json",
    "nemoclaw_config.yaml",
    "CITATION.cff",
}
BASELINE_REQUIRED_CONFIGS = [
    "dag-toolchain.json",
    "lakefile.lean",
    "lake-manifest.json",
    "lean-toolchain",
    "pyproject.toml",
    ".github/workflows/ci.yml",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate a repository-wide file-surface index across Lean, Markdown, Python, "
            "and configuration classes."
        )
    )
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT, help="Markdown output path.")
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="JSON output path.")
    parser.add_argument(
        "--include-untracked",
        action="store_true",
        help="Include untracked non-ignored files in addition to tracked files.",
    )
    return parser.parse_args()


def tracked_files(root: Path) -> list[str]:
    raw = subprocess.check_output(["git", "ls-files", "-z"], cwd=root)
    files = [chunk for chunk in raw.decode("utf-8", errors="replace").split("\0") if chunk]
    files.sort()
    return files


def untracked_files(root: Path) -> list[str]:
    raw = subprocess.check_output(
        ["git", "ls-files", "-z", "--others", "--exclude-standard"],
        cwd=root,
    )
    files = [chunk for chunk in raw.decode("utf-8", errors="replace").split("\0") if chunk]
    files.sort()
    return files


def is_config_path(rel: str) -> bool:
    path = Path(rel)
    name = path.name
    suffix = path.suffix.lower()
    rel_lower = rel.lower()

    if name in CONFIG_FILENAMES:
        return True
    if suffix in CONFIG_SUFFIXES and suffix != ".json" and suffix != ".jsonl":
        return True
    if suffix in {".json", ".jsonl"}:
        if any(rel.startswith(prefix) for prefix in CONFIG_JSON_PREFIXES):
            return True
        stem = path.stem.lower()
        if any(keyword in stem for keyword in CONFIG_JSON_KEYWORDS):
            return True
        if any(keyword in rel_lower for keyword in CONFIG_JSON_KEYWORDS):
            return True
    return False


def top_level_bucket(rel: str) -> str:
    parts = Path(rel).parts
    if not parts:
        return "."
    if len(parts) == 1:
        return "<root>"
    return parts[0]


def extension_bucket(rel: str) -> str:
    path = Path(rel)
    suffix = path.suffix.lower()
    if suffix:
        return suffix
    return "<no-ext>"


def render_markdown(payload: dict) -> str:
    counts = payload["counts"]
    top_levels = payload["topLevelCounts"]
    ext_other = payload["otherExtensionCounts"]
    classes = payload["classes"]
    include_untracked = payload.get("includeUntracked", False)

    lines: list[str] = []
    lines.append("# Repository Surface Index")
    lines.append("")
    lines.append(f"Generated: `{payload['generatedAt']}`")
    lines.append("")
    lines.append("## Scope")
    lines.append("- source classes: `lean`, `markdown`, `python`, `config`")
    if include_untracked:
        lines.append(
            "- universe: tracked files from `git ls-files` plus untracked non-ignored files"
        )
    else:
        lines.append("- universe: tracked files from `git ls-files`")
    lines.append("")
    lines.append("## Counts")
    lines.append(f"- tracked files: **{counts['trackedFiles']}**")
    lines.append(f"- untracked files (included): **{counts['untrackedFiles']}**")
    lines.append(f"- total universe files: **{counts['universeFiles']}**")
    lines.append(f"- lean files: **{counts['lean']}**")
    lines.append(f"- markdown files: **{counts['markdown']}**")
    lines.append(f"- python files: **{counts['python']}**")
    lines.append(f"- config files: **{counts['config']}**")
    lines.append(f"- union of tracked target classes: **{counts['trackedTargetUnion']}**")
    lines.append(f"- non-target/other tracked files: **{counts['other']}**")
    lines.append(f"- target union coverage: **{counts['targetCoveragePct']:.2f}%**")
    lines.append("")
    lines.append("## Baseline Config Presence")
    for item in payload["baselineConfigPresence"]:
        status = "present" if item["present"] else "missing"
        lines.append(f"- `{item['path']}`: **{status}**")
    lines.append("")
    lines.append("## Top-Level Distribution")
    for key, value in top_levels:
        lines.append(f"- `{key}`: {value}")
    lines.append("")
    lines.append("## Other Extension Distribution")
    if ext_other:
        for key, value in ext_other:
            lines.append(f"- `{key}`: {value}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Class Inventories")
    for class_name in ("lean", "markdown", "python", "config", "other"):
        entries = classes[class_name]
        lines.append(f"### {class_name} ({len(entries)})")
        if not entries:
            lines.append("- none")
            lines.append("")
            continue
        for rel in entries:
            lines.append(f"- `{rel}`")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root()
    tracked = tracked_files(root)
    untracked = untracked_files(root) if args.include_untracked else []
    files = sorted(set(tracked) | set(untracked))

    lean = sorted(rel for rel in files if rel.endswith(".lean"))
    markdown = sorted(rel for rel in files if Path(rel).suffix.lower() in MARKDOWN_SUFFIXES)
    python = sorted(rel for rel in files if Path(rel).suffix.lower() in PYTHON_SUFFIXES)
    config = sorted(rel for rel in files if is_config_path(rel))

    tracked_union = set(lean) | set(markdown) | set(python) | set(config)
    other = sorted(rel for rel in files if rel not in tracked_union)

    top_counter = Counter(top_level_bucket(rel) for rel in files)
    other_ext_counter = Counter(extension_bucket(rel) for rel in other)

    total = len(files)
    union_count = len(tracked_union)
    coverage_pct = (100.0 * union_count / total) if total else 0.0

    baseline_presence = [
        {"path": rel, "present": rel in set(files)} for rel in BASELINE_REQUIRED_CONFIGS
    ]

    payload = {
        "generatedAt": generated_timestamp(),
        "includeUntracked": args.include_untracked,
        "counts": {
            "trackedFiles": len(tracked),
            "untrackedFiles": len(untracked),
            "universeFiles": total,
            "lean": len(lean),
            "markdown": len(markdown),
            "python": len(python),
            "config": len(config),
            "trackedTargetUnion": union_count,
            "other": len(other),
            "targetCoveragePct": coverage_pct,
        },
        "baselineConfigPresence": baseline_presence,
        "topLevelCounts": sorted(top_counter.items(), key=lambda kv: (-kv[1], kv[0])),
        "otherExtensionCounts": sorted(other_ext_counter.items(), key=lambda kv: (-kv[1], kv[0])),
        "classes": {
            "lean": lean,
            "markdown": markdown,
            "python": python,
            "config": config,
            "other": other,
        },
    }

    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)
    write_text(json_out, json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
    write_text(md_out, render_markdown(payload))
    print(f"[generate-repository-surface-index] wrote {md_out}")
    print(f"[generate-repository-surface-index] wrote {json_out}")
    print(
        "[generate-repository-surface-index] counts "
        f"lean={len(lean)} markdown={len(markdown)} python={len(python)} "
        f"config={len(config)} union={union_count} other={len(other)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
