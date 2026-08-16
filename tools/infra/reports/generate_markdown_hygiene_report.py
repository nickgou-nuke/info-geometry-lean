#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import repo_root
else:
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import repo_root


DEFAULT_CLASSIFICATION_JSON = "reports/dag/markdown-classification.json"
DEFAULT_JSON_OUT = "reports/dag/markdown-hygiene.json"
DEFAULT_MD_OUT = "reports/dag/markdown-hygiene.md"

EXCLUDE_PREFIXES_DEFAULT = (
    "docs/black_books/",
    "docs/black_books_refactor/",
)

PROTECTED_DOCS = {
    "README.md",
    "docs/README.md",
    "docs/OperatorQuickstart.md",
    "docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md",
    "docs/MarkdownCorpusGovernance.md",
    "docs/ToolingMethodology.md",
    "docs/RepositoryMemoryMap.md",
    "docs/CODEBASE_STATUS.md",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Analyze markdown hygiene using content classification + link graph + git recency, "
            "with optional exclusion corridors (black books by default)."
        )
    )
    parser.add_argument("--classification-json", default=DEFAULT_CLASSIFICATION_JSON)
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT)
    parser.add_argument("--stale-days", type=int, default=45)
    parser.add_argument("--hard-stale-days", type=int, default=120)
    parser.add_argument("--low-confidence-threshold", type=float, default=0.55)
    parser.add_argument("--min-word-thin", type=int, default=120)
    parser.add_argument(
        "--exclude-prefix",
        action="append",
        default=[],
        help="Exclude path prefix from hygiene review (can repeat).",
    )
    parser.add_argument("--top-candidates", type=int, default=120)
    parser.add_argument("--top-readmes", type=int, default=80)
    parser.add_argument("--top-orphans", type=int, default=120)
    return parser.parse_args()


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def to_rel(path: Path, root: Path) -> str:
    return str(path.resolve().relative_to(root.resolve()))


def normalize_title(text: str) -> str:
    for line in text.splitlines():
        if line.strip().startswith("#"):
            title = re.sub(r"^#+\s*", "", line.strip()).strip().lower()
            title = re.sub(r"[^a-z0-9]+", " ", title).strip()
            return title
    return ""


def iter_markdown_links(text: str) -> list[str]:
    # Markdown link syntax: [label](target)
    out: list[str] = []
    for match in re.finditer(r"\[[^\]]+\]\(([^)]+)\)", text):
        target = match.group(1).strip()
        if not target:
            continue
        out.append(target)
    return out


def resolve_link_target(src_rel: str, raw_target: str, root: Path) -> str | None:
    target = raw_target.split("#", 1)[0].split("?", 1)[0].strip()
    if not target:
        return None
    lower = target.lower()
    if lower.startswith(("http://", "https://", "mailto:", "file://")):
        return None
    if target.startswith("#"):
        return None

    src_dir = (root / src_rel).parent
    candidate = (src_dir / target).resolve()
    if candidate.exists():
        try:
            rel = to_rel(candidate, root)
        except Exception:
            return None
        if rel.lower().endswith(".md"):
            return rel
    return None


def git_last_commit_unix(root: Path, rel_path: str) -> int | None:
    try:
        raw = subprocess.check_output(
            ["git", "log", "-1", "--format=%ct", "--", rel_path],
            cwd=root,
            stderr=subprocess.DEVNULL,
        ).decode("utf-8", errors="replace").strip()
    except Exception:
        return None
    if not raw:
        return None
    try:
        return int(raw)
    except Exception:
        return None


def classify_action(
    *,
    rel_path: str,
    stale_score: float,
    is_protected: bool,
) -> str:
    if is_protected:
        return "protected_keep"
    if stale_score >= 4.0:
        return "review_or_archive"
    if stale_score >= 2.5:
        return "review_update"
    return "keep"


def build_markdown(payload: dict[str, Any]) -> str:
    counts = payload["counts"]
    lines: list[str] = []
    lines.append("# Markdown Hygiene Report")
    lines.append("")
    lines.append(f"Generated: `{payload['generatedAt']}`")
    lines.append(f"Classification input: `{payload['classificationInput']}`")
    lines.append("")
    lines.append("## Scope")
    lines.append(f"- reviewed markdown files: **{counts['reviewed']}**")
    lines.append(f"- excluded markdown files: **{counts['excluded']}**")
    lines.append(f"- protected docs: **{counts['protected']}**")
    lines.append("")
    lines.append("## Actions")
    lines.append("")
    lines.append("| action | files |")
    lines.append("|---|---:|")
    for row in payload["actionCounts"]:
        lines.append(f"| `{row['action']}` | {row['count']} |")
    lines.append("")
    lines.append("## Top Review Candidates")
    lines.append("")
    lines.append("| score | age(d) | links-in | words | confidence | action | path |")
    lines.append("|---:|---:|---:|---:|---:|---|---|")
    for row in payload["topCandidates"]:
        lines.append(
            f"| {row['staleScore']:.2f} | {row['ageDays']} | {row['inboundLinks']} | {row['wordCount']} | "
            f"{row['confidence']:.3f} | `{row['action']}` | `{row['path']}` |"
        )
    lines.append("")
    lines.append("## README Inventory")
    lines.append("")
    lines.append("| age(d) | links-in | confidence | action | path |")
    lines.append("|---:|---:|---:|---|---|")
    for row in payload["readmeInventory"]:
        lines.append(
            f"| {row['ageDays']} | {row['inboundLinks']} | {row['confidence']:.3f} | "
            f"`{row['action']}` | `{row['path']}` |"
        )
    lines.append("")
    lines.append("## Orphan Docs (No Inbound Markdown Links)")
    lines.append("")
    lines.append("| age(d) | primary | confidence | path |")
    lines.append("|---:|---|---:|---|")
    for row in payload["topOrphans"]:
        lines.append(
            f"| {row['ageDays']} | `{row['primaryLabel']}` | {row['confidence']:.3f} | `{row['path']}` |"
        )
    lines.append("")
    lines.append("## Duplicate Titles")
    lines.append("")
    dupes = payload.get("duplicateTitles", [])
    if not dupes:
        lines.append("- none")
    else:
        for row in dupes:
            lines.append(f"- `{row['title']}` ({row['count']} files)")
            for path in row.get("paths", []):
                lines.append(f"  - `{path}`")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root()

    classification_json = normalize_user_path(
        args.classification_json,
        root / DEFAULT_CLASSIFICATION_JSON,
    )
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    cls = load_json(classification_json)
    files_raw = cls.get("files", [])
    if not isinstance(files_raw, list):
        raise SystemExit(f"invalid classification payload: {classification_json}")

    exclude_prefixes = list(EXCLUDE_PREFIXES_DEFAULT) + list(args.exclude_prefix or [])
    exclude_prefixes = [p.strip() for p in exclude_prefixes if p.strip()]

    now_unix = int(time.time())

    # Load rows by path for review scope.
    reviewed_rows: list[dict[str, Any]] = []
    excluded_rows: list[dict[str, Any]] = []
    for row in files_raw:
        if not isinstance(row, dict):
            continue
        rel = str(row.get("path", "")).strip()
        if not rel:
            continue
        if any(rel.startswith(prefix) for prefix in exclude_prefixes):
            excluded_rows.append(row)
        else:
            reviewed_rows.append(row)

    # Build markdown link graph (reviewed scope only).
    inbound_links: dict[str, set[str]] = defaultdict(set)
    outbound_links: dict[str, set[str]] = defaultdict(set)

    reviewed_set = {str(row.get("path", "")) for row in reviewed_rows}

    for row in reviewed_rows:
        rel = str(row.get("path", "")).strip()
        if not rel:
            continue
        path = root / rel
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            text = ""
        for raw_target in iter_markdown_links(text):
            target_rel = resolve_link_target(rel, raw_target, root)
            if not target_rel:
                continue
            if target_rel not in reviewed_set:
                continue
            outbound_links[rel].add(target_rel)
            inbound_links[target_rel].add(rel)

    # Duplicate titles across reviewed set.
    title_to_paths: dict[str, list[str]] = defaultdict(list)

    analyzed: list[dict[str, Any]] = []
    protected_count = 0

    stale_days = max(1, int(args.stale_days))
    hard_stale_days = max(stale_days, int(args.hard_stale_days))
    low_conf = float(args.low_confidence_threshold)
    min_word_thin = max(1, int(args.min_word_thin))

    for row in reviewed_rows:
        rel = str(row.get("path", "")).strip()
        primary = str(row.get("primaryLabel", "other"))
        confidence = float(row.get("confidence", 0.0))
        signals = row.get("signals", {}) if isinstance(row.get("signals"), dict) else {}
        words = int(signals.get("wordCount", 0) or 0)
        in_count = len(inbound_links.get(rel, set()))
        out_count = len(outbound_links.get(rel, set()))
        is_readme = Path(rel).name.lower() == "readme.md"
        is_protected = rel in PROTECTED_DOCS
        if is_protected:
            protected_count += 1

        last_ct = git_last_commit_unix(root, rel)
        age_days = -1
        if last_ct is not None:
            age_days = max(0, int((now_unix - last_ct) / 86400))

        text = ""
        try:
            text = (root / rel).read_text(encoding="utf-8", errors="ignore")
        except Exception:
            text = ""
        title = normalize_title(text)
        if title:
            title_to_paths[title].append(rel)

        stale_score = 0.0
        score_reasons: list[str] = []
        if age_days >= stale_days:
            stale_score += 1.8
            score_reasons.append(f"age>=stale({age_days})")
        if age_days >= hard_stale_days:
            stale_score += 1.2
            score_reasons.append(f"age>=hard_stale({age_days})")
        if in_count == 0:
            stale_score += 1.8
            score_reasons.append("orphan:no_inbound_links")
        if is_readme:
            stale_score += 0.8
            score_reasons.append("readme")
        if is_readme and in_count == 0:
            stale_score += 1.0
            score_reasons.append("readme_orphan")
        if confidence < low_conf:
            stale_score += 1.0
            score_reasons.append(f"low_confidence({confidence:.3f})")
        if words < min_word_thin:
            stale_score += 0.6
            score_reasons.append(f"thin_doc({words})")
        if primary in {"generated_auto", "generated_report"}:
            stale_score -= 0.7
            score_reasons.append("generated_surface")
        if is_protected:
            stale_score -= 2.0
            score_reasons.append("protected_doc")

        action = classify_action(rel_path=rel, stale_score=stale_score, is_protected=is_protected)

        analyzed.append(
            {
                "path": rel,
                "primaryLabel": primary,
                "confidence": confidence,
                "wordCount": words,
                "inboundLinks": in_count,
                "outboundLinks": out_count,
                "ageDays": age_days,
                "isReadme": is_readme,
                "isProtected": is_protected,
                "staleScore": round(stale_score, 4),
                "scoreReasons": score_reasons,
                "action": action,
                "title": title,
            }
        )

    analyzed.sort(key=lambda r: (-float(r["staleScore"]), str(r["path"])))

    action_counter = Counter(str(row["action"]) for row in analyzed)

    top_candidates = analyzed[: max(0, int(args.top_candidates))]
    readmes = [row for row in analyzed if bool(row.get("isReadme"))]
    readmes.sort(
        key=lambda r: (
            -float(r["staleScore"]),
            -int(r["ageDays"]),
            str(r["path"]),
        )
    )
    readmes = readmes[: max(0, int(args.top_readmes))]

    orphans = [row for row in analyzed if int(row.get("inboundLinks", 0)) == 0]
    orphans.sort(key=lambda r: (-float(r["staleScore"]), str(r["path"])))
    orphans = orphans[: max(0, int(args.top_orphans))]

    dupes = []
    for title, paths in title_to_paths.items():
        if not title or len(paths) < 2:
            continue
        dupes.append(
            {
                "title": title,
                "count": len(paths),
                "paths": sorted(paths)[:15],
            }
        )
    dupes.sort(key=lambda r: (-int(r["count"]), str(r["title"])))

    payload = {
        "generatedAt": generated_timestamp(),
        "classificationInput": str(classification_json.resolve()),
        "excludePrefixes": exclude_prefixes,
        "thresholds": {
            "staleDays": stale_days,
            "hardStaleDays": hard_stale_days,
            "lowConfidenceThreshold": low_conf,
            "minWordThin": min_word_thin,
        },
        "counts": {
            "reviewed": len(reviewed_rows),
            "excluded": len(excluded_rows),
            "protected": protected_count,
        },
        "actionCounts": [
            {"action": action, "count": int(count)}
            for action, count in sorted(action_counter.items(), key=lambda kv: (-kv[1], kv[0]))
        ],
        "topCandidates": top_candidates,
        "readmeInventory": readmes,
        "topOrphans": orphans,
        "duplicateTitles": dupes[:40],
        "files": analyzed,
    }

    write_text(json_out, json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
    write_text(md_out, build_markdown(payload))
    print(f"[generate-markdown-hygiene] wrote {md_out}")
    print(f"[generate-markdown-hygiene] wrote {json_out}")
    print(f"[generate-markdown-hygiene] reviewed={len(reviewed_rows)} excluded={len(excluded_rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
