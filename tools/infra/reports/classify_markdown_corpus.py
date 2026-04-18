#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
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


DEFAULT_JSON_OUT = "reports/dag/markdown-classification.json"
DEFAULT_MD_OUT = "reports/dag/markdown-classification.md"
MARKDOWN_SUFFIXES = {".md", ".markdown"}

LABELS = (
    "operator_runbook",
    "architecture_design",
    "policy_governance",
    "contract_spec",
    "troubleshooting",
    "setup_operations",
    "generated_report",
    "generated_auto",
    "black_book",
    "reference_index",
    "research_note",
    "other",
)

PATH_RULES: tuple[tuple[str, str, float, str], ...] = (
    ("docs/black_books/", "black_book", 10.0, "path:black_books"),
    ("docs/auto/", "generated_auto", 9.0, "path:docs_auto"),
    ("reports/", "generated_report", 8.0, "path:reports"),
    ("docs/policy/", "policy_governance", 8.0, "path:docs_policy"),
    ("docs-map/", "reference_index", 6.0, "path:docs_map"),
)

PHRASE_RULES: tuple[tuple[str, str, float, str], ...] = (
    ("lake script run", "operator_runbook", 3.0, "phrase:lake_script_run"),
    ("python3 tools/infra", "operator_runbook", 2.5, "phrase:python3_tools_infra"),
    ("runbook", "operator_runbook", 2.0, "phrase:runbook"),
    ("quickstart", "operator_runbook", 2.0, "phrase:quickstart"),
    ("toolchain architecture", "architecture_design", 3.0, "phrase:toolchain_architecture"),
    ("architecture", "architecture_design", 1.3, "phrase:architecture"),
    ("execution graph", "architecture_design", 2.0, "phrase:execution_graph"),
    ("policy", "policy_governance", 1.8, "phrase:policy"),
    ("mandate", "policy_governance", 1.5, "phrase:mandate"),
    ("governance", "policy_governance", 1.6, "phrase:governance"),
    ("contract", "contract_spec", 2.2, "phrase:contract"),
    ("schema", "contract_spec", 1.7, "phrase:schema"),
    ("typed packet", "contract_spec", 2.0, "phrase:typed_packet"),
    ("troubleshooting", "troubleshooting", 2.5, "phrase:troubleshooting"),
    ("error:", "troubleshooting", 1.5, "phrase:error_colon"),
    ("fix:", "troubleshooting", 1.2, "phrase:fix_colon"),
    ("setup", "setup_operations", 1.7, "phrase:setup"),
    ("install", "setup_operations", 1.7, "phrase:install"),
    ("ssh", "setup_operations", 1.3, "phrase:ssh"),
    ("dgx spark", "setup_operations", 1.6, "phrase:dgx_spark"),
    ("generated:", "generated_report", 1.2, "phrase:generated"),
    ("wrote ", "generated_report", 1.2, "phrase:wrote"),
    ("black book", "black_book", 2.2, "phrase:black_book"),
    ("liber ", "black_book", 1.5, "phrase:liber"),
    ("index", "reference_index", 1.0, "phrase:index"),
    ("inventory", "reference_index", 1.2, "phrase:inventory"),
    ("synthesis", "research_note", 1.8, "phrase:synthesis"),
    ("theorem", "research_note", 1.1, "phrase:theorem"),
    ("lemma", "research_note", 1.1, "phrase:lemma"),
    ("proof", "research_note", 1.1, "phrase:proof"),
    ("modular", "research_note", 1.0, "phrase:modular"),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Classify all markdown files in the repository using path + content heuristics "
            "and produce JSON/Markdown reports."
        )
    )
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT)
    parser.add_argument(
        "--include-untracked",
        action="store_true",
        help="Include untracked non-ignored markdown files in addition to tracked files.",
    )
    parser.add_argument("--top-low-confidence", type=int, default=50)
    parser.add_argument("--max-reasons-per-label", type=int, default=8)
    return parser.parse_args()


def tracked_files(root: Path) -> list[str]:
    raw = subprocess.check_output(["git", "ls-files", "-z"], cwd=root)
    return sorted(chunk for chunk in raw.decode("utf-8", errors="replace").split("\0") if chunk)


def untracked_files(root: Path) -> list[str]:
    raw = subprocess.check_output(
        ["git", "ls-files", "-z", "--others", "--exclude-standard"],
        cwd=root,
    )
    return sorted(chunk for chunk in raw.decode("utf-8", errors="replace").split("\0") if chunk)


def is_markdown(rel: str) -> bool:
    return Path(rel).suffix.lower() in MARKDOWN_SUFFIXES


def command_line_count(text: str) -> int:
    count = 0
    for line in text.splitlines():
        if re.match(r"^\s*(python3|python|lake|ssh|rsync|git|docker|npx|uv|bash)\b", line):
            count += 1
    return count


def heading_count(text: str) -> int:
    return sum(1 for line in text.splitlines() if re.match(r"^\s*#{1,6}\s+", line))


def fenced_code_count(text: str) -> int:
    return text.count("```") // 2


def tokenize(text: str) -> list[str]:
    return re.findall(r"[a-zA-Z0-9_]+", text.lower())


def add_score(
    scores: dict[str, float],
    reasons: dict[str, list[str]],
    label: str,
    weight: float,
    reason: str,
    *,
    max_reasons_per_label: int,
) -> None:
    if label not in LABELS:
        return
    scores[label] += weight
    rr = reasons[label]
    if len(rr) < max_reasons_per_label:
        rr.append(reason)


def classify_markdown(
    rel_path: str,
    text: str,
    *,
    max_reasons_per_label: int,
) -> dict[str, Any]:
    lower_path = rel_path.lower()
    lower_text = text.lower()

    scores: dict[str, float] = defaultdict(float)
    reasons: dict[str, list[str]] = defaultdict(list)

    # Path-first rules.
    for prefix, label, weight, reason in PATH_RULES:
        if lower_path.startswith(prefix):
            add_score(
                scores,
                reasons,
                label,
                weight,
                reason,
                max_reasons_per_label=max_reasons_per_label,
            )

    # Filename/path token rules.
    if "troubleshoot" in lower_path:
        add_score(scores, reasons, "troubleshooting", 5.0, "path:troubleshoot", max_reasons_per_label=max_reasons_per_label)
    if "quickstart" in lower_path:
        add_score(scores, reasons, "operator_runbook", 4.0, "path:quickstart", max_reasons_per_label=max_reasons_per_label)
    if "methodology" in lower_path:
        add_score(scores, reasons, "operator_runbook", 2.0, "path:methodology", max_reasons_per_label=max_reasons_per_label)
        add_score(scores, reasons, "architecture_design", 1.5, "path:methodology", max_reasons_per_label=max_reasons_per_label)
    if "architecture" in lower_path:
        add_score(scores, reasons, "architecture_design", 4.0, "path:architecture", max_reasons_per_label=max_reasons_per_label)
    if "policy" in lower_path or "manifesto" in lower_path:
        add_score(scores, reasons, "policy_governance", 4.0, "path:policy_or_manifesto", max_reasons_per_label=max_reasons_per_label)
    if "contract" in lower_path or "blueprint" in lower_path:
        add_score(scores, reasons, "contract_spec", 4.0, "path:contract_or_blueprint", max_reasons_per_label=max_reasons_per_label)
    if "setup" in lower_path or "deploy" in lower_path:
        add_score(scores, reasons, "setup_operations", 4.0, "path:setup_or_deploy", max_reasons_per_label=max_reasons_per_label)
    if "index" in lower_path or "inventory" in lower_path or "map" in lower_path:
        add_score(scores, reasons, "reference_index", 2.3, "path:index_inventory_map", max_reasons_per_label=max_reasons_per_label)

    # Content phrase rules.
    for phrase, label, weight, reason in PHRASE_RULES:
        if phrase in lower_text:
            add_score(
                scores,
                reasons,
                label,
                weight,
                reason,
                max_reasons_per_label=max_reasons_per_label,
            )

    # Structural signals from content shape.
    cmd_count = command_line_count(text)
    headings = heading_count(text)
    fences = fenced_code_count(text)
    token_count = len(tokenize(text))

    if cmd_count >= 3:
        add_score(
            scores,
            reasons,
            "operator_runbook",
            min(4.0, 1.0 + cmd_count * 0.35),
            f"shape:command_lines={cmd_count}",
            max_reasons_per_label=max_reasons_per_label,
        )
    if cmd_count >= 1 and ("ssh" in lower_text or "rsync" in lower_text):
        add_score(
            scores,
            reasons,
            "setup_operations",
            1.5,
            "shape:ssh_rsync_commands",
            max_reasons_per_label=max_reasons_per_label,
        )
    if headings >= 8:
        add_score(
            scores,
            reasons,
            "reference_index",
            1.2,
            f"shape:many_headings={headings}",
            max_reasons_per_label=max_reasons_per_label,
        )
    if fences >= 2:
        add_score(
            scores,
            reasons,
            "operator_runbook",
            1.0,
            f"shape:code_fences={fences}",
            max_reasons_per_label=max_reasons_per_label,
        )
    if token_count > 2200:
        add_score(
            scores,
            reasons,
            "research_note",
            0.8,
            f"shape:long_form_tokens={token_count}",
            max_reasons_per_label=max_reasons_per_label,
        )

    # Fallback to "other" when everything is weak.
    if not scores:
        scores["other"] = 1.0
        reasons["other"] = ["fallback:no_rules_matched"]

    ranked = sorted(scores.items(), key=lambda kv: (-kv[1], kv[0]))
    primary_label, primary_score = ranked[0]
    top3_sum = sum(score for _, score in ranked[:3])
    confidence = float(primary_score / top3_sum) if top3_sum > 0 else 0.0

    secondary: list[str] = []
    if len(ranked) > 1:
        threshold = max(2.0, primary_score * 0.45)
        for label, score in ranked[1:]:
            if score >= threshold:
                secondary.append(label)

    labels_payload = [
        {
            "label": label,
            "score": round(score, 4),
            "reasons": reasons.get(label, []),
        }
        for label, score in ranked
    ]

    return {
        "path": rel_path,
        "primaryLabel": primary_label,
        "confidence": round(confidence, 6),
        "secondaryLabels": secondary,
        "signals": {
            "wordCount": token_count,
            "headingCount": headings,
            "codeFenceCount": fences,
            "commandLineCount": cmd_count,
        },
        "labels": labels_payload,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    counts = payload["counts"]
    lines: list[str] = []
    lines.append("# Markdown Classification Report")
    lines.append("")
    lines.append(f"Generated: `{payload['generatedAt']}`")
    lines.append(f"Universe: `{counts['markdownFiles']}` markdown files")
    lines.append(f"Tracked: `{counts['trackedFiles']}` | Untracked included: `{counts['untrackedFiles']}`")
    lines.append("")
    lines.append("## Primary Label Distribution")
    lines.append("")
    lines.append("| label | files |")
    lines.append("|---|---:|")
    for row in payload["primaryLabelCounts"]:
        lines.append(f"| `{row['label']}` | {row['count']} |")
    lines.append("")
    lines.append("## Low-Confidence Files")
    lines.append("")
    lines.append("| confidence | primary | path |")
    lines.append("|---:|---|---|")
    for row in payload["lowConfidenceFiles"]:
        lines.append(
            f"| {row['confidence']:.3f} | `{row['primaryLabel']}` | `{row['path']}` |"
        )
    lines.append("")
    lines.append("## Label Examples")
    lines.append("")
    for label in LABELS:
        examples = payload["labelExamples"].get(label, [])
        if not examples:
            continue
        lines.append(f"### {label}")
        for ex in examples:
            lines.append(f"- `{ex}`")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root()
    tracked = tracked_files(root)
    untracked = untracked_files(root) if args.include_untracked else []
    files = sorted(set(tracked) | set(untracked))
    markdown_files = [rel for rel in files if is_markdown(rel)]

    rows: list[dict[str, Any]] = []
    missing_paths: list[str] = []
    for rel in markdown_files:
        path = root / rel
        if not path.exists():
            missing_paths.append(rel)
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            text = ""
        rows.append(
            classify_markdown(
                rel,
                text,
                max_reasons_per_label=max(1, int(args.max_reasons_per_label)),
            )
        )

    rows.sort(key=lambda r: r["path"])
    primary_counter = Counter(str(row.get("primaryLabel", "other")) for row in rows)

    low_conf = sorted(
        rows,
        key=lambda r: (float(r.get("confidence", 0.0)), str(r.get("path", ""))),
    )[: max(0, int(args.top_low_confidence))]
    low_conf_rows = [
        {
            "path": row["path"],
            "primaryLabel": row["primaryLabel"],
            "confidence": float(row["confidence"]),
        }
        for row in low_conf
    ]

    label_examples: dict[str, list[str]] = {}
    for label in LABELS:
        subset = [row for row in rows if row.get("primaryLabel") == label]
        subset.sort(key=lambda r: (-float(r.get("confidence", 0.0)), str(r.get("path", ""))))
        label_examples[label] = [str(row["path"]) for row in subset[:5]]

    payload = {
        "generatedAt": generated_timestamp(),
        "includeUntracked": bool(args.include_untracked),
        "counts": {
            "trackedFiles": len(tracked),
            "untrackedFiles": len(untracked),
            "markdownFiles": len(rows),
            "markdownFilesCandidate": len(markdown_files),
            "markdownFilesScanned": len(rows),
            "markdownFilesMissingOnDisk": len(missing_paths),
        },
        "missingPaths": missing_paths,
        "labels": list(LABELS),
        "primaryLabelCounts": [
            {"label": label, "count": int(primary_counter.get(label, 0))}
            for label in sorted(LABELS, key=lambda lb: (-primary_counter.get(lb, 0), lb))
            if primary_counter.get(label, 0) > 0
        ],
        "lowConfidenceFiles": low_conf_rows,
        "labelExamples": label_examples,
        "files": rows,
    }

    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)
    write_text(json_out, json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
    write_text(md_out, render_markdown(payload))

    print(f"[classify-markdown-corpus] wrote {md_out}")
    print(f"[classify-markdown-corpus] wrote {json_out}")
    print(f"[classify-markdown-corpus] markdown_files={len(markdown_files)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
