#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
from collections import Counter, defaultdict
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path


MARKER_RE = re.compile(
    r"copyright|all rights reserved|licensed under|spdx-license-identifier|"
    r"community license|gnu lesser general public license|proprietary|license as published by",
    re.IGNORECASE,
)

EXTERNAL_OWNER_RE = re.compile(
    r"meta platforms|national technology\s*&\s*engineering solutions|sandia|microsoft|google|apache software foundation",
    re.IGNORECASE,
)

BINARY_EXT = {
    ".png",
    ".jpg",
    ".jpeg",
    ".gif",
    ".pdf",
    ".zip",
    ".gz",
    ".tgz",
    ".tar",
    ".olean",
    ".so",
    ".dll",
    ".dylib",
    ".mp4",
    ".mov",
}

DEFAULT_SKIP_DIRS = {
    ".git",
    ".lake",
    ".build",
    ".venv",
    "__pycache__",
    "archive/evidence",
    "archive/public-release",
}


@dataclass
class Hit:
    line: int
    text: str


@dataclass
class FileFinding:
    path: str
    classification: str
    reason: str
    hits: list[Hit]


def run(cmd: list[str], cwd: Path) -> str:
    p = subprocess.run(cmd, cwd=str(cwd), check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return p.stdout


def load_owner_names(root: Path) -> list[str]:
    notice = root / "NOTICE"
    if not notice.exists():
        return []
    text = notice.read_text(encoding="utf-8", errors="ignore")
    names: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        # crude heuristic for person-name style entries
        if re.search(r"[A-Z][a-z]+ [A-Z][a-z]+", line):
            names.append(line)
    return names


def load_excluded_prefixes(root: Path) -> list[str]:
    p = root / "tools" / "infra" / "archive_excludes.txt"
    if not p.exists():
        return []
    out: list[str] = []
    for raw in p.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            out.append(line)
    return out


def is_text_file(path: Path) -> bool:
    if path.suffix.lower() in BINARY_EXT:
        return False
    try:
        with path.open("rb") as f:
            chunk = f.read(4096)
        if b"\x00" in chunk:
            return False
        return True
    except Exception:
        return False


def iter_files(root: Path, tracked_only: bool) -> list[Path]:
    if tracked_only:
        out = run(["git", "ls-files", "-z"], cwd=root)
        return [root / p for p in out.split("\0") if p]
    files: list[Path] = []
    for p in root.rglob("*"):
        if not p.is_file():
            continue
        rel = p.relative_to(root).as_posix()
        if any(rel == s or rel.startswith(f"{s}/") for s in DEFAULT_SKIP_DIRS):
            continue
        files.append(p)
    return files


def classify(rel: str, hits: list[Hit], owner_names: list[str], excluded_prefixes: list[str]) -> tuple[str, str]:
    if any(rel == x.rstrip("/") or rel.startswith(x.rstrip("/") + "/") for x in excluded_prefixes):
        return "third_party_or_reference", "path is in archive exclusion policy"

    joined = "\n".join(h.text for h in hits)
    if EXTERNAL_OWNER_RE.search(joined) or re.search(r"all rights reserved", joined, re.IGNORECASE):
        return "third_party_or_reference", "external owner/licensing markers in file text"

    for name in owner_names:
        if name and name.lower() in joined.lower():
            return "project_owned", "contains project owner name"

    if rel.startswith("external_refs/") or rel.startswith("interspec_src/"):
        return "third_party_or_reference", "known third-party reference directory"

    return "review_needed", "license marker found but ownership not auto-resolved"


def scan_file(path: Path, max_hits: int) -> list[Hit]:
    hits: list[Hit] = []
    try:
        with path.open("r", encoding="utf-8", errors="ignore") as f:
            for ln, raw in enumerate(f, start=1):
                if MARKER_RE.search(raw):
                    text = raw.strip()
                    if len(text) > 200:
                        text = text[:197] + "..."
                    hits.append(Hit(line=ln, text=text))
                    if len(hits) >= max_hits:
                        break
    except Exception:
        return []
    return hits


def write_markdown(
    out_path: Path,
    root: Path,
    findings: list[FileFinding],
    tracked_only: bool,
    total_files: int,
    owner_names: list[str],
    excluded_prefixes: list[str],
) -> None:
    by_class = Counter(f.classification for f in findings)
    by_top = Counter(Path(f.path).parts[0] if Path(f.path).parts else "." for f in findings)

    lines: list[str] = []
    lines.append("# Third-Party / License Deep Scan Report")
    lines.append("")
    lines.append(f"- Generated (UTC): `{datetime.now(timezone.utc).isoformat()}`")
    lines.append(f"- Repository root: `{root}`")
    lines.append(f"- Scan mode: `{'tracked-only' if tracked_only else 'all-files'}`")
    lines.append(f"- Files scanned: `{total_files}`")
    lines.append(f"- Files with license/copyright markers: `{len(findings)}`")
    lines.append("")
    lines.append("## Project owner names (NOTICE-derived)")
    if owner_names:
        for n in owner_names:
            lines.append(f"- `{n}`")
    else:
        lines.append("- none detected")
    lines.append("")
    lines.append("## Exclusion policy prefixes")
    if excluded_prefixes:
        for p in excluded_prefixes:
            lines.append(f"- `{p}`")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Classification summary")
    for cls, count in sorted(by_class.items(), key=lambda kv: (-kv[1], kv[0])):
        lines.append(f"- `{cls}`: **{count}**")
    lines.append("")
    lines.append("## Top-level directory distribution")
    for d, count in sorted(by_top.items(), key=lambda kv: (-kv[1], kv[0]))[:30]:
        lines.append(f"- `{d}`: {count}")
    lines.append("")

    for cls in ("third_party_or_reference", "review_needed", "project_owned"):
        subset = [f for f in findings if f.classification == cls]
        if not subset:
            continue
        lines.append(f"## {cls}")
        for f in sorted(subset, key=lambda x: x.path):
            lines.append(f"- `{f.path}`")
            lines.append(f"  - reason: {f.reason}")
            for h in f.hits:
                lines.append(f"  - hit: L{h.line} `{h.text}`")
        lines.append("")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Deep scan repository for third-party licensing/copyright markers.")
    parser.add_argument("--all-files", action="store_true", help="scan all files, not only tracked files")
    parser.add_argument("--max-hits", type=int, default=4, help="max hit lines kept per file")
    parser.add_argument(
        "--out",
        default="docs/ThirdPartyDeepScanReport.md",
        help="markdown output path",
    )
    parser.add_argument(
        "--json-out",
        default="",
        help="optional JSON output path",
    )
    args = parser.parse_args()

    root = Path(run(["git", "rev-parse", "--show-toplevel"], cwd=Path.cwd()).strip())
    tracked_only = not args.all_files
    owner_names = load_owner_names(root)
    excluded_prefixes = load_excluded_prefixes(root)

    files = iter_files(root, tracked_only=tracked_only)
    findings: list[FileFinding] = []
    for p in files:
        rel = p.relative_to(root).as_posix()
        if not is_text_file(p):
            continue
        hits = scan_file(p, max_hits=args.max_hits)
        if not hits:
            continue
        classification, reason = classify(rel, hits, owner_names, excluded_prefixes)
        findings.append(FileFinding(path=rel, classification=classification, reason=reason, hits=hits))

    out_path = (root / args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    write_markdown(
        out_path=out_path,
        root=root,
        findings=findings,
        tracked_only=tracked_only,
        total_files=len(files),
        owner_names=owner_names,
        excluded_prefixes=excluded_prefixes,
    )

    if args.json_out:
        jpath = (root / args.json_out).resolve()
        jpath.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "scan_mode": "all-files" if args.all_files else "tracked-only",
            "total_files_scanned": len(files),
            "owner_names": owner_names,
            "excluded_prefixes": excluded_prefixes,
            "findings": [
                {
                    **asdict(f),
                    "hits": [asdict(h) for h in f.hits],
                }
                for f in findings
            ],
        }
        jpath.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(f"[license-scan] scanned_files={len(files)} findings={len(findings)} out={out_path}")


if __name__ == "__main__":
    main()
