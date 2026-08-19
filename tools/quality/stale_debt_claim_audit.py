#!/usr/bin/env python3
from __future__ import annotations

"""Find stale closure-debt claims whose named targets already exist.

This is an observability tool.  It does not prove that a debt is paid.  It finds
source lines that claim something is missing/open and cross-checks the names
mentioned on those lines against tracked Lean declarations.  Every hit is a
candidate for source inspection and Lean validation.
"""

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


ROOT = repo_root()

DEFAULT_ROOTS = ("lean", "docs", "tools")
DEFAULT_SUFFIXES = (".lean", ".md", ".py")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?(?:private\s+|protected\s+|local\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque|constant)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")

DEBT_RE = re.compile(
    r"\b("
    r"open\s+debt|closure\s+debt|remaining\s+debt|real\s+open\s+debt|"
    r"missing\s+(?:theorem|lemma|owner|declaration|bridge|construction|substrate)|"
    r"not\s+formalized|not\s+yet\s+formalized|incomplete|placeholder|"
    r"conjectural\s+interface|conditional\s+interface|TODO|FIXME|proof\s+hole|unproven|"
    r"external\s+certificate"
    r")\b",
    re.IGNORECASE,
)
NEGATED_DEBT_RE = re.compile(
    r"\b(no|not|without|avoids?|replacing|closed|already\s+closed)\b.{0,80}"
    r"\b(debt|missing|placeholder|sorry|axiom|assumption)\b",
    re.IGNORECASE,
)
RESOLUTION_LANGUAGE_RE = re.compile(
    r"\b(resolves?|already|no\s+longer|refines?|forgetful\s+adapter|existing|proof-carrying)\b",
    re.IGNORECASE,
)
BACKTICK_RE = re.compile(r"`([^`\n]+)`")
IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_'.]*\b")

COMMON_TOKENS = {
    "a",
    "after",
    "an",
    "and",
    "audit",
    "before",
    "bridge",
    "bucket",
    "build",
    "by",
    "canonical",
    "chain",
    "checkpoint",
    "classical",
    "closure",
    "counts",
    "current",
    "debt",
    "def",
    "defect",
    "evaluate",
    "exact",
    "false",
    "file",
    "finite",
    "fixme",
    "flow",
    "for",
    "from",
    "full",
    "global",
    "grade",
    "graph",
    "identity",
    "if",
    "in",
    "index",
    "kernel",
    "lean",
    "lemma",
    "mathlib",
    "metric",
    "momentum",
    "namespace",
    "no",
    "none",
    "not",
    "owner",
    "packet",
    "partition",
    "plus",
    "potential",
    "product",
    "prop",
    "rfl",
    "shape",
    "interface",
    "sorry",
    "split",
    "state",
    "step",
    "system",
    "target",
    "the",
    "theorem",
    "theta",
    "this",
    "todo",
    "total",
    "trivial",
    "true",
    "type",
    "unit",
    "with",
    "zero",
    "zeta",
}


@dataclass(frozen=True)
class Decl:
    name: str
    fqname: str
    kind: str
    file: str
    line: int
    has_body_hole: bool


@dataclass(frozen=True)
class DebtLine:
    file: str
    line: int
    text: str
    terms: list[tuple[str, str]]


@dataclass(frozen=True)
class Candidate:
    file: str
    line: int
    text: str
    term: str
    term_source: str
    confidence: str
    matches: list[dict[str, object]]


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def git_tracked_files() -> set[str]:
    proc = subprocess.run(
        ["git", "ls-files"],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise SystemExit(f"git ls-files failed: {proc.stderr.strip()}")
    return {line.strip() for line in proc.stdout.splitlines() if line.strip()}


def iter_source_files(roots: Iterable[Path], suffixes: set[str], tracked: set[str]) -> list[Path]:
    skip_dirs = {
        ".git",
        ".lake",
        ".venv",
        ".venv-py312",
        ".venv-123",
        "artifacts",
        "external_refs",
        "lake-packages",
        "node_modules",
        "__pycache__",
    }
    out: list[Path] = []
    for root in roots:
        if root.is_file():
            candidates = [root]
        else:
            candidates = sorted(path for path in root.rglob("*") if path.is_file())
        for path in candidates:
            if path.suffix not in suffixes:
                continue
            if any(part in skip_dirs for part in path.relative_to(ROOT).parts):
                continue
            if rel(path) not in tracked:
                continue
            out.append(path)
    return sorted(set(out))


def scan_decls(path: Path) -> list[Decl]:
    if path.suffix != ".lean":
        return []
    lines = path.read_text(encoding="utf-8").splitlines()
    namespace_stack: list[str] = []
    raw: list[tuple[str, str, str, int, int]] = []
    for idx, line in enumerate(lines, start=1):
        ns = NAMESPACE_RE.match(line)
        if ns:
            namespace_stack.append(ns.group(1))
            continue
        if END_RE.match(line) and namespace_stack:
            namespace_stack.pop()
            continue
        decl = DECL_RE.match(line)
        if not decl:
            continue
        name = decl.group("name")
        kind = decl.group("kind")
        fqname = ".".join([*namespace_stack, name]) if namespace_stack else name
        raw.append((name, fqname, kind, idx, idx))

    out: list[Decl] = []
    starts = [row[3] for row in raw] + [len(lines) + 1]
    for pos, (name, fqname, kind, line, _end) in enumerate(raw):
        start = line
        end = starts[pos + 1] - 1
        block = "\n".join(lines[start - 1 : end])
        out.append(
            Decl(
                name=name,
                fqname=fqname,
                kind=kind,
                file=rel(path),
                line=line,
                has_body_hole=bool(re.search(r"(?<!\w)(sorry|admit)(?!\w)", block)),
            )
        )
    return out


def clean_term(raw: str) -> str | None:
    term = raw.strip()
    term = term.removeprefix("#check ").strip()
    term = term.strip(".,;:()[]{}")
    if not term:
        return None
    if " " in term:
        return None
    if term.lower() in COMMON_TOKENS:
        return None
    if "." not in term and len(term) < 3:
        return None
    if "." in term and any(part == "" for part in term.split(".")):
        return None
    if not IDENT_RE.fullmatch(term):
        return None
    return term


def extract_terms(line: str, *, include_bare: bool) -> list[tuple[str, str]]:
    terms: list[tuple[str, str]] = []
    for match in BACKTICK_RE.finditer(line):
        term = clean_term(match.group(1))
        if term is not None:
            terms.append((term, "backtick"))
    if terms:
        return list(dict.fromkeys(terms))

    # Bare identifiers are much noisier.  Only use them on lines whose language
    # strongly implies "the target named here is missing".
    if not include_bare:
        return []
    lowered = line.lower()
    if not any(marker in lowered for marker in ("missing", "open debt", "remaining debt", "not formalized")):
        return []
    for match in IDENT_RE.finditer(line):
        term = clean_term(match.group(0))
        if term is not None and len(term) >= 4:
            terms.append((term, "bare"))
    return list(dict.fromkeys(terms))


def scan_debt_lines(path: Path, *, include_bare: bool) -> list[DebtLine]:
    out: list[DebtLine] = []
    for idx, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not DEBT_RE.search(line):
            continue
        if NEGATED_DEBT_RE.search(line):
            continue
        if RESOLUTION_LANGUAGE_RE.search(line):
            continue
        terms = extract_terms(line, include_bare=include_bare)
        out.append(DebtLine(file=rel(path), line=idx, text=line.strip(), terms=terms))
    return out


def build_decl_index(decls: list[Decl]) -> tuple[dict[str, list[Decl]], dict[str, list[Decl]]]:
    by_leaf: dict[str, list[Decl]] = defaultdict(list)
    by_full: dict[str, list[Decl]] = defaultdict(list)
    for decl in decls:
        by_leaf[decl.name].append(decl)
        by_full[decl.fqname].append(decl)
    return by_leaf, by_full


def find_matches(term: str, by_leaf: dict[str, list[Decl]], by_full: dict[str, list[Decl]]) -> list[Decl]:
    matches = list(by_full.get(term, []))
    if "." not in term:
        matches.extend(by_leaf.get(term, []))
    seen: set[tuple[str, int, str]] = set()
    unique: list[Decl] = []
    for decl in matches:
        key = (decl.file, decl.line, decl.fqname)
        if key in seen:
            continue
        seen.add(key)
        unique.append(decl)
    return unique


def classify_confidence(file: str, matches: list[Decl], source: str) -> str:
    external = [match for match in matches if match.file != file]
    prefix = "exact-backtick" if source == "backtick" else "bare-name"
    if external:
        return f"{prefix}-external-declaration"
    return f"{prefix}-same-file-declaration"


def make_candidates(debt_lines: list[DebtLine], by_leaf: dict[str, list[Decl]], by_full: dict[str, list[Decl]]) -> list[Candidate]:
    out: list[Candidate] = []
    for row in debt_lines:
        for term, source in row.terms:
            matches = find_matches(term, by_leaf, by_full)
            if not matches:
                continue
            out.append(
                Candidate(
                    file=row.file,
                    line=row.line,
                    text=row.text,
                    term=term,
                    term_source=source,
                    confidence=classify_confidence(row.file, matches, source),
                    matches=[
                        {
                            "name": decl.name,
                            "fqname": decl.fqname,
                            "kind": decl.kind,
                            "file": decl.file,
                            "line": decl.line,
                            "has_body_hole": decl.has_body_hole,
                        }
                        for decl in matches
                    ],
                )
            )
    out.sort(key=lambda c: (c.file, c.line, c.term, c.confidence))
    return out


def write_markdown(path: Path, payload: dict[str, object]) -> None:
    candidates = [Candidate(**row) for row in payload["candidates"]]  # type: ignore[index]
    lines: list[str] = []
    lines.append("# Stale Debt Claim Audit")
    lines.append("")
    lines.append("This report is navigation evidence only.  A candidate means a debt line names")
    lines.append("a declaration that already exists somewhere in tracked Lean source.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    summary = payload["summary"]  # type: ignore[index]
    assert isinstance(summary, dict)
    for key, value in summary.items():
        lines.append(f"- {key}: `{value}`")
    lines.append("")

    if not candidates:
        lines.append("No stale-debt candidates found.")
        lines.append("")
        path.write_text("\n".join(lines), encoding="utf-8")
        return

    lines.append("## Candidates")
    lines.append("")
    lines.append("| debt line | term | confidence | matching declarations |")
    lines.append("| --- | --- | --- | --- |")
    for cand in candidates:
        matches = []
        for match in cand.matches:  # type: ignore[attr-defined]
            hole = " hole" if match["has_body_hole"] else ""
            matches.append(
                f"`{match['fqname']}` ({match['kind']}, `{match['file']}:{match['line']}`{hole})"
            )
        lines.append(
            f"| `{cand.file}:{cand.line}` | `{cand.term}` | `{cand.confidence}` | "
            f"{'<br>'.join(matches)} |"
        )
    lines.append("")

    lines.append("## Source Context")
    lines.append("")
    for cand in candidates:
        lines.append(f"### `{cand.file}:{cand.line}`")
        lines.append("")
        lines.append(f"- term: `{cand.term}`")
        lines.append(f"- confidence: `{cand.confidence}`")
        lines.append("")
        lines.append("```text")
        lines.append(cand.text)
        lines.append("```")
        lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Find debt-language lines that reference declarations already present in tracked Lean source."
    )
    parser.add_argument("--root", action="append", default=[], help="File or directory to scan. Repeatable.")
    parser.add_argument("--suffix", action="append", default=[], help="Source suffix to include. Repeatable.")
    parser.add_argument("--json-out", default="artifacts/quality/stale_debt_claim_audit.json")
    parser.add_argument("--md-out", default="artifacts/quality/stale_debt_claim_audit.md")
    parser.add_argument("--max-candidates", type=int, default=0, help="Limit candidates in output after sorting.")
    parser.add_argument(
        "--include-bare",
        action="store_true",
        help="Also match non-backticked identifiers on debt-language lines. Noisier; off by default.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    roots = [normalize_user_path(raw, ROOT) for raw in (args.root or DEFAULT_ROOTS)]
    suffixes = set(args.suffix or DEFAULT_SUFFIXES)
    tracked = git_tracked_files()
    source_files = iter_source_files(roots, suffixes, tracked)

    decls: list[Decl] = []
    debt_lines: list[DebtLine] = []
    for path in source_files:
        decls.extend(scan_decls(path))
        debt_lines.extend(scan_debt_lines(path, include_bare=args.include_bare))

    by_leaf, by_full = build_decl_index(decls)
    candidates = make_candidates(debt_lines, by_leaf, by_full)
    if args.max_candidates > 0:
        candidates = candidates[: args.max_candidates]

    summary = {
        "source_files": len(source_files),
        "lean_declarations_indexed": len(decls),
        "debt_lines": len(debt_lines),
        "debt_lines_with_named_terms": sum(1 for row in debt_lines if row.terms),
        "include_bare": bool(args.include_bare),
        "stale_debt_candidates": len(candidates),
        "external_declaration_candidates": sum(
            1 for row in candidates if "external" in row.confidence
        ),
    }
    payload: dict[str, object] = {
        "schema": "info_geometry.stale_debt_claim_audit.v1",
        "roots": [rel(path) for path in roots],
        "suffixes": sorted(suffixes),
        "summary": summary,
        "candidates": [asdict(row) for row in candidates],
    }

    json_out = normalize_user_path(args.json_out, ROOT / args.json_out)
    md_out = normalize_user_path(args.md_out, ROOT / args.md_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    write_markdown(md_out, payload)
    print(
        "[stale-debt] "
        f"files={summary['source_files']} decls={summary['lean_declarations_indexed']} "
        f"debt_lines={summary['debt_lines']} candidates={summary['stale_debt_candidates']} "
        f"json={rel(json_out)} md={rel(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
