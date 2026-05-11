#!/usr/bin/env python3
from __future__ import annotations

"""
Closure Debt Crawler for Lean repositories.

Goal:
- Crawl Lean files recursively.
- Detect temporary trust/debt constructs (proof holes, axioms, postulates, opaque stubs,
  witness packaging, placeholder assumptions, skeletal proofs, vacuous props).
- Emit per-file debt reports plus aggregate summary.

This is a heuristic auditor; Lean kernel remains theorem-truth authority.
"""

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality import audit_constructivity
else:
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality import audit_constructivity

ROOT = repo_root()

DECL_HEADER_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:partial\s+)?(?:private\s+|protected\s+|local\s+)?"
    r"(theorem|lemma|example|def|abbrev|structure|class|instance|axiom|postulate|inductive)\b"
    r"\s+([A-Za-z0-9_'.]+)",
    re.M,
)

PROOF_HOLE_RE = re.compile(r"\b(?:sorry|admit|sorryAx|admitAx)\b")
AXIOM_DECL_RE = re.compile(r"^\s*axiom\b", re.M)
POSTULATE_DECL_RE = re.compile(r"^\s*postulate\b", re.M)
OPAQUE_DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+|local\s+)?opaque\b", re.M)

VAR_ASSUME_RE = re.compile(r"^\s*variable\s*\([^\n]*:[^\n]*\)\s*$", re.M)
WITNESS_FIELD_RE = re.compile(r"(?m)^\s*([A-Za-z0-9_']+_valid)\s*:\s*([A-Za-z0-9_'.]+)\s*$")
UNIVERSAL_TRUE_FIELD_RE = re.compile(r"(?m)^\s*[A-Za-z0-9_']+\s*:\s*∀\s+[^\n]*,\s*True\s*$")

# placeholder naming conventions discussed in the session
PLACEHOLDER_NAME_RE = re.compile(r"^(?:external|hyp|unproven|todo|stub|bridge)_", re.I)

VacuousPropRe = re.compile(
    r"(?ms)^\s*(?:theorem|lemma|def|abbrev)\s+[A-Za-z0-9_'.]+\b"
    r"[\s\S]{0,700}?:\s*Prop\s*:=\s*(?:--[^\n]*\n\s*)*(?:True|False)\b"
)

SKELETAL_ONE_LINER_RE = re.compile(
    r"(?ms)^\s*(?:theorem|lemma|example)\s+[A-Za-z0-9_'.]+\b"
    r"[\s\S]{0,900}?:=\s*(?:by\s*)?(?:rfl|trivial|simp|simpa|aesop|linarith|omega|ring|exact\s+True\.intro)\b"
)

EXIST_PACKAGING_RE = re.compile(r"\b(?:Nonempty|Exists)\b|∃")


@dataclass(frozen=True)
class Finding:
    category: str
    severity: str  # hard|soft|advisory
    line: int
    declaration_kind: str
    declaration_name: str
    detail: str


@dataclass(frozen=True)
class FileReport:
    path: str
    module: str
    status: str  # clean|advisory|open_gap
    debt_score: int
    hard_count: int
    soft_count: int
    advisory_count: int
    finding_count: int
    findings: list[Finding]


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def module_name(path: Path) -> str:
    try:
        rp = path.resolve().relative_to(ROOT / "lean").with_suffix("").as_posix()
        return rp.replace("/", ".")
    except ValueError:
        try:
            rp = path.resolve().relative_to(ROOT).with_suffix("").as_posix()
            return rp.replace("/", ".")
        except ValueError:
            return path.stem


def line_of(text: str, offset: int) -> int:
    return audit_constructivity.line_of(text, offset)


def strip_comments(text: str) -> str:
    return audit_constructivity.strip_comments(text, strip_strings=True, strip_quoted_identifiers=True)


def iter_lean_files(root: Path) -> Iterable[Path]:
    if root.is_file():
        if root.suffix == ".lean":
            yield root
        return

    skip_dirs = {".git", ".lake", "lake-packages", ".cache", "node_modules", ".venv"}
    for path in sorted(root.rglob("*.lean")):
        if not path.is_file():
            continue
        if any(part in skip_dirs for part in path.parts):
            continue
        yield path


def find_decl_blocks(clean_text: str) -> list[tuple[str, str, int, str]]:
    blocks: list[tuple[str, str, int, str]] = []
    headers = list(DECL_HEADER_RE.finditer(clean_text))
    for idx, m in enumerate(headers):
        kind = m.group(1)
        name = m.group(2)
        start = m.start()
        end = headers[idx + 1].start() if idx + 1 < len(headers) else len(clean_text)
        blocks.append((kind, name, line_of(clean_text, start), clean_text[start:end]))
    return blocks


def proof_body(block: str) -> str:
    idx = block.find(":=")
    if idx < 0:
        return ""
    return block[idx + 2 :].strip()


def classify_block(kind: str, name: str, line: int, block: str) -> list[Finding]:
    out: list[Finding] = []

    if kind in {"axiom", "postulate"}:
        out.append(
            Finding(
                category="global-assumption",
                severity="hard",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail=f"{kind} declaration introduces global trust debt",
            )
        )

    if PROOF_HOLE_RE.search(block):
        out.append(
            Finding(
                category="proof-hole",
                severity="hard",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration body contains sorry/admit placeholder",
            )
        )

    body = proof_body(block)

    if kind in {"theorem", "lemma", "example"} and body and SKELETAL_ONE_LINER_RE.match(block):
        out.append(
            Finding(
                category="skeletal-proof",
                severity="soft",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="proof appears to close via minimal tactic one-liner",
            )
        )

    if PLACEHOLDER_NAME_RE.match(name):
        out.append(
            Finding(
                category="placeholder-naming",
                severity="advisory",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration name indicates temporary/external hypothesis surface",
            )
        )

    if EXIST_PACKAGING_RE.search(block) and kind in {"theorem", "lemma", "def", "abbrev", "structure", "class"}:
        out.append(
            Finding(
                category="existential-packaging",
                severity="advisory",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration uses Nonempty/Exists packaging; verify eventual constructive readback",
            )
        )

    return out


def audit_file(path: Path) -> FileReport:
    raw = path.read_text(encoding="utf-8")
    clean = strip_comments(raw)

    findings: list[Finding] = []

    # File-level scans
    for m in AXIOM_DECL_RE.finditer(clean):
        findings.append(
            Finding(
                category="axiom-token",
                severity="hard",
                line=line_of(clean, m.start()),
                declaration_kind="file",
                declaration_name="<file-level>",
                detail="axiom token detected",
            )
        )

    for m in POSTULATE_DECL_RE.finditer(clean):
        findings.append(
            Finding(
                category="postulate-token",
                severity="hard",
                line=line_of(clean, m.start()),
                declaration_kind="file",
                declaration_name="<file-level>",
                detail="postulate token detected",
            )
        )

    for m in OPAQUE_DECL_RE.finditer(clean):
        findings.append(
            Finding(
                category="opaque-stub",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="opaque",
                declaration_name="<opaque>",
                detail="opaque declaration found; ensure behavior is justified by proved lemmas",
            )
        )

    for m in VAR_ASSUME_RE.finditer(clean):
        findings.append(
            Finding(
                category="injected-hypothesis-surface",
                severity="advisory",
                line=line_of(clean, m.start()),
                declaration_kind="variable",
                declaration_name="<section-variable>",
                detail="section variable assumption detected (valid pattern; track for closure debt)",
            )
        )

    for m in VacuousPropRe.finditer(clean):
        findings.append(
            Finding(
                category="vacuous-prop",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="prop",
                declaration_name="<vacuous>",
                detail="Prop declaration appears to reduce to True/False",
            )
        )

    for m in WITNESS_FIELD_RE.finditer(clean):
        findings.append(
            Finding(
                category="witness-field-projection",
                severity="advisory",
                line=line_of(clean, m.start()),
                declaration_kind="structure-field",
                declaration_name=m.group(1),
                detail=f"witness field `{m.group(1)} : {m.group(2)}` detected; verify owner-level derivation",
            )
        )

    for m in UNIVERSAL_TRUE_FIELD_RE.finditer(clean):
        findings.append(
            Finding(
                category="placeholder-law",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="structure-field",
                declaration_name="<forall-true>",
                detail="field with `∀ ..., True` detected",
            )
        )

    # Declaration-level scans
    for kind, name, line, block in find_decl_blocks(clean):
        findings.extend(classify_block(kind, name, line, block))

    # Deduplicate
    dedup: dict[tuple[str, str, int, str, str], Finding] = {}
    for f in findings:
        key = (f.category, f.severity, f.line, f.declaration_kind, f.declaration_name)
        dedup[key] = f
    findings = sorted(dedup.values(), key=lambda x: (x.line, x.severity, x.category, x.declaration_name))

    hard = sum(1 for f in findings if f.severity == "hard")
    soft = sum(1 for f in findings if f.severity == "soft")
    advisory = sum(1 for f in findings if f.severity == "advisory")

    score = hard * 5 + soft * 2 + advisory
    if hard > 0:
        status = "open_gap"
    elif soft > 0 or advisory > 0:
        status = "advisory"
    else:
        status = "clean"

    return FileReport(
        path=rel(path),
        module=module_name(path),
        status=status,
        debt_score=score,
        hard_count=hard,
        soft_count=soft,
        advisory_count=advisory,
        finding_count=len(findings),
        findings=findings,
    )


def build_payload(root: Path, reports: list[FileReport]) -> dict[str, object]:
    hard_total = sum(r.hard_count for r in reports)
    soft_total = sum(r.soft_count for r in reports)
    advisory_total = sum(r.advisory_count for r in reports)

    status_counts = {
        "clean": sum(1 for r in reports if r.status == "clean"),
        "advisory": sum(1 for r in reports if r.status == "advisory"),
        "open_gap": sum(1 for r in reports if r.status == "open_gap"),
    }

    top = sorted(reports, key=lambda r: (-r.debt_score, -r.hard_count, -r.soft_count, r.path))[:50]

    return {
        "schema": "info_geometry.closure_debt_crawler.v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": rel(root),
        "summary": {
            "file_count": len(reports),
            "status_counts": status_counts,
            "finding_count": hard_total + soft_total + advisory_total,
            "hard_count": hard_total,
            "soft_count": soft_total,
            "advisory_count": advisory_total,
        },
        "top_debt_files": [asdict(r) for r in top],
        "files": [
            {
                **asdict(r),
                "findings": [asdict(f) for f in r.findings],
            }
            for r in reports
        ],
    }


def build_markdown(payload: dict[str, object]) -> str:
    summary = payload["summary"]
    lines: list[str] = []
    lines.append("# Lean Closure Debt Crawler Report")
    lines.append("")
    lines.append(f"Generated: `{payload['generated_at']}`")
    lines.append(f"Root: `{payload['root']}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Files scanned: **{summary['file_count']}**")
    lines.append(f"- Findings: **{summary['finding_count']}**")
    lines.append(f"- Hard: **{summary['hard_count']}**")
    lines.append(f"- Soft: **{summary['soft_count']}**")
    lines.append(f"- Advisory: **{summary['advisory_count']}**")
    status = summary["status_counts"]
    lines.append(
        "- File status counts: "
        f"clean={status['clean']}, advisory={status['advisory']}, open_gap={status['open_gap']}"
    )
    lines.append("")

    lines.append("## Per-file status")
    lines.append("")
    lines.append("| file | status | debt_score | hard | soft | advisory | findings |")
    lines.append("| --- | --- | ---: | ---: | ---: | ---: | ---: |")
    for row in payload["files"]:
        lines.append(
            f"| `{row['path']}` | `{row['status']}` | {row['debt_score']} | {row['hard_count']} | {row['soft_count']} | {row['advisory_count']} | {row['finding_count']} |"
        )

    lines.append("")
    lines.append("## Findings by file")
    lines.append("")
    for row in payload["files"]:
        lines.append(f"### `{row['path']}`")
        lines.append(f"- module: `{row['module']}`")
        lines.append(f"- status: `{row['status']}`")
        lines.append(f"- debt_score: `{row['debt_score']}`")
        if not row["findings"]:
            lines.append("- findings: none")
            lines.append("")
            continue
        lines.append("- findings:")
        for f in row["findings"]:
            lines.append(
                f"  - L{f['line']} [{f['severity']}] `{f['category']}` in `{f['declaration_kind']} {f['declaration_name']}` — {f['detail']}"
            )
        lines.append("")

    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Crawl Lean files and produce detailed per-file closure debt report for temporary assumptions, "
            "proof holes, stubs, and witness-packaging surfaces."
        )
    )
    parser.add_argument("--root", default=".", help="Directory or .lean file to scan")
    parser.add_argument("--json-out", default="reports/audit/closure-debt-crawler.json")
    parser.add_argument("--md-out", default="reports/audit/closure-debt-crawler.md")
    parser.add_argument("--strict", action="store_true", help="Exit nonzero when any hard finding exists")
    parser.add_argument("--print-summary", action="store_true", help="Print compact summary to stdout")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = normalize_user_path(args.root, ROOT)
    reports = [audit_file(path) for path in iter_lean_files(root)]
    reports.sort(key=lambda r: r.path)

    payload = build_payload(root, reports)

    json_out = normalize_user_path(args.json_out, ROOT / "reports" / "audit" / "closure-debt-crawler.json")
    md_out = normalize_user_path(args.md_out, ROOT / "reports" / "audit" / "closure-debt-crawler.md")

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(build_markdown(payload), encoding="utf-8")

    if args.print_summary:
        s = payload["summary"]
        print(
            f"[closure-debt-crawler] files={s['file_count']} findings={s['finding_count']} "
            f"hard={s['hard_count']} soft={s['soft_count']} advisory={s['advisory_count']}"
        )
        print(f"[closure-debt-crawler] json={json_out}")
        print(f"[closure-debt-crawler] md={md_out}")

    if not args.strict:
        return 0
    return 1 if payload["summary"]["hard_count"] > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
