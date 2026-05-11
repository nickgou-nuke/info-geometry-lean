#!/usr/bin/env python3
"""Scan Lean files for mathless propositions and placeholder proofs.

This tool is heuristic and aimed at review triage, not proof authority.
It flags:
* explicit `axiom` declarations
* `sorry` / `admit` in declarations
* theorems/lemmas/examples whose proof body is purely skeletal (`rfl`, `trivial`,
  `simp`, `simpa`, `aesop`, or equivalent tiny closures)
* propositions proved by literal `True`/`False` constants
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

DECL_START_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|local\s+)?(theorem|lemma|example|def|axiom)\s+([A-Za-z0-9_'.]+)"
)
HAS_AXIOM_RE = re.compile(r"^\s*axiom\s+")
SIMPLE_PROOF_RE = re.compile(
    r"^\s*(rfl|trivial|aesop!?|simpa!?|simp!?)(?:\b|$)",
)
EXACT_TRIVIAL_RE = re.compile(r"^\s*exact\s+(rfl|True\.intro|And.intro|Iff.rfl)\b")
TRIVIAL_TOKEN_RE = re.compile(
    r"\b(sorry|admit|sorryAx|admitAx)\b",
)
@dataclass
class Finding:
    path: Path
    line: int
    kind: str
    name: str
    category: str
    detail: str


def rel_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except Exception:
        return str(path)


def strip_comments(line: str, block_depth: int) -> tuple[str, int]:
    """Strip line/block comments and string literals heuristically."""
    out: list[str] = []
    i = 0
    n = len(line)
    in_string = False
    while i < n:
        ch = line[i]
        nxt = line[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth += 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            break
        if ch == '"':
            in_string = True
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out), block_depth


def strip_comments_text(text: str) -> str:
    depth = 0
    out = []
    for line in text.splitlines():
        clean, depth = strip_comments(line, depth)
        out.append(clean)
    return "\n".join(out)


def looks_trivial_proof(block: str) -> bool:
    """Return True for proofs that are likely skeleton-only."""
    lines = [ln.strip() for ln in block.splitlines() if ln.strip()]
    if not lines:
        return False
    # `:= by` with immediate empty body.
    if "by" in lines[-1] and len(lines) == 1:
        return True

    # Proof block is tiny and composed only of trivial markers.
    filtered: list[str] = []
    for ln in lines:
        if ln.startswith("where"):
            break
        if ln in {"by", "exact", "by simp", "by aesop"}:
            filtered.append(ln)
            continue
        if SIMPLE_PROOF_RE.search(ln) or EXACT_TRIVIAL_RE.search(ln) or TRIVIAL_TOKEN_RE.search(ln):
            filtered.append(ln)
            continue
        if ln.startswith("|"):  # skip tactic branches used in simple scripts
            continue
        if ln in {":="}:
            continue
        filtered.append(ln)

    if not filtered:
        return True
    if len(filtered) > 3:
        return False

    return all(
        SIMPLE_PROOF_RE.search(ln) is not None
        or EXACT_TRIVIAL_RE.search(ln) is not None
        or ln in {"by", "admit", "sorry"}
        for ln in filtered
    )


def is_true_false_body(block: str) -> bool:
    compact = re.sub(r"\s+", " ", block)
    return bool(re.search(r":=\s*(True|False)\b", compact))


def scan_file(path: Path) -> list[Finding]:
    if not path.is_file():
        return []
    text = path.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines()
    findings: list[Finding] = []
    block_depth = 0
    i = 0
    while i < len(lines):
        raw = lines[i]
        clean, block_depth = strip_comments(raw, block_depth)
        m = DECL_START_RE.match(clean)
        if not m:
            i += 1
            continue

        kind = m.group(1)
        name = m.group(2)
        start_line = i + 1

        # Capture declaration block until next top-level declaration or EOF
        decl_lines = [raw]
        j = i + 1
        while j < len(lines):
            nxt_raw = lines[j]
            nxt_clean, _ = strip_comments(nxt_raw, 0)
            indent = len(nxt_raw) - len(nxt_raw.lstrip(" "))
            if DECL_START_RE.match(nxt_clean) and indent == 0 and j != i:
                break
            if HAS_AXIOM_RE.match(clean):
                break
            decl_lines.append(nxt_raw)
            j += 1
        block = "\n".join(decl_lines)
        clean_block = strip_comments_text(block)

        # 1) Explicit axiom declaration
        if kind == "axiom":
            findings.append(
                Finding(
                    path=path,
                    line=start_line,
                    kind=kind,
                    name=name,
                    category="explicit_axiom",
                    detail="Direct `axiom` declaration; not a proof.",
                )
            )
            i = j
            continue

        # 2) sorry/admit/holes in the declaration block
        if TRIVIAL_TOKEN_RE.search(clean_block):
            category = "proof_hole"
            detail = "contains `sorry`/`admit`"
        else:
            # 3) trivial proof body for theorem-like declarations
            if kind in {"theorem", "lemma", "example"}:
                before, sep, after = clean_block.partition(":=")
                if TRIVIAL_TOKEN_RE.search(after):
                    category = "proof_hole"
                    detail = "contains `sorry`/`admit` in proof body"
                elif looks_trivial_proof(after):
                    category = "skeletal_proof"
                    detail = "proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only"
                elif is_true_false_body(clean_block):
                    category = "vacuous_body"
                    detail = "body is a constant True/False witness"
                else:
                    category = ""
                    detail = ""
            else:
                category = ""
                detail = ""

        if category:
            findings.append(
                Finding(
                    path=path,
                    line=start_line,
                    kind=kind,
                    name=name,
                    category=category,
                    detail=detail,
                )
            )

        i = j

    return findings


def run_root(root: Path) -> list[Finding]:
    files = sorted(
        p
        for p in root.rglob("*.lean")
        if ".lake" not in p.parts and ".lake-packages" not in p.parts
    )
    out: list[Finding] = []
    for path in files:
        out.extend(scan_file(path))
    return out


def as_json(findings: list[Finding]) -> str:
    return json.dumps(
        [
            {
                "path": rel_path(f.path),
                "line": f.line,
                "kind": f.kind,
                "name": f.name,
                "category": f.category,
                "detail": f.detail,
            }
            for f in findings
        ],
        indent=2,
    )


def as_text(findings: list[Finding]) -> str:
    if not findings:
        return "No mathless/proof-hole candidates detected."
    out = [f"Found {len(findings)} candidate(s):", ""]
    for f in findings:
        out.append(f"{rel_path(f.path)}:{f.line}: {f.kind} {f.name} [{f.category}]")
        out.append(f"  - {f.detail}")
        out.append("")
    return "\n".join(out)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Find mathless propositions and placeholder-style proofs in Lean code."
        )
    )
    parser.add_argument(
        "--root",
        default="lean/InfoGeometry",
        help="Directory or file to scan (default: lean/InfoGeometry)",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = (ROOT / args.root).resolve() if not Path(args.root).is_absolute() else Path(args.root).resolve()
    findings = run_root(target) if target.is_dir() else scan_file(target)
    if args.format == "json":
        print(as_json(findings))
    else:
        print(as_text(findings))
    return 0 if findings == [] else 1


if __name__ == "__main__":
    raise SystemExit(main())
