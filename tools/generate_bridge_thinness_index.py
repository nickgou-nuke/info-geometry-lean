#!/usr/bin/env python3
from __future__ import annotations

import datetime as dt
import re
import sys
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


DECL_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?(theorem|lemma)\s+([A-Za-z0-9_'.]+)"
)
DECL_BOUNDARY_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|axiom)\s+[A-Za-z0-9_'.]+"
)
TARGET_NAME_RE = re.compile(
    r"(bridge|launchpad|package|equivalence|correspondence)",
    re.IGNORECASE,
)
TARGET_FILE_RE = re.compile(r"(Bridge|Launchpad|Interface)\.lean$")
HELPER_NAME_RE = re.compile(
    r"^(?:fst|snd)_(?:coe|val)$|"
    r".*(?:_apply|_zero|_eq_1|_proof_[0-9_]+)$"
)
ARG_NAME_RE = re.compile(r"\(([A-Za-z_][A-Za-z0-9_']*)\s*:")
ONE_LINE_RFL_RE = re.compile(r"^\s*rfl\s*$")
BY_RFL_RE = re.compile(r"^\s*by\s+rfl\s*$", re.DOTALL)
EXACT_FORWARD_RE = re.compile(
    r"^\s*by\s+exact\s+([A-Za-z0-9_'.]+)",
    re.DOTALL,
)
SIMPA_USING_RE = re.compile(
    r"^\s*by\s+simpa(?:\s*\[[^\]]*\])?\s+using\s+([A-Za-z0-9_'.]+)",
    re.DOTALL,
)
PACKAGE_SHAPE_RE = re.compile(r"\brcases\b.*\bexact\s+⟨", re.DOTALL)


@dataclass(frozen=True)
class Finding:
    file: str
    line: int
    name: str
    category: str
    priority: str
    note: str


def relpath(path: Path, root: Path) -> str:
    return str(path.relative_to(root))


def priority_for(category: str) -> str:
    if category == "definitional_identity":
        return "high"
    if category == "direct_forwarder":
        return "medium"
    if category == "underscore_hypothesis":
        return "medium"
    if category == "package_orchestration":
        return "low"
    return "low"


def is_target(rel: str, name: str) -> bool:
    if HELPER_NAME_RE.match(name):
        return False
    return bool(TARGET_NAME_RE.search(name) or TARGET_FILE_RE.search(Path(rel).name))


def trim_proof(proof: str) -> str:
    kept: list[str] = []
    for line in proof.splitlines():
        stripped = line.strip()
        if stripped.startswith("/--") or stripped.startswith("--"):
            continue
        kept.append(line)
    return "\n".join(kept).strip()


def classify_block(rel: str, start_line: int, name: str, block_lines: list[str]) -> list[Finding]:
    findings: list[Finding] = []
    joined = "\n".join(block_lines)
    head = joined.split(":=", 1)[0]
    proof = trim_proof(joined.split(":=", 1)[1]) if ":=" in joined else ""

    underscore_args = [arg for arg in ARG_NAME_RE.findall(head) if arg.startswith("_")]
    if underscore_args:
        findings.append(
            Finding(
                file=rel,
                line=start_line,
                name=name,
                category="underscore_hypothesis",
                priority=priority_for("underscore_hypothesis"),
                note="declaration head contains underscore-prefixed hypotheses: "
                + ", ".join(f"`{arg}`" for arg in underscore_args),
            )
        )

    if proof:
        compact = "\n".join(line.rstrip() for line in proof.splitlines()).strip()
        if ONE_LINE_RFL_RE.fullmatch(compact) or BY_RFL_RE.fullmatch(compact):
            findings.append(
                Finding(
                    file=rel,
                    line=start_line,
                    name=name,
                    category="definitional_identity",
                    priority=priority_for("definitional_identity"),
                    note="proof body reduces directly to `rfl`",
                )
            )
        else:
            exact_match = EXACT_FORWARD_RE.match(compact)
            simpa_match = SIMPA_USING_RE.match(compact)
            if exact_match:
                findings.append(
                    Finding(
                        file=rel,
                        line=start_line,
                        name=name,
                        category="direct_forwarder",
                        priority=priority_for("direct_forwarder"),
                        note=f"proof body forwards directly via `exact {exact_match.group(1)}`",
                    )
                )
            elif simpa_match:
                findings.append(
                    Finding(
                        file=rel,
                        line=start_line,
                        name=name,
                        category="direct_forwarder",
                        priority=priority_for("direct_forwarder"),
                        note=f"proof body is a `simpa ... using {simpa_match.group(1)}` forwarder",
                    )
                )
            elif PACKAGE_SHAPE_RE.search(compact):
                findings.append(
                    Finding(
                        file=rel,
                        line=start_line,
                        name=name,
                        category="package_orchestration",
                        priority=priority_for("package_orchestration"),
                        note="proof body is primarily package/orchestration (`rcases` + tuple assembly)",
                    )
                )

    return findings


def collect_findings(root: Path) -> list[Finding]:
    findings: list[Finding] = []
    src = root / "lean" / "InfoGeometry"
    for path in sorted(src.rglob("*.lean")):
        rel = relpath(path, root)
        lines = path.read_text(encoding="utf-8").splitlines()
        i = 0
        while i < len(lines):
            line = lines[i]
            match = DECL_START_RE.match(line)
            if not match:
                i += 1
                continue
            kind, name = match.group(1), match.group(2)
            if kind not in {"theorem", "lemma"} or not is_target(rel, name):
                i += 1
                continue
            start = i
            j = i + 1
            while j < len(lines):
                if DECL_BOUNDARY_RE.match(lines[j]):
                    break
                j += 1
            findings.extend(classify_block(rel, start + 1, name, lines[start:j]))
            i = j
    return findings


def render_md(findings: list[Finding]) -> str:
    now = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    total = len(findings)
    by_category: dict[str, int] = {}
    by_priority: dict[str, int] = {}
    for item in findings:
        by_category[item.category] = by_category.get(item.category, 0) + 1
        by_priority[item.priority] = by_priority.get(item.priority, 0) + 1

    order = {"high": 0, "medium": 1, "low": 2}
    queue = sorted(findings, key=lambda f: (order.get(f.priority, 9), f.file, f.line, f.name))

    lines: list[str] = []
    lines.append("# Bridge Thinness Index")
    lines.append("")
    lines.append(f"Generated: `{now}`")
    lines.append("")
    lines.append(
        "This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces "
        "that may be mathematically thinner than their names suggest."
    )
    lines.append("")
    lines.append("## Status")
    lines.append(f"- thin-bridge gate: **{'FAIL' if by_priority.get('high', 0) else 'PASS'}**")
    lines.append(
        "- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity"
    )
    lines.append("")
    lines.append("## Counts")
    lines.append(f"- total tracked findings: **{total}**")
    lines.append(f"- definitional identity findings: **{by_category.get('definitional_identity', 0)}**")
    lines.append(f"- direct forwarder findings: **{by_category.get('direct_forwarder', 0)}**")
    lines.append(f"- underscore-hypothesis findings: **{by_category.get('underscore_hypothesis', 0)}**")
    lines.append(f"- package/orchestration findings: **{by_category.get('package_orchestration', 0)}**")
    lines.append("")
    lines.append("## Queue")
    if queue:
        for item in queue:
            lines.append(f"- `{item.priority}` `{item.category}` `{item.name}` at `{item.file}:{item.line}`")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Findings")
    if queue:
        for item in queue:
            lines.append(f"- `{item.file}:{item.line}` `{item.name}` [{item.priority}]")
            lines.append(f"  {item.note}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Policy")
    lines.append("- this is a heuristic syntax audit, not a proof oracle")
    lines.append("- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics")
    lines.append("- the purpose is to keep bridge names aligned with actual proof depth")
    return "\n".join(lines) + "\n"


def main() -> int:
    root = repo_root()
    findings = collect_findings(root)
    out_path = root / "BRIDGE_THINNESS_INDEX.md"
    out_path.write_text(render_md(findings), encoding="utf-8")
    high = sum(1 for item in findings if item.priority == "high")
    print(f"[generate-bridge-thinness-index] wrote {out_path}")
    print(f"[generate-bridge-thinness-index] findings={len(findings)} gate={'FAIL' if high else 'PASS'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
