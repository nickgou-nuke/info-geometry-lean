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


@dataclass(frozen=True)
class Finding:
    file: str
    line: int
    category: str
    priority: str
    name: str
    note: str


FOCUS_FILES = [
    "lean/InfoGeometry/Krein/HilbertBridge.lean",
    "lean/InfoGeometry/Krein/DoubledAdjoint.lean",
    "lean/InfoGeometry/Krein/Clifford.lean",
    "lean/InfoGeometry/Krein/README.lean",
]

COMMENT_MARKER_RE = re.compile(
    r"(current alias model|identity under aliasing|compatibility alias|compatibility layer)",
    re.IGNORECASE,
)
CARRIER_ALIAS_RE = re.compile(
    r"^abbrev\s+(?P<name>HilbertDoubled|NeutralSpace)\b.*:=\s*DoubledSpace\b"
)


def collect_findings(root: Path) -> list[Finding]:
    findings: list[Finding] = []

    for rel in FOCUS_FILES:
        path = root / rel
        if not path.exists():
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines, start=1):
            stripped = line.strip()
            carrier_match = CARRIER_ALIAS_RE.match(stripped)
            if carrier_match and carrier_match.group("name") == "HilbertDoubled":
                findings.append(
                    Finding(
                        file=rel,
                        line=i,
                        category="carrier_alias",
                        priority="high",
                        name="HilbertDoubled",
                        note="Hilbert carrier is a definitional alias of `DoubledSpace`.",
                    )
                )
            elif carrier_match and carrier_match.group("name") == "NeutralSpace":
                findings.append(
                    Finding(
                        file=rel,
                        line=i,
                        category="carrier_alias",
                        priority="high",
                        name="NeutralSpace",
                        note="Neutral carrier is a definitional alias of `DoubledSpace`.",
                    )
                )
            elif re.match(r"^noncomputable\s+abbrev\s+doubledToHilbert\b", stripped):
                window = "\n".join(lines[i - 1 : min(i + 3, len(lines))])
                if "ContinuousLinearEquiv.refl" in window:
                    findings.append(
                        Finding(
                            file=rel,
                            line=i,
                            category="identity_transport",
                            priority="high",
                            name="doubledToHilbert",
                            note="Hilbert transport is implemented by identity transport under aliasing.",
                        )
                    )
            elif COMMENT_MARKER_RE.search(stripped):
                findings.append(
                    Finding(
                        file=rel,
                        line=i,
                        category="explicit_vacuity_marker",
                        priority="medium",
                        name="comment",
                        note=stripped,
                    )
                )

    return findings


def render_md(findings: list[Finding]) -> str:
    now = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    total = len(findings)
    high = sum(1 for f in findings if f.priority == "high")
    medium = sum(1 for f in findings if f.priority == "medium")
    low = sum(1 for f in findings if f.priority == "low")

    lines: list[str] = []
    lines.append("# Vacuity Index")
    lines.append("")
    lines.append(f"Generated: `{now}`")
    lines.append("")
    lines.append(
        "This report tracks alias-driven and definitional-identity surfaces that can make a bridge "
        "look mathematically deeper than it currently is."
    )
    lines.append("")
    lines.append("## Status")
    lines.append(f"- vacuity gate: **{'FAIL' if high > 0 else 'PASS'}**")
    lines.append(
        "- interpretation: `FAIL` means at least one high-priority alias/identity transport surface "
        "still sits on the active theory path"
    )
    lines.append("")
    lines.append("## Counts")
    lines.append(f"- total tracked findings: **{total}**")
    lines.append(f"- high-priority carrier/identity findings: **{high}**")
    lines.append(f"- medium-priority explicit marker findings: **{medium}**")
    lines.append(f"- low-priority findings: **{low}**")
    lines.append("")
    lines.append("## Aggressive Replacement Queue")
    queue = sorted(findings, key=lambda f: (0 if f.priority == "high" else 1, f.file, f.line))
    if queue:
        for item in queue:
            lines.append(
                f"- `{item.priority}` `{item.category}` `{item.name}` at `{item.file}:{item.line}`"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Findings")
    if findings:
        for item in queue:
            lines.append(
                f"- `{item.file}:{item.line}` `{item.name}` [{item.priority}]"
            )
            lines.append(f"  {item.note}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Policy")
    lines.append(
        "- absence of `sorry` is not enough if a bridge is true only by aliasing or identity transport"
    )
    lines.append(
        "- carrier aliases on bridge boundaries count as real mathematical debt, even when Lean accepts them"
    )
    lines.append(
        "- replacement priority is: carrier aliases -> identity transports -> explicit alias-model compatibility layers"
    )
    return "\n".join(lines) + "\n"


def main() -> int:
    root = repo_root()
    findings = collect_findings(root)
    out_path = root / "VACUITY_INDEX.md"
    out_path.write_text(render_md(findings), encoding="utf-8")
    print(f"[generate-vacuity-index] wrote {out_path}")
    print(f"[generate-vacuity-index] findings={len(findings)} gate={'FAIL' if any(f.priority == 'high' for f in findings) else 'PASS'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
