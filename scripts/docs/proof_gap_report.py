#!/usr/bin/env python3
"""Generate a proof-gap report (sorry/axiom) in Markdown and LaTeX.

The report is intentionally lightweight and uses only local source text:
- finds declarations that are axioms
- finds declarations whose proof body currently contains `sorry`

This helps stage a clean reimplementation pass against the existing codebase.
"""

from __future__ import annotations

import argparse
import datetime as dt
import re
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?"
    r"(theorem|lemma|def|structure|class|instance|axiom)\s+([A-Za-z0-9_'.]+)"
)


@dataclass
class Decl:
    kind: str
    name: str
    line: int
    text: str


@dataclass
class Gap:
    file: Path
    line: int
    gap_kind: str  # "sorry" or "axiom"
    decl: Decl | None


def escape_tex(s: str) -> str:
    table = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "_": r"\_",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "^": r"\^{}",
        "~": r"\~{}",
    }
    return "".join(table.get(c, c) for c in s)


def natlang(decl: Decl | None, gap_kind: str) -> str:
    if decl is None:
        return f"Unscoped `{gap_kind}` placeholder."
    words = decl.name.replace("_", " ").replace(".", " ").strip()
    if decl.kind == "axiom":
        return f"Assumed statement `{decl.name}` ({words})."
    return f"Unfinished proof for `{decl.name}` ({words})."


def collect_gaps(root: Path) -> list[Gap]:
    gaps: list[Gap] = []
    files = sorted(root.rglob("*.lean"))
    for f in files:
        rel = f.relative_to(root.parent)
        lines = f.read_text(encoding="utf-8").splitlines()
        last_decl: Decl | None = None
        for i, line in enumerate(lines, start=1):
            m = DECL_RE.match(line)
            if m:
                kind, name = m.group(1), m.group(2)
                last_decl = Decl(kind=kind, name=name, line=i, text=line.strip())
                if kind == "axiom":
                    gaps.append(Gap(file=rel, line=i, gap_kind="axiom", decl=last_decl))
                continue
            if "sorry" in line and not line.strip().startswith("--"):
                gaps.append(Gap(file=rel, line=i, gap_kind="sorry", decl=last_decl))
    return gaps


def render_md(gaps: list[Gap]) -> str:
    now = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    by_file: dict[Path, list[Gap]] = defaultdict(list)
    for g in gaps:
        by_file[g.file].append(g)

    lines: list[str] = []
    lines.append("# Proof Gap Report")
    lines.append("")
    lines.append(f"Generated: `{now}`")
    lines.append("")
    lines.append(
        "This report lists unfinished or assumed formal statements (`sorry` and `axiom`) "
        "to support clean canonical reimplementation."
    )
    lines.append("")
    lines.append(f"- Total gaps: **{len(gaps)}**")
    lines.append(f"- Files with gaps: **{len(by_file)}**")
    lines.append("")

    for f in sorted(by_file):
        lines.append(f"## `{f}`")
        lines.append("")
        for g in by_file[f]:
            decl = g.decl
            if decl is None:
                lines.append(f"- L{g.line}: `{g.gap_kind}` (no declaration context)")
                continue
            lines.append(
                f"- L{g.line}: `{g.gap_kind}` in `{decl.kind} {decl.name}` "
                f"(decl starts L{decl.line})"
            )
            lines.append(f"  - Natural language: {natlang(decl, g.gap_kind)}")
            lines.append(f"  - Source head: `{decl.text}`")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def render_tex(gaps: list[Gap]) -> str:
    by_file: dict[Path, list[Gap]] = defaultdict(list)
    for g in gaps:
        by_file[g.file].append(g)
    now = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    out: list[str] = []
    out.append(r"\documentclass[11pt]{article}")
    out.append(r"\usepackage[margin=1in]{geometry}")
    out.append(r"\usepackage[T1]{fontenc}")
    out.append(r"\usepackage[utf8]{inputenc}")
    out.append(r"\usepackage{enumitem}")
    out.append(r"\begin{document}")
    out.append(r"\section*{Proof Gap Report}")
    out.append(r"\textbf{Generated:} " + escape_tex(now) + r"\\")
    out.append(
        r"This report lists unfinished or assumed formal statements "
        r"(\texttt{sorry} and \texttt{axiom}) for canonical reimplementation."
    )
    out.append(
        r"\begin{itemize}[leftmargin=2em]"
        + f"\n\\item Total gaps: {len(gaps)}"
        + f"\n\\item Files with gaps: {len(by_file)}"
        + "\n\\end{itemize}"
    )

    for f in sorted(by_file):
        out.append(r"\subsection*{" + escape_tex(str(f)) + "}")
        out.append(r"\begin{itemize}[leftmargin=2em]")
        for g in by_file[f]:
            if g.decl is None:
                out.append(
                    r"\item L"
                    + str(g.line)
                    + r": \texttt{"
                    + escape_tex(g.gap_kind)
                    + r"} (no declaration context)"
                )
                continue
            d = g.decl
            out.append(
                r"\item L"
                + str(g.line)
                + r": \texttt{"
                + escape_tex(g.gap_kind)
                + r"} in \texttt{"
                + escape_tex(f"{d.kind} {d.name}")
                + r"} (decl starts L"
                + str(d.line)
                + r")"
            )
            out.append(r"\begin{itemize}[leftmargin=1.75em]")
            out.append(r"\item " + escape_tex(natlang(d, g.gap_kind)))
            out.append(r"\item Source head: \texttt{" + escape_tex(d.text) + r"}")
            out.append(r"\end{itemize}")
        out.append(r"\end{itemize}")

    out.append(r"\end{document}")
    return "\n".join(out) + "\n"


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--root", default="lean/InfoGeometry", help="Lean module root to scan")
    p.add_argument("--md-out", default="notes/proof_gap_report.md", help="Markdown output path")
    p.add_argument("--tex-out", default="notes/proof_gap_report.tex", help="LaTeX output path")
    args = p.parse_args()

    root = Path(args.root)
    gaps = collect_gaps(root)

    md_out = Path(args.md_out)
    tex_out = Path(args.tex_out)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    tex_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(render_md(gaps), encoding="utf-8")
    tex_out.write_text(render_tex(gaps), encoding="utf-8")

    print(f"wrote {md_out} ({len(gaps)} gaps)")
    print(f"wrote {tex_out}")


if __name__ == "__main__":
    main()

