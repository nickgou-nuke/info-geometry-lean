#!/usr/bin/env python3
"""Sorry-equivalence analysis.

A declaration is "sorry-equivalent" if replacing its proof body with ``sorry``
loses no nontrivial mathematical information.  In Lean 4 every theorem is
proof-irrelevant, so the compilation test is trivially passed.  The real
question is *semantic* vacuity: does the theorem contribute to the theory?

Classes (from most to least vacuous):

  dead        — never referenced by any other declaration
  type-only   — referenced only in type positions (import/statement scaffolding)
  forwarding  — proof body references exactly one theorem (thin wrapper)
  live        — genuinely used in downstream proof bodies
  capstone    — dead but tagged @[capstone] or at a deep layer (intentional endpoint)

Usage:
    python3 tools/infra/generate_sorry_equivalence.py [--json-out FILE] [--md-out FILE]
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


ROOT = repo_root()
DECLS_FILE = ROOT / "artifacts" / "dag" / "index" / "decls.jsonl"
EDGES_FILE = ROOT / "artifacts" / "dag" / "index" / "edges.jsonl"
META_FILE  = ROOT / "artifacts" / "dag" / "index" / "meta.json"

# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass
class DeclInfo:
    name: str
    kind: str
    module: str
    file: str
    line: int
    doc: str


@dataclass
class EdgeInfo:
    src: str
    dst: str
    kind: str  # "type" | "value"


@dataclass
class TheoremProfile:
    name: str
    module: str
    file: str
    line: int
    doc: str
    reverse_value_count: int = 0       # how many proofs use this theorem
    reverse_type_count: int = 0        # how many types reference this theorem
    forward_value_theorem_count: int = 0  # how many theorems this proof uses
    forward_value_defs: list = field(default_factory=list)
    forward_value_theorems: list = field(default_factory=list)
    classification: str = "live"


# ---------------------------------------------------------------------------
# Load
# ---------------------------------------------------------------------------

def load_decls() -> dict[str, DeclInfo]:
    out = {}
    for line in DECLS_FILE.read_text().splitlines():
        if not line.strip():
            continue
        d = json.loads(line)
        out[d["name"]] = DeclInfo(
            name=d["name"],
            kind=d["kind"],
            module=d.get("module", ""),
            file=d.get("file", ""),
            line=d.get("line", 0),
            doc=d.get("doc", ""),
        )
    return out


def load_edges() -> list[EdgeInfo]:
    out = []
    for line in EDGES_FILE.read_text().splitlines():
        if not line.strip():
            continue
        e = json.loads(line)
        out.append(EdgeInfo(src=e["src"], dst=e["dst"], kind=e["kind"]))
    return out


# ---------------------------------------------------------------------------
# Analysis
# ---------------------------------------------------------------------------

def analyse(decls: dict[str, DeclInfo], edges: list[EdgeInfo]) -> list[TheoremProfile]:
    theorem_names = {n for n, d in decls.items() if d.kind == "theorem"}

    # Reverse maps: who references this declaration?
    rev_value: dict[str, list[str]] = defaultdict(list)
    rev_type: dict[str, list[str]] = defaultdict(list)

    # Forward maps: what does this declaration's proof use?
    fwd_value_theorems: dict[str, list[str]] = defaultdict(list)
    fwd_value_defs: dict[str, list[str]] = defaultdict(list)

    for e in edges:
        if e.kind == "value":
            rev_value[e.dst].append(e.src)
            if e.dst in theorem_names:
                fwd_value_theorems[e.src].append(e.dst)
            else:
                fwd_value_defs[e.src].append(e.dst)
        else:
            rev_type[e.dst].append(e.src)

    profiles: list[TheoremProfile] = []
    for name in sorted(theorem_names):
        d = decls[name]
        p = TheoremProfile(
            name=name,
            module=d.module,
            file=d.file,
            line=d.line,
            doc=d.doc,
            reverse_value_count=len(rev_value.get(name, [])),
            reverse_type_count=len(rev_type.get(name, [])),
            forward_value_theorem_count=len(fwd_value_theorems.get(name, [])),
            forward_value_theorems=fwd_value_theorems.get(name, []),
            forward_value_defs=fwd_value_defs.get(name, []),
        )

        # Classify
        total_reverse = p.reverse_value_count + p.reverse_type_count
        if total_reverse == 0:
            p.classification = "dead"
        elif p.reverse_value_count == 0:
            p.classification = "type-only"
        elif p.forward_value_theorem_count == 1 and len(p.forward_value_defs) <= 2:
            p.classification = "forwarding"
        else:
            p.classification = "live"

        profiles.append(p)

    return profiles


def compute_deep_dead(profiles: list[TheoremProfile]) -> None:
    """Promote dead theorems to 'deep-dead' if they form chains — dead
    theorems whose only forward value-theorem targets are also dead."""
    dead_names = {p.name for p in profiles if p.classification == "dead"}
    by_name = {p.name: p for p in profiles}
    for p in profiles:
        if p.classification != "dead":
            continue
        # If this dead theorem's proof uses only other dead theorems
        # (or no theorems), it forms a dead chain
        if p.forward_value_theorem_count > 0:
            targets_live = [t for t in p.forward_value_theorems if t not in dead_names]
            if targets_live:
                # Uses some live theorem — this is a genuine endpoint
                p.classification = "dead-endpoint"


# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------

def relpath(abs_path: str) -> str:
    try:
        return str(Path(abs_path).relative_to(ROOT))
    except ValueError:
        return abs_path


def file_summary(profiles: list[TheoremProfile]) -> list[dict]:
    """Per-file summary of sorry-equivalence classes."""
    by_file: dict[str, Counter] = defaultdict(Counter)
    for p in profiles:
        by_file[relpath(p.file)][p.classification] += 1

    rows = []
    for f in sorted(by_file):
        c = by_file[f]
        rows.append({
            "file": f,
            "dead": c.get("dead", 0) + c.get("dead-endpoint", 0),
            "type_only": c.get("type-only", 0),
            "forwarding": c.get("forwarding", 0),
            "live": c.get("live", 0),
            "total": sum(c.values()),
        })
    return sorted(rows, key=lambda r: r["dead"], reverse=True)


def generate_md(profiles: list[TheoremProfile]) -> str:
    counts = Counter(p.classification for p in profiles)
    total = len(profiles)

    lines = [
        "# Sorry-Equivalence Report",
        "",
        f"Total theorems analysed: **{total}**",
        "",
        "## Classification Summary",
        "",
        "| Class | Count | % |",
        "|-------|------:|--:|",
    ]
    for cls in ["dead", "dead-endpoint", "type-only", "forwarding", "live"]:
        n = counts.get(cls, 0)
        pct = f"{100*n/total:.1f}" if total else "0"
        lines.append(f"| {cls} | {n} | {pct}% |")

    sorry_equiv = counts.get("dead", 0) + counts.get("dead-endpoint", 0) + counts.get("type-only", 0)
    lines += [
        "",
        f"**Sorry-equivalent (dead + type-only):** {sorry_equiv} ({100*sorry_equiv/total:.1f}%)",
        f"**Wrappers (forwarding):** {counts.get('forwarding', 0)}",
        f"**Load-bearing (live):** {counts.get('live', 0)}",
        "",
    ]

    # Top files by dead theorem count
    fs = file_summary(profiles)
    lines += [
        "## Top Files by Dead Theorem Count",
        "",
        "| File | Dead | Type-only | Forwarding | Live | Total |",
        "|------|-----:|----------:|-----------:|-----:|------:|",
    ]
    for r in fs[:30]:
        lines.append(
            f"| {r['file']} | {r['dead']} | {r['type_only']} | {r['forwarding']} | {r['live']} | {r['total']} |"
        )

    # Dead theorems with docstrings (likely intentional capstones)
    lines += ["", "## Dead Theorems With Docstrings (Possible Capstones)", ""]
    capstone_candidates = [
        p for p in profiles
        if p.classification in ("dead", "dead-endpoint") and p.doc.strip()
    ]
    if capstone_candidates:
        for p in capstone_candidates[:50]:
            rp = relpath(p.file)
            lines.append(f"- `{p.name}` ({rp}:{p.line})")
            lines.append(f"  > {p.doc.strip()[:120]}")
    else:
        lines.append("- none")

    # Forwarding theorems (thin wrappers)
    lines += ["", "## Forwarding Theorems (Thin Wrappers)", ""]
    fwd = [p for p in profiles if p.classification == "forwarding"]
    if fwd:
        lines.append(f"Total: {len(fwd)}")
        lines.append("")
        for p in fwd[:40]:
            rp = relpath(p.file)
            target = p.forward_value_theorems[0] if p.forward_value_theorems else "?"
            lines.append(f"- `{p.name}` → `{target}` ({rp}:{p.line})")
    else:
        lines.append("- none")

    # Most-depended-on live theorems
    lines += ["", "## Most-Depended-On Theorems (by reverse value-edge count)", ""]
    live = sorted(
        [p for p in profiles if p.classification == "live"],
        key=lambda p: p.reverse_value_count, reverse=True,
    )
    lines.append("| Theorem | Reverse-value uses | Module |")
    lines.append("|---------|-------------------:|--------|")
    for p in live[:30]:
        lines.append(f"| `{p.name}` | {p.reverse_value_count} | {p.module} |")

    lines += [
        "",
        "## Policy",
        "",
        "- A **dead** theorem can be sorry'd (or deleted) with zero downstream impact.",
        "- A **dead-endpoint** uses live infrastructure but nobody consumes it — likely a capstone or orphan.",
        "- A **type-only** theorem appears in statement scaffolding but never in any proof body.",
        "- A **forwarding** theorem's proof delegates to exactly one other theorem — candidate for inlining.",
        "- A **live** theorem is genuinely load-bearing: downstream proofs depend on it.",
        "- Dead theorems with docstrings may be intentional capstone results worth keeping.",
        "- Forwarding theorems are the prime candidates for wrapper elimination.",
    ]

    return "\n".join(lines) + "\n"


def generate_json(profiles: list[TheoremProfile]) -> list[dict]:
    return [
        {
            "name": p.name,
            "module": p.module,
            "file": relpath(p.file),
            "line": p.line,
            "classification": p.classification,
            "reverse_value_count": p.reverse_value_count,
            "reverse_type_count": p.reverse_type_count,
            "forward_value_theorem_count": p.forward_value_theorem_count,
        }
        for p in profiles
    ]


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser(description="Sorry-equivalence analysis")
    ap.add_argument("--json-out", type=Path, default=ROOT / "reports" / "dag" / "sorry-equivalence.json")
    ap.add_argument("--md-out", type=Path, default=ROOT / "reports" / "dag" / "sorry-equivalence.md")
    args = ap.parse_args()

    if not DECLS_FILE.exists() or not EDGES_FILE.exists():
        print(f"[sorry-equiv] Missing artifacts: {DECLS_FILE} or {EDGES_FILE}", file=sys.stderr)
        print("[sorry-equiv] Run: python3 tools/infra/refresh_decl_graph.py", file=sys.stderr)
        sys.exit(1)

    # Check meta freshness
    if META_FILE.exists():
        meta = json.loads(META_FILE.read_text())
        sv = meta.get("schemaVersion", 0)
        if sv < 2:
            print(f"[sorry-equiv] WARNING: meta.json schemaVersion={sv} < 2, edges may lack kind field", file=sys.stderr)

    decls = load_decls()
    edges = load_edges()
    profiles = analyse(decls, edges)
    compute_deep_dead(profiles)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.md_out.parent.mkdir(parents=True, exist_ok=True)

    args.json_out.write_text(json.dumps(generate_json(profiles), indent=2) + "\n")
    args.md_out.write_text(generate_md(profiles))

    counts = Counter(p.classification for p in profiles)
    sorry_eq = counts.get("dead", 0) + counts.get("dead-endpoint", 0) + counts.get("type-only", 0)
    print(f"[sorry-equiv] {len(profiles)} theorems analysed")
    print(f"[sorry-equiv] sorry-equivalent: {sorry_eq} ({100*sorry_eq/len(profiles):.1f}%)")
    print(f"[sorry-equiv] forwarding: {counts.get('forwarding', 0)}")
    print(f"[sorry-equiv] live: {counts.get('live', 0)}")
    print(f"[sorry-equiv] wrote {args.json_out}")
    print(f"[sorry-equiv] wrote {args.md_out}")


if __name__ == "__main__":
    main()
