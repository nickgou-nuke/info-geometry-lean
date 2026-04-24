#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.decl_graph_support import load_decl_graph, resolve_graph_profile, weak_graph_evidence
    from tools.infra.decl_graph_support import load_decl_graph, resolve_graph_profile, weak_graph_evidence
    from tools.infra.reports.common import relpath
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import load_decl_graph, resolve_graph_profile, weak_graph_evidence
    from tools.infra.reports.common import relpath
    from tools.pathing import repo_root


DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|structure|class|instance|axiom)\s+([A-Za-z0-9_'.]+)"
)
PROOF_HOLE_RE = re.compile(r"\b(?:sorry|admit)\b")
CONDITIONAL_SUFFIX_RE = re.compile(r"_of_(?:axioms|hypotheses|assumptions)$")
CONTRACT_NAME_RE = re.compile(r"(?:Axioms|Hypotheses|Assumptions|axioms|hypotheses|assumptions)")
CONTRACT_CONSTRUCTOR_RE = re.compile(
    r"(?:"
    r"^to.*(?:Axioms|Hypotheses|Assumptions)$|"
    r"(?:Axioms|Hypotheses|Assumptions|axioms|hypotheses|assumptions)_of_"
    r")"
)
SURROGATE_MARKER_RE = re.compile(r"\b(?:placeholder|surrogate)\b", re.IGNORECASE)
DEPRECATED_ATTR_RE = re.compile(r"^\s*attribute\s+\[deprecated.*\]\s+([A-Za-z0-9_'.]+)")
NAME_ONLY_RE = re.compile(r"^\s*([A-Za-z0-9_'.]+)\s*$")

CONSTRUCTIVITY_CATEGORY_MAP = {
    "proof-hole": "proof_hole",
    "axiom": "axiom_decl",
    "quarantine-manifest": "quarantine_manifest",
    "prop-constant": "prop_constant",
    "trivial-theorem": "trivial_theorem",
    "universal-true-field": "universal_true_field",
    "zero-quadratic-form": "zero_quadratic_form",
    "scaled-zero-quadratic-form": "scaled_zero_quadratic_form",
}


@dataclass(frozen=True)
class Decl:
    kind: str
    name: str
    line: int
    head: str


@dataclass(frozen=True)
class Finding:
    file: str
    line: int
    decl_kind: str
    name: str
    category: str
    priority: str
    note: str
    structural_role: str = 'graph_unknown'
    graph_load_bearing_score: float = 0.0

def module_to_relpath(root: Path, raw: str) -> str:
    if raw.endswith('.lean') or '/' in raw:
        return raw
    lean_path = root / 'lean' / Path(raw.replace('.', '/')).with_suffix('.lean')
    if lean_path.exists():
        return relpath(lean_path, root)
    direct_path = root / Path(raw.replace('.', '/')).with_suffix('.lean')
    if direct_path.exists():
        return relpath(direct_path, root)
    return raw


def is_comment_line(line: str, in_block_comment: bool = False) -> bool:
    stripped = line.strip()
    return in_block_comment or stripped.startswith("--") or stripped.startswith("/-") or stripped.startswith("-/") or stripped.startswith("*")


def file_bucket(rel: str) -> str:
    if "/Unstable/" in rel or "/Archive/" in rel:
        return "unstable"
    if "/Canonical/" in rel:
        return "canonical"
    return "stable"


def priority_for(category: str, rel: str) -> str:
    bucket = file_bucket(rel)
    if category in {"proof_hole", "axiom_decl", "quarantine_manifest", "prop_constant", "trivial_theorem", "universal_true_field"}:
        return "critical" if bucket != "unstable" else "medium"
    if category in {"zero_quadratic_form", "scaled_zero_quadratic_form", "conditional_theorem"}:
        return "high" if bucket == "canonical" else "medium" if bucket != "unstable" else "low"
    if category == "contract_constructor":
        return "low"
    if category == "contract_decl":
        return "medium" if bucket != "unstable" else "low"
    return "low"


def find_decl_at_or_before(path: Path, line: int) -> Decl | None:
    last_decl: Decl | None = None
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        match = DECL_RE.match(raw)
        if match:
            kind, name = match.group(1), match.group(2)
            last_decl = Decl(kind=kind, name=name, line=idx, head=raw.strip())
        if idx >= line:
            break
    return last_decl


def collect_constructivity_findings(root: Path) -> list[Finding]:
    proc = subprocess.run(
        [sys.executable, "tools/quality/audit_constructivity.py", "--mode", "stable", "--json"],
        cwd=root,
        text=True,
        capture_output=True,
        check=False,
    )
    if not proc.stdout.strip():
        stderr = (proc.stderr or "").strip()
        raise SystemExit(
            "constructivity audit subprocess produced no JSON output"
            + (f": {stderr}" if stderr else "")
        )
    payload = json.loads(proc.stdout or '{"findings": []}')
    findings: list[Finding] = []
    for item in payload.get("findings", []):
        mapped = CONSTRUCTIVITY_CATEGORY_MAP.get(item["category"])
        if mapped is None or mapped in {"proof_hole", "axiom_decl"}:
            continue
        rel = module_to_relpath(root, item["path"])
        path = root / rel
        decl = find_decl_at_or_before(path, int(item["line"])) if path.exists() else None
        findings.append(
            Finding(
                file=rel,
                line=int(item["line"]),
                decl_kind=decl.kind if decl is not None else "unknown",
                name=decl.name if decl is not None else "<unscoped>",
                category=mapped,
                priority=priority_for(mapped, rel),
                note=item["detail"],
            )
        )
    return findings


def dedupe_findings(findings: list[Finding]) -> list[Finding]:
    seen: set[tuple[str, int, str, str]] = set()
    out: list[Finding] = []
    for item in findings:
        key = (item.file, item.line, item.category, item.name)
        if key in seen:
            continue
        seen.add(key)
        out.append(item)
    return out


def collect_findings(root: Path) -> list[Finding]:
    _decl_key_to_full, graph_profiles = load_decl_graph(root)
    findings: list[Finding] = []
    src = root / "lean" / "InfoGeometry"
    deprecated_names: set[str] = set()
    for path in sorted(src.rglob("*.lean")):
        rel = relpath(path, root)
        lines = path.read_text(encoding="utf-8").splitlines()
        last_decl: Decl | None = None
        pending_markers: list[tuple[int, str]] = []
        in_block_comment = False
        pending_deprecated_attr = False
        for i, line in enumerate(lines, start=1):
            dep_match = DEPRECATED_ATTR_RE.match(line)
            if dep_match:
                deprecated_names.add(dep_match.group(1))
                pending_deprecated_attr = False
            elif line.lstrip().startswith("attribute [deprecated"):
                pending_deprecated_attr = True
            elif pending_deprecated_attr:
                name_match = NAME_ONLY_RE.match(line)
                if name_match:
                    deprecated_names.add(name_match.group(1))
                if line.strip():
                    pending_deprecated_attr = False
            line_is_comment = is_comment_line(line, in_block_comment)
            if SURROGATE_MARKER_RE.search(line) and line_is_comment:
                pending_markers.append((i, line.strip()))
            match = DECL_RE.match(line)
            if match:
                kind, name = match.group(1), match.group(2)
                last_decl = Decl(kind=kind, name=name, line=i, head=line.strip())
                if pending_markers:
                    marker_line, marker_text = pending_markers[0]
                    findings.append(
                        Finding(
                            file=rel,
                            line=marker_line,
                            decl_kind=kind,
                            name=name,
                            category="surrogate_marker",
                            priority=priority_for("conditional_theorem", rel),
                            note=f"comment/docstring marks `{name}` as placeholder/surrogate: {marker_text}",
                        )
                    )
                    pending_markers = []
                if kind == "axiom":
                    findings.append(
                        Finding(
                            file=rel,
                            line=i,
                            decl_kind=kind,
                            name=name,
                            category="axiom_decl",
                            priority=priority_for("axiom_decl", rel),
                            note="explicit axiom declaration",
                        )
                    )
                elif kind in {"theorem", "lemma"} and CONDITIONAL_SUFFIX_RE.search(name):
                    profile = resolve_graph_profile(file_rel=rel, leaf_name_hint=name, line=i, graph_profiles=graph_profiles)
                    if weak_graph_evidence(profile):
                        findings.append(
                            Finding(
                                file=rel,
                                line=i,
                                decl_kind=kind,
                                name=name,
                                category="conditional_theorem",
                                priority=priority_for("conditional_theorem", rel),
                                note="conditional theorem surface on weak graph role",
                                structural_role='graph_unknown' if profile is None else profile.structural_role,
                                graph_load_bearing_score=0.0 if profile is None else profile.graph_load_bearing_score,
                            )
                        )
                elif kind in {"def", "abbrev"} and CONTRACT_CONSTRUCTOR_RE.search(name):
                    profile = resolve_graph_profile(file_rel=rel, leaf_name_hint=name, line=i, graph_profiles=graph_profiles)
                    if weak_graph_evidence(profile):
                        findings.append(
                            Finding(
                                file=rel,
                                line=i,
                                decl_kind=kind,
                                name=name,
                                category="contract_constructor",
                                priority=priority_for("contract_constructor", rel),
                                note="constructor from concrete data into a named contract interface on weak graph role",
                                structural_role='graph_unknown' if profile is None else profile.structural_role,
                                graph_load_bearing_score=0.0 if profile is None else profile.graph_load_bearing_score,
                            )
                        )
                elif kind in {"structure", "class", "def", "abbrev"} and CONTRACT_NAME_RE.search(name):
                    profile = resolve_graph_profile(file_rel=rel, leaf_name_hint=name, line=i, graph_profiles=graph_profiles)
                    findings.append(
                        Finding(
                            file=rel,
                            line=i,
                            decl_kind=kind,
                            name=name,
                            category="contract_decl",
                            priority=priority_for("contract_decl", rel),
                            note="named contract/surrogate interface",
                            structural_role='graph_unknown' if profile is None else profile.structural_role,
                            graph_load_bearing_score=0.0 if profile is None else profile.graph_load_bearing_score,
                        )
                    )
                if "/-" in line and "-/" not in line:
                    in_block_comment = True
                continue
            if PROOF_HOLE_RE.search(line) and not line_is_comment:
                decl = last_decl or Decl("unknown", "<unscoped>", i, "")
                findings.append(
                    Finding(
                        file=rel,
                        line=i,
                        decl_kind=decl.kind,
                        name=decl.name,
                        category="proof_hole",
                        priority=priority_for("proof_hole", rel),
                        note="explicit proof hole",
                    )
                )
            if line.strip() and not line_is_comment:
                pending_markers = []
            if "/-" in line and "-/" not in line:
                in_block_comment = True
            elif "-/" in line:
                in_block_comment = False
    return [f for f in findings if f.name not in deprecated_names]


def run_surrogate_gate(root: Path) -> tuple[bool, str]:
    proc = subprocess.run(
        ["bash", "scripts/audit_surrogates.sh"],
        cwd=root,
        text=True,
        capture_output=True,
        check=False,
    )
    out = (proc.stdout + proc.stderr).strip()
    return proc.returncode == 0, out


def summarize_counts(findings: list[Finding]) -> dict[str, Counter[str]]:
    by_category: Counter[str] = Counter()
    by_priority: Counter[str] = Counter()
    by_bucket: Counter[str] = Counter()
    for item in findings:
        by_category[item.category] += 1
        by_priority[item.priority] += 1
        by_bucket[file_bucket(item.file)] += 1
    return {
        "category": by_category,
        "priority": by_priority,
        "bucket": by_bucket,
    }


def top_queue(findings: list[Finding], limit: int = 25) -> list[Finding]:
    order = {"critical": 0, "high": 1, "medium": 2, "low": 3}
    return sorted(
        findings,
        key=lambda f: (
            order.get(f.priority, 9),
            0 if file_bucket(f.file) == "canonical" else 1 if file_bucket(f.file) == "stable" else 2,
            -f.graph_load_bearing_score,
            f.file,
            f.line,
            f.name,
        ),
    )[:limit]


def render_md(findings: list[Finding], gate_ok: bool, gate_output: str) -> str:
    now = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    counts = summarize_counts(findings)
    lines: list[str] = []
    lines.append("# Surrogate Index")
    lines.append("")
    lines.append(f"Generated: `{now}`")
    lines.append("")
    lines.append(
        "This report tracks explicit proof gaps, assumption-bearing theorem surfaces, "
        "and named contract interfaces so surrogate debt can be replaced aggressively with real proofs."
    )
    lines.append("")
    lines.append("## Hard Gate")
    lines.append(f"- `scripts/audit_surrogates.sh`: **{'PASS' if gate_ok else 'FAIL'}**")
    if gate_output:
        tail = gate_output.splitlines()[-6:]
        lines.append("- last gate output:")
        for row in tail:
            lines.append(f"  - `{row}`")
    lines.append("")
    lines.append("## Counts")
    lines.append(f"- total tracked findings: **{len(findings)}**")
    lines.append(f"- proof holes: **{counts['category']['proof_hole']}**")
    lines.append(f"- explicit axiom declarations: **{counts['category']['axiom_decl']}**")
    lines.append(f"- quarantine manifest drift findings: **{counts['category']['quarantine_manifest']}**")
    lines.append(f"- vacuous `trivial` theorems: **{counts['category']['trivial_theorem']}**")
    lines.append(f"- constant `Prop := True/False` surfaces: **{counts['category']['prop_constant']}**")
    lines.append(f"- universal `∀ _, True` fields: **{counts['category']['universal_true_field']}**")
    lines.append(f"- zero quadratic-form surrogates: **{counts['category']['zero_quadratic_form']}**")
    lines.append(f"- scaled-zero quadratic-form surrogates: **{counts['category']['scaled_zero_quadratic_form']}**")
    lines.append(f"- conditional theorem wrappers (`_of_axioms/_of_hypotheses/_of_assumptions`): **{counts['category']['conditional_theorem']}**")
    lines.append(f"- named contract declarations (`Axioms/Hypotheses/Assumptions`): **{counts['category']['contract_decl']}**")
    lines.append(f"- contract constructors (`to...Assumptions`, `..._of_concrete`, `..._of_finiteSupport`): **{counts['category']['contract_constructor']}**")
    lines.append(f"- stable surrogate/placeholder markers: **{counts['category']['surrogate_marker']}**")
    lines.append(f"- canonical findings: **{counts['bucket']['canonical']}**")
    lines.append(f"- other stable findings: **{counts['bucket']['stable']}**")
    lines.append(f"- unstable/archive findings: **{counts['bucket']['unstable']}**")
    lines.append("")
    lines.append("## Aggressive Replacement Queue")
    for item in top_queue(findings):
        lines.append(
            f"- `{item.priority}` `{item.category}` {item.name} "
            f"at `{item.file}:{item.line}`"
        )
    lines.append("")
    for category, title in [
        ("proof_hole", "Explicit Proof Holes"),
        ("axiom_decl", "Explicit Axiom Declarations"),
        ("quarantine_manifest", "Quarantine Manifest Drift"),
        ("trivial_theorem", "Vacuous `trivial` Theorems"),
        ("prop_constant", "Constant `Prop := True/False` Surfaces"),
        ("universal_true_field", "Universal `∀ _, True` Fields"),
        ("zero_quadratic_form", "Zero Quadratic-Form Surrogates"),
        ("scaled_zero_quadratic_form", "Scaled-Zero Quadratic-Form Surrogates"),
        ("conditional_theorem", "Conditional Theorem Surface"),
        ("contract_decl", "Named Contract Declarations"),
        ("contract_constructor", "Contract Constructors"),
        ("surrogate_marker", "Stable Surrogate/Placeholder Markers"),
    ]:
        rows = [f for f in findings if f.category == category]
        lines.append(f"## {title}")
        if not rows:
            lines.append("")
            lines.append("- none")
            lines.append("")
            continue
        lines.append("")
        for item in rows:
            lines.append(
                f"- `{item.file}:{item.line}` `{item.decl_kind} {item.name}` "
                f"[{item.priority}]"
            )
        lines.append("")
    lines.append("## Policy")
    lines.append("- explicit proof holes, explicit axioms, and quarantine-manifest drift are not acceptable end-state theory surface")
    lines.append("- vacuous closed proofs (`trivial`, `Prop := True/False`, universal-True fields) count as surrogate debt even when Lean accepts them")
    lines.append("- zero-valued surrogate constructions count as debt when they stand in for real mathematical content")
    lines.append("- conditional wrappers are tolerated only when the missing obligation is explicit and scheduled for replacement")
    lines.append("- contract declarations must not be confused with completed proofs")
    lines.append("- contract constructors are lower-risk adapters from concrete data into contract surfaces; they should not dominate the replacement queue")
    lines.append("- replacement priority is: canonical proof holes/vacuous proofs -> manifest drift and stable axioms -> canonical conditional wrappers -> open contract interfaces")
    lines.append("")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate a tracked surrogate debt index.")
    p.add_argument(
        "--out",
        default="SURROGATE_INDEX.md",
        help="Output markdown path (default: SURROGATE_INDEX.md)",
    )
    return p.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    findings = dedupe_findings(collect_findings(root) + collect_constructivity_findings(root))
    gate_ok, gate_output = run_surrogate_gate(root)
    out = root / args.out
    out.write_text(render_md(findings, gate_ok, gate_output), encoding="utf-8")
    print(f"[generate-surrogate-index] wrote {out}")
    print(f"[generate-surrogate-index] findings={len(findings)} gate={'PASS' if gate_ok else 'FAIL'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
