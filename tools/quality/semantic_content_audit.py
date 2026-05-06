#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
    from tools.quality import audit_constructivity
else:
    from tools.pathing import repo_root
    from tools.quality import audit_constructivity


ROOT = repo_root()
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.M)

POLICY = {
    "schema": "info_geometry.semantic_content_audit.policy.v1",
    "canonical_definition": (
        "Canonical is a semantic status, not a folder name. A surface is a "
        "canonical candidate only when its exported mathematical claims are "
        "Lean-kernel checked, trust-clean, non-vacuous, rooted in mathlib or "
        "local owner theorems or checked constructive certificates, and free "
        "of dependency on unpromoted quarantine/prognosis material as theorem "
        "authority."
    ),
    "quarantine_definition": (
        "Quarantine is a controlled non-promotable holding status, not a claim "
        "that a file is worthless or permanently noncanonical. It is appropriate "
        "for proof holes, unapproved axioms, True-only/trivial theorem surfaces, "
        "stored-witness or graph-only bridges, diagnostic-only overlays, or "
        "external claims that still lack Lean owner proofs."
    ),
    "to_be_quarantined_definition": (
        "A surface is to be quarantined only when current source evidence shows "
        "a proof hole, unapproved axiom, vacuous/surrogate theorem claim, "
        "graph-only or diagnostic-only support used as proof, or dependency on "
        "unpromoted material, and the surface cannot be immediately rewritten "
        "or split into a proved owner statement plus an explicitly non-authority "
        "hypothesis/prognosis lane."
    ),
    "prognosis_definition": (
        "Prognosis/prima-materia is research guidance or literature material "
        "that may become mathematics later. It is allowed to guide search, but "
        "it is not proof authority until rewritten as a Lean theorem, checked "
        "certificate, or explicit hypothesis-bearing context."
    ),
    "graph_boundary": (
        "DAG, InfoTree, Arango, retrieval, Hodge, Drazin, and spectral evidence "
        "are navigation/provenance diagnostics only. They never promote a claim "
        "without raw Lean descent and a proof/certificate owner."
    ),
}


@dataclass(frozen=True)
class ModuleAudit:
    module: str
    path: str
    semantic_status: str
    recommended_action: str
    finding_categories: list[str]
    findings: list[dict[str, Any]]
    current_manifest_reason: str | None
    direct_importer_count: int
    direct_importers: list[str]
    source_excerpts: list[dict[str, Any]]


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def module_name(path: Path) -> str:
    rpath = rel(path)
    if rpath.startswith("lean/"):
        rpath = rpath[len("lean/") :]
    return Path(rpath).with_suffix("").as_posix().replace("/", ".")


def module_to_path(module: str) -> Path | None:
    path = ROOT / "lean" / Path(module.replace(".", "/")).with_suffix(".lean")
    return path if path.exists() else None


def read_manifest() -> dict[str, str]:
    return audit_constructivity.read_quarantine_manifest()


def all_infogeometry_files() -> list[Path]:
    root = ROOT / "lean" / "InfoGeometry"
    files = sorted(path for path in root.rglob("*.lean") if path.is_file())
    top = ROOT / "lean" / "InfoGeometry.lean"
    if top.exists():
        files.insert(0, top)
    return files


def importers_by_module() -> dict[str, list[str]]:
    importers: dict[str, list[str]] = defaultdict(list)
    for path in all_infogeometry_files():
        text = path.read_text(encoding="utf-8")
        owner = module_name(path)
        for match in IMPORT_RE.finditer(text):
            importers[match.group(1)].append(owner)
    return {key: sorted(values) for key, values in importers.items()}


def source_excerpt(path: Path, line: int, radius: int = 3) -> dict[str, Any]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {"line": line, "available": False, "text": ""}
    start = max(1, line - radius)
    end = min(len(lines), line + radius)
    body = "\n".join(f"{idx}: {lines[idx - 1]}" for idx in range(start, end + 1))
    return {"line": line, "available": True, "start": start, "end": end, "text": body}


def semantic_status(categories: set[str]) -> tuple[str, str]:
    if "proof-hole" in categories:
        return (
            "proof_hole_blocker",
            "split proved content from hole-bearing claims; rewrite or quarantine until no sorry/admit remains",
        )
    if "axiom" in categories:
        return (
            "explicit_axiom_blocker",
            "replace axiom by proof, move to explicit hypothesis context, or quarantine as assumption-bearing surface",
        )
    if categories & {"prop-constant", "trivial-theorem"}:
        return (
            "vacuous_or_surrogate_surface",
            "split real definitions from theorem-looking wrappers; rewrite True/trivial claims as proof-bearing statements or mark expository infrastructure",
        )
    if categories & {
        "universal-true-field",
        "zero-quadratic-form",
        "scaled-zero-quadratic-form",
        "review-constant-function",
        "review-identity-function",
        "review-identity-linear-map",
        "review-projection-theorem",
    }:
        return (
            "review_scaffold_surface",
            "inspect whether the constant/projection surface is intentional infrastructure or a surrogate for missing mathematics",
        )
    if categories:
        return (
            "constructivity_review_surface",
            "inspect exact findings and either prove, split, or explicitly quarantine remaining assumptions",
        )
    return ("content_clean_by_this_audit", "no constructivity findings in this audit")


def collect_findings(*, include_review: bool) -> list[audit_constructivity.Finding]:
    findings: list[audit_constructivity.Finding] = []
    for path in all_infogeometry_files():
        findings.extend(audit_constructivity.scan_file(path, include_review=include_review))
    findings.sort(key=lambda item: (item.path, item.line, item.category))
    return findings


def build_report(*, include_review: bool, excerpt_radius: int) -> dict[str, Any]:
    findings = collect_findings(include_review=include_review)
    by_path: dict[str, list[audit_constructivity.Finding]] = defaultdict(list)
    for finding in findings:
        by_path[finding.path].append(finding)

    manifest = read_manifest()
    importers = importers_by_module()
    modules: list[ModuleAudit] = []
    category_counts: Counter[str] = Counter()
    status_counts: Counter[str] = Counter()

    for rpath, module_findings in sorted(by_path.items()):
        path = ROOT / rpath
        mod = module_name(path)
        categories = {finding.category for finding in module_findings}
        status, action = semantic_status(categories)
        category_counts.update(finding.category for finding in module_findings)
        status_counts[status] += 1
        direct_importers = importers.get(mod, [])
        modules.append(
            ModuleAudit(
                module=mod,
                path=rpath,
                semantic_status=status,
                recommended_action=action,
                finding_categories=sorted(categories),
                findings=[asdict(finding) for finding in module_findings],
                current_manifest_reason=manifest.get(mod),
                direct_importer_count=len(direct_importers),
                direct_importers=direct_importers[:50],
                source_excerpts=[
                    source_excerpt(path, finding.line, radius=excerpt_radius)
                    for finding in module_findings[:8]
                ],
            )
        )

    return {
        "schema": "info_geometry.semantic_content_audit.v1",
        "policy": POLICY,
        "inputs": {
            "source": "current checkout Lean source",
            "constructivity_scanner": "tools/quality/audit_constructivity.py::scan_file",
            "include_review_patterns": include_review,
            "uses_folder_as_truth_label": False,
            "mutates_quarantine_manifest": False,
        },
        "summary": {
            "modules_with_findings": len(modules),
            "finding_count": len(findings),
            "category_counts": dict(sorted(category_counts.items())),
            "semantic_status_counts": dict(sorted(status_counts.items())),
        },
        "modules": [asdict(module) for module in modules],
    }


def write_md(report: dict[str, Any], path: Path) -> None:
    lines: list[str] = []
    lines.append("# Semantic content audit")
    lines.append("")
    lines.append("This report is generated from the current checkout. It does not use folder names as truth labels.")
    lines.append("")
    lines.append("## Definitions")
    for key in (
        "canonical_definition",
        "quarantine_definition",
        "to_be_quarantined_definition",
        "prognosis_definition",
        "graph_boundary",
    ):
        lines.append(f"- `{key}`: {report['policy'][key]}")
    lines.append("")
    lines.append("## Summary")
    summary = report["summary"]
    lines.append(f"- `modules_with_findings`: {summary['modules_with_findings']}")
    lines.append(f"- `finding_count`: {summary['finding_count']}")
    lines.append(f"- `category_counts`: `{json.dumps(summary['category_counts'], sort_keys=True)}`")
    lines.append(f"- `semantic_status_counts`: `{json.dumps(summary['semantic_status_counts'], sort_keys=True)}`")
    lines.append("")
    lines.append("## Module findings")
    for module in report["modules"]:
        lines.append(f"### `{module['module']}`")
        lines.append("")
        lines.append(f"- `path`: `{module['path']}`")
        lines.append(f"- `semantic_status`: `{module['semantic_status']}`")
        lines.append(f"- `recommended_action`: {module['recommended_action']}")
        if module["current_manifest_reason"]:
            lines.append(f"- `current_manifest_reason`: {module['current_manifest_reason']}")
        lines.append(f"- `direct_importer_count`: {module['direct_importer_count']}")
        if module["direct_importers"]:
            lines.append(f"- `direct_importers_sample`: `{', '.join(module['direct_importers'][:10])}`")
        lines.append(f"- `finding_categories`: `{', '.join(module['finding_categories'])}`")
        lines.append("")
        for finding in module["findings"][:12]:
            lines.append(
                f"- `{finding['category']}` at `{finding['path']}:{finding['line']}`: {finding['detail']}"
            )
        if module["source_excerpts"]:
            lines.append("")
            lines.append("```lean")
            lines.append(module["source_excerpts"][0]["text"])
            lines.append("```")
        lines.append("")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Semantic content audit over current Lean source; does not classify by folder name."
    )
    parser.add_argument("--json-out", type=Path, default=ROOT / "reports/dag/semantic-content-audit.json")
    parser.add_argument("--md-out", type=Path, default=ROOT / "reports/dag/semantic-content-audit.md")
    parser.add_argument("--include-review", action="store_true")
    parser.add_argument("--excerpt-radius", type=int, default=3)
    args = parser.parse_args()

    report = build_report(include_review=args.include_review, excerpt_radius=args.excerpt_radius)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_md(report, args.md_out)
    print(json.dumps(report["summary"], indent=2, sort_keys=True))
    return 1 if report["summary"]["finding_count"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
