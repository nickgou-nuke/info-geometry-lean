#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
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
DECL_HEADER_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
    r"(def|abbrev|theorem|lemma|structure|class|instance|axiom|inductive)\s+"
    r"([A-Za-z0-9_'.]+)",
    re.M,
)

BLOCKING_CATEGORIES = {
    "proof-hole",
    "axiom",
    "prop-constant",
    "trivial-theorem",
    "quarantine-manifest",
}

REVIEW_CATEGORIES = {
    "universal-true-field",
    "zero-quadratic-form",
    "scaled-zero-quadratic-form",
    "review-constant-function",
    "review-identity-function",
    "review-identity-linear-map",
    "review-projection-theorem",
}

STATUS_PRECEDENCE = [
    "proof_hole_blocker",
    "explicit_axiom_blocker",
    "vacuous_or_surrogate_surface",
    "quarantine_manifest_inconsistency",
    "review_scaffold_surface",
    "manifested_quarantine_no_current_findings",
    "constructivity_review_surface",
    "content_clean_by_this_audit",
]

DEFAULT_FAIL_STATUSES = {
    "proof_hole_blocker",
    "explicit_axiom_blocker",
    "vacuous_or_surrogate_surface",
    "quarantine_manifest_inconsistency",
}

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
    "blocking_categories": sorted(BLOCKING_CATEGORIES),
    "review_categories": sorted(REVIEW_CATEGORIES),
    "status_precedence": STATUS_PRECEDENCE,
    "default_fail_statuses": sorted(DEFAULT_FAIL_STATUSES),
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
    importer_class_counts: dict[str, int]
    forbidden_importer_count: int
    forbidden_importers: list[str]
    source_excerpts: list[dict[str, Any]]


def rel(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def module_name(path: Path) -> str:
    rpath = rel(path)
    if rpath.startswith("lean/"):
        rpath = rpath[len("lean/") :]
    return Path(rpath).with_suffix("").as_posix().replace("/", ".")


def module_to_path(module: str) -> Path | None:
    path = ROOT / "lean" / Path(module.replace(".", "/")).with_suffix(".lean")
    return path if path.exists() else None


def read_manifest() -> tuple[dict[str, str], bool, str | None]:
    try:
        return audit_constructivity.read_quarantine_manifest(), True, None
    except FileNotFoundError:
        return {}, False, "missing_quarantine_manifest"
    except Exception as exc:
        return {}, False, f"failed_to_read_quarantine_manifest:{exc!r}"


def in_scope(
    path: Path,
    *,
    scope: str = "all",
    file_prefixes: list[str] | None = None,
    module_prefixes: list[str] | None = None,
    exclude_prefixes: list[str] | None = None,
    manifest_modules: set[str] | None = None,
) -> bool:
    rpath = rel(path)
    mod = module_name(path)
    file_prefixes = file_prefixes or []
    module_prefixes = module_prefixes or []
    exclude_prefixes = exclude_prefixes or []
    if scope == "canonical" and not mod.startswith("InfoGeometry.Canonical."):
        return False
    if scope == "stable" and mod.startswith("InfoGeometry.Unstable."):
        return False
    if scope == "stable" and manifest_modules and mod in manifest_modules:
        return False
    if scope == "quarantine":
        is_unstable = mod.startswith("InfoGeometry.Unstable.")
        is_manifested = bool(manifest_modules and mod in manifest_modules)
        if not (is_unstable or is_manifested):
            return False
    if file_prefixes and not any(rpath.startswith(prefix) for prefix in file_prefixes):
        return False
    if module_prefixes and not any(mod.startswith(prefix) for prefix in module_prefixes):
        return False
    if any(rpath.startswith(prefix) or mod.startswith(prefix) for prefix in exclude_prefixes):
        return False
    return True


def all_lean_files(
    *,
    scope: str = "all",
    file_prefixes: list[str] | None = None,
    module_prefixes: list[str] | None = None,
    exclude_prefixes: list[str] | None = None,
    manifest_modules: set[str] | None = None,
) -> list[Path]:
    if scope == "canonical":
        roots = [ROOT / "lean" / "InfoGeometry" / "Canonical"]
    elif scope == "quarantine":
        roots = [ROOT / "lean" / "InfoGeometry" / "Unstable"]
    else:
        # The semantic gate is repo-wide, but its authoritative source set is
        # the tracked/non-ignored Lean tree.  Ignored scratch fixtures (for
        # example `lean/test_axiom.lean`) remain available to forensic audits
        # without poisoning the release gate.
        try:
            result = subprocess.run(
                [
                    "git",
                    "ls-files",
                    "--cached",
                    "--others",
                    "--exclude-standard",
                    "--",
                    "lean/*.lean",
                ],
                cwd=ROOT,
                check=True,
                capture_output=True,
                text=True,
            )
            files = sorted(
                path
                for raw in result.stdout.splitlines()
                if (path := ROOT / raw).is_file()
                and path.is_relative_to(ROOT / "lean")
            )
        except (OSError, subprocess.CalledProcessError):
            roots = [ROOT / "lean"]
            files = sorted(path for root in roots for path in root.rglob("*.lean") if path.is_file())
    if scope in {"canonical", "quarantine"}:
        files = sorted(path for root in roots for path in root.rglob("*.lean") if path.is_file())
    if scope == "quarantine" and manifest_modules:
        for module in sorted(manifest_modules):
            path = module_to_path(module)
            if path is not None and path not in files:
                files.append(path)
        files = sorted(set(files))
    top = ROOT / "lean" / "InfoGeometry.lean"
    if scope == "all" and top.exists():
        files.insert(0, top)
    file_prefixes = file_prefixes or []
    module_prefixes = module_prefixes or []
    exclude_prefixes = exclude_prefixes or []
    out: list[Path] = []
    for path in files:
        if not in_scope(
            path,
            scope=scope,
            file_prefixes=file_prefixes,
            module_prefixes=module_prefixes,
            exclude_prefixes=exclude_prefixes,
            manifest_modules=manifest_modules,
        ):
            continue
        out.append(path)
    return out


# Compatibility name for older callers inside this tool and external reports.
all_infogeometry_files = all_lean_files


def importers_by_module(files: list[Path] | None = None) -> dict[str, list[str]]:
    importers: dict[str, list[str]] = defaultdict(list)
    for path in files or all_infogeometry_files():
        if not path.is_file():
            continue
        text = audit_constructivity.strip_comments(path.read_text(encoding="utf-8"))
        owner = module_name(path)
        for match in IMPORT_RE.finditer(text):
            importers[match.group(1)].append(owner)
    return {key: sorted(values) for key, values in importers.items()}


def importer_class(importer: str) -> str:
    if importer.startswith("InfoGeometry.Unstable."):
        return "allowed_unstable"
    if importer in {"InfoGeometry.All", "InfoGeometry.Canonical.All"}:
        return "umbrella"
    if importer.startswith("InfoGeometry.") and importer.endswith(".All"):
        return "umbrella"
    if importer.startswith("InfoGeometry.Canonical."):
        return "canonical"
    return "other"


def importer_class_counts(importers: list[str]) -> dict[str, int]:
    return dict(sorted(Counter(importer_class(importer) for importer in importers).items()))


def forbidden_importers_for_status(status: str, importers: list[str]) -> list[str]:
    if status == "content_clean_by_this_audit":
        return []
    return [
        importer
        for importer in importers
        if importer_class(importer) in {"umbrella", "canonical", "other"}
    ]


def resolve_finding_location(rpath: str) -> tuple[str, Path | None]:
    path = ROOT / rpath
    if path.exists():
        return module_name(path), path
    if rpath.startswith("InfoGeometry."):
        return rpath, module_to_path(rpath)
    return rpath, None


def finding_in_scope(
    finding: audit_constructivity.Finding,
    *,
    scope: str,
    file_prefixes: list[str] | None,
    module_prefixes: list[str] | None,
    exclude_prefixes: list[str] | None,
    manifest_modules: set[str],
) -> bool:
    mod, path = resolve_finding_location(finding.path)
    if path is not None:
        return in_scope(
            path,
            scope=scope,
            file_prefixes=file_prefixes,
            module_prefixes=module_prefixes,
            exclude_prefixes=exclude_prefixes,
            manifest_modules=manifest_modules,
        )
    file_prefixes = file_prefixes or []
    module_prefixes = module_prefixes or []
    exclude_prefixes = exclude_prefixes or []
    if scope == "canonical" and not mod.startswith("InfoGeometry.Canonical."):
        return False
    if scope == "stable" and mod.startswith("InfoGeometry.Unstable."):
        return False
    if scope == "stable" and mod in manifest_modules:
        return False
    if scope == "quarantine" and not (mod.startswith("InfoGeometry.Unstable.") or mod in manifest_modules):
        return False
    if file_prefixes:
        return False
    if module_prefixes and not any(mod.startswith(prefix) for prefix in module_prefixes):
        return False
    if any(mod.startswith(prefix) for prefix in exclude_prefixes):
        return False
    return True


def source_excerpt(path: Path, line: int, radius: int = 3) -> dict[str, Any]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {"line": line, "available": False, "text": ""}
    start = max(1, line - radius)
    end = min(len(lines), line + radius)
    body = "\n".join(f"{idx}: {lines[idx - 1]}" for idx in range(start, end + 1))
    return {"line": line, "available": True, "start": start, "end": end, "text": body}


def declaration_headers(path: Path, module: str) -> list[dict[str, Any]]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return []
    scan_text = audit_constructivity.strip_comments(text)
    headers: list[dict[str, Any]] = []
    for match in DECL_HEADER_RE.finditer(scan_text):
        raw_name = match.group(2)
        name = raw_name if raw_name.startswith("InfoGeometry.") else f"{module}.{raw_name}"
        headers.append(
            {
                "line": audit_constructivity.line_of(scan_text, match.start()),
                "kind": match.group(1),
                "name": name,
                "raw_name": raw_name,
            }
        )
    headers.sort(key=lambda row: int(row["line"]))
    return headers


def enclosing_decl(headers: list[dict[str, Any]], line: int) -> dict[str, Any] | None:
    best: dict[str, Any] | None = None
    for header in headers:
        if int(header["line"]) <= line:
            best = header
        else:
            break
    return best


def finding_payload(
    finding: audit_constructivity.Finding,
    *,
    headers: list[dict[str, Any]],
) -> dict[str, Any]:
    payload = asdict(finding)
    owner = enclosing_decl(headers, finding.line)
    if owner is not None:
        payload["enclosing_decl"] = owner["name"]
        payload["enclosing_decl_kind"] = owner["kind"]
        payload["enclosing_decl_line"] = owner["line"]
        payload["enclosing_decl_raw_name"] = owner["raw_name"]
    else:
        payload["enclosing_decl"] = None
        payload["enclosing_decl_kind"] = None
        payload["enclosing_decl_line"] = None
        payload["enclosing_decl_raw_name"] = None
    return payload


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
    if "quarantine-manifest" in categories:
        return (
            "quarantine_manifest_inconsistency",
            "fix quarantine manifest or InfoGeometry.Unstable.Quarantine import coverage",
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


def collect_findings(
    files: list[Path],
    *,
    include_review: bool,
    include_manifest_consistency: bool,
) -> list[audit_constructivity.Finding]:
    findings: list[audit_constructivity.Finding] = []
    if include_manifest_consistency:
        try:
            findings.extend(audit_constructivity.scan_manifest_consistency())
        except Exception as exc:
            manifest_path = getattr(audit_constructivity, "MANIFEST", ROOT / "scripts/quality/quarantine_manifest.txt")
            findings.append(
                audit_constructivity.Finding(
                    "quarantine-manifest",
                    rel(Path(manifest_path)),
                    1,
                    f"manifest consistency unavailable: {exc!r}",
                )
            )
    for path in files:
        if not path.is_file():
            continue
        findings.extend(audit_constructivity.scan_file(path, include_review=include_review))
    findings.sort(key=lambda item: (item.path, item.line, item.category))
    return findings


def build_report(
    *,
    scope: str = "all",
    include_review: bool,
    excerpt_radius: int,
    file_prefixes: list[str] | None = None,
    module_prefixes: list[str] | None = None,
    exclude_prefixes: list[str] | None = None,
    include_manifest_consistency: bool = True,
) -> dict[str, Any]:
    manifest, manifest_present, manifest_error = read_manifest()
    files = all_infogeometry_files(
        scope=scope,
        file_prefixes=file_prefixes,
        module_prefixes=module_prefixes,
        exclude_prefixes=exclude_prefixes,
        manifest_modules=set(manifest),
    )
    findings = collect_findings(
        files,
        include_review=include_review,
        include_manifest_consistency=include_manifest_consistency,
    )
    findings = [
        finding
        for finding in findings
        if finding_in_scope(
            finding,
            scope=scope,
            file_prefixes=file_prefixes,
            module_prefixes=module_prefixes,
            exclude_prefixes=exclude_prefixes,
            manifest_modules=set(manifest),
        )
    ]
    by_path: dict[str, list[audit_constructivity.Finding]] = defaultdict(list)
    for finding in findings:
        by_path[finding.path].append(finding)

    importers = importers_by_module(all_infogeometry_files(scope="all"))
    modules: list[ModuleAudit] = []
    category_counts: Counter[str] = Counter()
    status_counts: Counter[str] = Counter()

    for rpath, module_findings in sorted(by_path.items()):
        mod, maybe_path = resolve_finding_location(rpath)
        path = maybe_path
        headers = declaration_headers(path, mod) if path is not None else []
        categories = {finding.category for finding in module_findings}
        status, action = semantic_status(categories)
        category_counts.update(finding.category for finding in module_findings)
        status_counts[status] += 1
        direct_importers = importers.get(mod, [])
        forbidden_importers = forbidden_importers_for_status(status, direct_importers)
        modules.append(
            ModuleAudit(
                module=mod,
                path=rpath,
                semantic_status=status,
                recommended_action=action,
                finding_categories=sorted(categories),
                findings=[finding_payload(finding, headers=headers) for finding in module_findings],
                current_manifest_reason=manifest.get(mod),
                direct_importer_count=len(direct_importers),
                direct_importers=direct_importers[:50],
                importer_class_counts=importer_class_counts(direct_importers),
                forbidden_importer_count=len(forbidden_importers),
                forbidden_importers=forbidden_importers[:50],
                source_excerpts=[
                    source_excerpt(path, finding.line, radius=excerpt_radius)
                    for finding in module_findings[:8]
                    if path is not None
                ],
            )
        )

    for mod, reason in sorted(manifest.items()):
        path = module_to_path(mod)
        if path is None:
            continue
        rpath = rel(path)
        if rpath in by_path:
            continue
        if not in_scope(
            path,
            scope=scope,
            file_prefixes=file_prefixes,
            module_prefixes=module_prefixes,
            exclude_prefixes=exclude_prefixes,
            manifest_modules=set(manifest),
        ):
            continue
        direct_importers = importers.get(mod, [])
        status = "manifested_quarantine_no_current_findings"
        forbidden_importers = forbidden_importers_for_status(status, direct_importers)
        status_counts[status] += 1
        modules.append(
            ModuleAudit(
                module=mod,
                path=rpath,
                semantic_status=status,
                recommended_action="review for possible dequarantine or update manifest reason",
                finding_categories=[],
                findings=[],
                current_manifest_reason=reason,
                direct_importer_count=len(direct_importers),
                direct_importers=direct_importers[:50],
                importer_class_counts=importer_class_counts(direct_importers),
                forbidden_importer_count=len(forbidden_importers),
                forbidden_importers=forbidden_importers[:50],
                source_excerpts=[],
            )
        )

    status_rank = {status: idx for idx, status in enumerate(STATUS_PRECEDENCE)}
    modules.sort(key=lambda module: (status_rank.get(module.semantic_status, 999), module.module))
    blocking_count = sum(1 for finding in findings if finding.category in BLOCKING_CATEGORIES)
    review_count = sum(1 for finding in findings if finding.category in REVIEW_CATEGORIES)
    modules_with_findings = sum(1 for module in modules if module.findings)
    manifest_only_count = sum(
        1 for module in modules if module.semantic_status == "manifested_quarantine_no_current_findings"
    )
    return {
        "schema": "info_geometry.semantic_content_audit.v1",
        "policy": POLICY,
        "inputs": {
            "source": "current checkout Lean source",
            "scope": scope,
            "constructivity_scanner": "tools/quality/audit_constructivity.py::scan_file",
            "include_review_patterns": include_review,
            "include_manifest_consistency": include_manifest_consistency,
            "manifest_present": manifest_present,
            "manifest_error": manifest_error,
            "selected_file_count": len(files),
            "file_prefixes": file_prefixes or [],
            "module_prefixes": module_prefixes or [],
            "exclude_prefixes": exclude_prefixes or [],
            "uses_folder_as_truth_label": False,
            "mutates_quarantine_manifest": False,
            "transitive_impact_available": False,
            "impact_scope": "all InfoGeometry direct importers only",
        },
        "summary": {
            "selected_file_count": len(files),
            "modules_reported": len(modules),
            "modules_with_findings": modules_with_findings,
            "modules_with_current_findings": modules_with_findings,
            "manifested_without_current_findings": manifest_only_count,
            "manifest_only_module_count": manifest_only_count,
            "finding_count": len(findings),
            "blocking_finding_count": blocking_count,
            "review_finding_count": review_count,
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
    lines.append(f"- `selected_file_count`: {summary['selected_file_count']}")
    lines.append(f"- `modules_reported`: {summary['modules_reported']}")
    lines.append(f"- `modules_with_current_findings`: {summary['modules_with_current_findings']}")
    lines.append(f"- `manifest_only_module_count`: {summary['manifest_only_module_count']}")
    lines.append(f"- `finding_count`: {summary['finding_count']}")
    lines.append(f"- `blocking_finding_count`: {summary['blocking_finding_count']}")
    lines.append(f"- `review_finding_count`: {summary['review_finding_count']}")
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
        lines.append(f"- `forbidden_importer_count`: {module['forbidden_importer_count']}")
        if module["importer_class_counts"]:
            lines.append(f"- `importer_class_counts`: `{json.dumps(module['importer_class_counts'], sort_keys=True)}`")
        if module["direct_importers"]:
            lines.append(f"- `direct_importers_sample`: `{', '.join(module['direct_importers'][:10])}`")
        if module["forbidden_importers"]:
            lines.append(f"- `forbidden_importers_sample`: `{', '.join(module['forbidden_importers'][:10])}`")
        lines.append(f"- `finding_categories`: `{', '.join(module['finding_categories'])}`")
        lines.append("")
        for finding in module["findings"][:12]:
            lines.append(
                f"- `{finding['category']}` at `{finding['path']}:{finding['line']}`: {finding['detail']}"
            )
        if module["source_excerpts"]:
            lines.append("")
            seen_categories: set[str] = set()
            for finding, excerpt in zip(module["findings"], module["source_excerpts"]):
                category = finding["category"]
                if category in seen_categories:
                    continue
                seen_categories.add(category)
                lines.append(f"Excerpt for `{category}`:")
                lines.append("")
                lines.append("```lean")
                lines.append(excerpt["text"])
                lines.append("```")
                lines.append("")
        lines.append("")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Semantic content audit over current Lean source; does not classify by folder name."
    )
    parser.add_argument("--json-out", type=Path, default=ROOT / "reports/dag/semantic-content-audit.json")
    parser.add_argument("--md-out", type=Path, default=ROOT / "reports/dag/semantic-content-audit.md")
    parser.add_argument("--scope", choices=("all", "canonical", "stable", "quarantine"), default="all")
    parser.add_argument("--include-review", action="store_true")
    parser.add_argument("--no-manifest-consistency", action="store_true")
    parser.add_argument("--file-prefix", action="append", default=[])
    parser.add_argument("--module-prefix", action="append", default=[])
    parser.add_argument("--exclude-prefix", action="append", default=[])
    parser.add_argument("--excerpt-radius", type=int, default=3)
    parser.add_argument("--gate", action="store_true", help="Fail only on blocking findings.")
    parser.add_argument("--gate-review", action="store_true", help="Fail on blocking and review findings.")
    parser.add_argument("--gate-import-boundary", action="store_true", help="Fail if reported non-clean surfaces have forbidden direct importers.")
    parser.add_argument(
        "--fail-status",
        action="append",
        default=[],
        help="Semantic module status that fails --gate. Defaults to proof holes, axioms, vacuous/surrogate surfaces, and quarantine manifest inconsistencies.",
    )
    args = parser.parse_args()

    include_review = args.include_review or args.gate_review
    report = build_report(
        scope=args.scope,
        include_review=include_review,
        excerpt_radius=args.excerpt_radius,
        file_prefixes=args.file_prefix,
        module_prefixes=args.module_prefix,
        exclude_prefixes=args.exclude_prefix,
        include_manifest_consistency=not args.no_manifest_consistency,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_md(report, args.md_out)
    print(json.dumps(report["summary"], indent=2, sort_keys=True))
    if args.gate_review:
        if report["summary"]["selected_file_count"] == 0:
            return 1
        return 1 if report["summary"]["finding_count"] else 0
    if args.gate_import_boundary:
        if report["summary"]["selected_file_count"] == 0:
            return 1
        if any(int(module.get("forbidden_importer_count") or 0) > 0 for module in report["modules"]):
            return 1
    if args.gate:
        if report["summary"]["selected_file_count"] == 0:
            return 1
        fail_statuses = set(args.fail_status) if args.fail_status else DEFAULT_FAIL_STATUSES
        failures = [
            module
            for module in report["modules"]
            if module.get("semantic_status") in fail_statuses
        ]
        return 1 if failures else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
