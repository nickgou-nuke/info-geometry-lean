#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.quality.common import (
        APPROVED_AXIOMS_PATH,
        AUDIT_AXIOMS_REPORT_PATH,
        QUARANTINE_MANIFEST_PATH,
        line_of,
        module_to_path,
        path_to_module,
        rel,
        strip_lean_comments,
    )
    from tools.pathing import repo_root
else:
    from tools.quality.common import (
        APPROVED_AXIOMS_PATH,
        AUDIT_AXIOMS_REPORT_PATH,
        QUARANTINE_MANIFEST_PATH,
        line_of,
        module_to_path,
        path_to_module,
        rel,
        strip_lean_comments,
    )
    from tools.pathing import repo_root

ROOT = repo_root()
MANIFEST = QUARANTINE_MANIFEST_PATH
APPROVED_AXIOMS = APPROVED_AXIOMS_PATH

PROJECT_PATTERNS_FULL = (
    "lean/**/*.lean",
    "scripts/**/*.lean",
    "test*.lean",
    "lakefile.lean",
)

PROJECT_PATTERNS_STABLE = (
    "lean/InfoGeometry*.lean",
    "lean/InfoGeometry/**/*.lean",
    "lean/SelfReference*.lean",
    "lean/SelfReference/**/*.lean",
)

SKIP_BASENAMES = {"auto_blueprints.lean", "generated_blueprints.lean"}

DECL_RE = re.compile(
    r"(?m)^\s*(?:@[^\n]*\n\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>def|abbrev|theorem|lemma|class|structure|inductive)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)\b"
)

ABBREV_RE = re.compile(
    r"(?m)^\s*(?:@[^\n]*\n\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"abbrev\s+(?P<name>[A-Za-z0-9_'.]+)\b"
)

DIRECT_ALIAS_ABBREV_RE = re.compile(
    r"(?m)^\s*(?:@[^\n]*\n\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"abbrev\s+(?P<name>[A-Za-z0-9_'.]+)\b"
    r"[^:=\n]*:=\s*(?P<rhs>[A-Za-z0-9_'.]+)\b"
)

STRUCTURE_HEADER_RE = re.compile(
    r"^\s*(?:@[^\n]*\n\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>structure|class)\s+(?P<name>[A-Za-z0-9_'.]+)\b"
)

FIELD_RE = re.compile(
    r"^(?P<indent>\s+)(?:(?P<bracket>\[[^\]]+\])|(?P<name>[A-Za-z0-9_']+))\s*:\s*(?P<ty>.+)$"
)

SIMPLE_TRUE_FALSE_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma)\s+"
    r"(?P<name>[A-Za-z0-9_']+)\b[\s\S]{0,500}?:=\s*(?:by\s*)?(?P<value>True|False)\b"
)

TRIVIAL_THEOREM_RE = re.compile(
    r"(?ms)^\s*(?:theorem|lemma)\s+(?P<name>[A-Za-z0-9_']+)\b"
    r"[\s\S]{0,500}?:=\s*(?:by\s*)?(?:exact\s+)?trivial\b"
)

ZERO_LITERAL_DEF_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+(?P<name>[A-Za-z0-9_']+)\b"
    r"[\s\S]{0,500}?:=\s*(?:0|1)\b"
)

CONSTANT_FUNCTION_RE = re.compile(
    r"(?m)^\s*(?P<field>[A-Za-z0-9_']+)\s*:=\s*fun\s+"
    r"(?:_[^=]*|[A-Za-z0-9_']+(?:\s+[A-Za-z0-9_']+)*)\s*=>\s*(?P<value>0|1|True|False)\b"
)

IDENTITY_FUNCTION_RE = re.compile(
    r"(?m)^\s*(?P<field>[A-Za-z0-9_']+)\s*:=\s*fun\s+(?P<arg>[A-Za-z0-9_']+)\s*=>\s*(?P=arg)\b"
)

IDENTITY_MAP_RE = re.compile(
    r"(?m)^\s*(?P<field>[A-Za-z0-9_']+)\s*:=\s*fun\s+_\s*=>\s*(?P<kind>LinearMap|ContinuousLinearMap)\.id\b"
)

BANNED_PATTERNS: dict[str, re.Pattern[str]] = {
    "proof_hole": re.compile(r"\b(?:sorry|admit)\b"),
    "axiom_decl": re.compile(r"(?m)^\s*axiom\b"),
    "opaque_decl": re.compile(r"(?m)^\s*opaque\b"),
    "unsafe_decl": re.compile(r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*unsafe\s+(?:def|theorem|lemma|abbrev)\b"),
    "partial_decl": re.compile(r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*partial\s+def\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "extern_decl": re.compile(r"(?m)^\s*extern\b"),
}

PROOF_LIKE_TOKENS = ("=", "↔", "≤", "≥", "≠", "∈", "∉", "⊆", "Disjoint", "Subsingleton")
RAWISH_NAME_TOKENS = ("Raw", "Witness", "Candidate", "Datum", "Core", "Scaffold", "Bundle")
DYNAMIC_NAME_TOKENS = (
    "flow",
    "transport",
    "update",
    "cocycle",
    "trajectory",
    "evolution",
    "dynamics",
    "connection",
    "metric",
    "volume",
    "state",
    "operator",
)


@dataclass(frozen=True)
class InterfaceInfo:
    path: str
    line: int
    kind: str
    name: str
    total_fields: int
    proof_fields: int
    data_fields: int
    context_fields: int


def declaration_modules(texts: dict[str, str]) -> list[str]:
    modules: set[str] = set()
    for path, text in texts.items():
        if DECL_RE.search(strip_lean_comments(text)) is None:
            continue
        module = path_to_module(path)
        if module is None:
            continue
        if module.startswith("InfoGeometry") or module.startswith("SelfReference"):
            modules.add(module)
    return sorted(modules)


def read_quarantine_manifest() -> dict[str, str]:
    manifest: dict[str, str] = {}
    if not MANIFEST.exists():
      return manifest
    for raw_line in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        module, _, reason = raw_line.partition("|")
        manifest[module.strip()] = reason.strip()
    return manifest


def quarantined_paths() -> set[str]:
    mods: set[str] = set()
    for module in read_quarantine_manifest():
        path = module_to_path(module)
        if path is not None:
            mods.add(rel(path))
    mods.add("lean/InfoGeometry/Unstable/Quarantine.lean")
    unstable_root = ROOT / "lean/InfoGeometry/Unstable"
    if unstable_root.exists():
        for path in unstable_root.glob("*.lean"):
            mods.add(rel(path))
    return mods


def iter_files(mode: str) -> list[Path]:
    patterns = PROJECT_PATTERNS_STABLE if mode == "stable" else PROJECT_PATTERNS_FULL
    files = sorted(
        {
            path
            for pattern in patterns
            for path in ROOT.glob(pattern)
            if path.is_file()
            and ".lake/" not in path.as_posix()
            and path.name not in SKIP_BASENAMES
        }
    )
    if mode != "stable":
        return files
    quarantined = quarantined_paths()
    stable_files: list[Path] = []
    for path in files:
        rpath = rel(path)
        if rpath in quarantined:
            continue
        if rpath.startswith("lean/InfoGeometry/Unstable/"):
            continue
        stable_files.append(path)
    return stable_files


def read_files(paths: list[Path]) -> dict[str, str]:
    return {rel(path): path.read_text(encoding="utf-8") for path in paths}


def make_finding(**kwargs: Any) -> dict[str, Any]:
    return dict(kwargs)


def scan_banned_constructs(texts: dict[str, str]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path, text in texts.items():
        for category, pattern in BANNED_PATTERNS.items():
            for match in pattern.finditer(text):
                findings.append(
                    make_finding(
                        category=category,
                        path=path,
                        line=line_of(text, match.start()),
                        snippet=match.group(0).strip(),
                    )
                )
    return findings


def scan_constant_collapse(texts: dict[str, str]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path, text in texts.items():
        for match in SIMPLE_TRUE_FALSE_RE.finditer(text):
            findings.append(
                make_finding(
                    category="truth_constant",
                    path=path,
                    line=line_of(text, match.start()),
                    name=match.group("name"),
                    detail=f"declaration reduces to {match.group('value')}",
                )
            )
        for match in TRIVIAL_THEOREM_RE.finditer(text):
            findings.append(
                make_finding(
                    category="trivial_theorem",
                    path=path,
                    line=line_of(text, match.start()),
                    name=match.group("name"),
                    detail="theorem/lemma proven by trivial",
                )
            )
        for match in ZERO_LITERAL_DEF_RE.finditer(text):
            name = match.group("name")
            if any(token in name.lower() for token in DYNAMIC_NAME_TOKENS):
                findings.append(
                    make_finding(
                        category="dynamic_literal",
                        path=path,
                        line=line_of(text, match.start()),
                        name=name,
                        detail="dynamic-looking declaration reduces to a literal",
                    )
                )
        for match in CONSTANT_FUNCTION_RE.finditer(text):
            findings.append(
                make_finding(
                    category="constant_function",
                    path=path,
                    line=line_of(text, match.start()),
                    name=match.group("field"),
                    detail=f"field/function returns constant {match.group('value')}",
                )
            )
        for match in IDENTITY_FUNCTION_RE.finditer(text):
            findings.append(
                make_finding(
                    category="identity_function",
                    path=path,
                    line=line_of(text, match.start()),
                    name=match.group("field"),
                    detail="field/function is syntactic identity",
                )
            )
        for match in IDENTITY_MAP_RE.finditer(text):
            findings.append(
                make_finding(
                    category="identity_map",
                    path=path,
                    line=line_of(text, match.start()),
                    name=match.group("field"),
                    detail=f"field/function is constant {match.group('kind')}.id",
                )
            )
    return findings


def is_proof_like_type(ty: str) -> bool:
    stripped = ty.strip()
    if stripped.startswith("Prop") or stripped.startswith("∀"):
        return True
    return any(token in stripped for token in PROOF_LIKE_TOKENS)


def parse_interfaces(texts: dict[str, str]) -> list[InterfaceInfo]:
    interfaces: list[InterfaceInfo] = []
    for path, text in texts.items():
        lines = text.splitlines()
        i = 0
        while i < len(lines):
            header = STRUCTURE_HEADER_RE.match(lines[i])
            if header is None:
                i += 1
                continue
            kind = header.group("kind")
            name = header.group("name")
            header_indent = len(lines[i]) - len(lines[i].lstrip(" "))
            total_fields = 0
            proof_fields = 0
            data_fields = 0
            context_fields = 0
            j = i + 1
            while j < len(lines):
                line = lines[j]
                stripped = line.strip()
                indent = len(line) - len(line.lstrip(" "))
                if stripped and indent <= header_indent and not stripped.startswith("--") and not stripped.startswith("/-"):
                    break
                field = FIELD_RE.match(line)
                if field and indent > header_indent:
                    total_fields += 1
                    ty = field.group("ty")
                    if field.group("bracket"):
                        context_fields += 1
                    elif is_proof_like_type(ty):
                        proof_fields += 1
                    else:
                        data_fields += 1
                j += 1
            interfaces.append(
                InterfaceInfo(
                    path=path,
                    line=i + 1,
                    kind=kind,
                    name=name,
                    total_fields=total_fields,
                    proof_fields=proof_fields,
                    data_fields=data_fields,
                    context_fields=context_fields,
                )
            )
            i = j
    return interfaces


def scan_raw_witness_bundles(interfaces: list[InterfaceInfo]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for info in interfaces:
        rawish_name = any(token in info.name for token in RAWISH_NAME_TOKENS)
        witness_heavy = info.proof_fields >= 2 and info.proof_fields >= info.data_fields and info.data_fields <= 2
        if rawish_name or witness_heavy:
            findings.append(
                make_finding(
                    path=info.path,
                    line=info.line,
                    kind=info.kind,
                    name=info.name,
                    total_fields=info.total_fields,
                    proof_fields=info.proof_fields,
                    data_fields=info.data_fields,
                    context_fields=info.context_fields,
                )
            )
    return findings


def scan_ghost_classes(interfaces: list[InterfaceInfo]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for info in interfaces:
        if info.kind == "class" and info.data_fields == 0 and info.proof_fields >= 2:
            findings.append(
                make_finding(
                    path=info.path,
                    line=info.line,
                    kind=info.kind,
                    name=info.name,
                    total_fields=info.total_fields,
                    proof_fields=info.proof_fields,
                    context_fields=info.context_fields,
                )
            )
    return findings


def count_name_occurrences(texts: dict[str, str], names: list[str]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for name in names:
        pattern = re.compile(rf"\b{re.escape(name)}\b")
        counts[name] = sum(len(pattern.findall(text)) for text in texts.values())
    return counts


def scan_uninstantiated_interfaces(
    texts: dict[str, str], interfaces: list[InterfaceInfo]
) -> list[dict[str, Any]]:
    candidates = [info for info in interfaces if info.kind in {"class", "structure"}]
    counts = count_name_occurrences(texts, [info.name for info in candidates])
    findings: list[dict[str, Any]] = []
    for info in candidates:
        occurrences = counts.get(info.name, 0)
        if occurrences <= 2:
            findings.append(
                make_finding(
                    path=info.path,
                    line=info.line,
                    kind=info.kind,
                    name=info.name,
                    occurrences=occurrences,
                    detail="interface has little or no downstream mention",
                )
            )
    return findings


def scan_alias_density(texts: dict[str, str]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path, text in texts.items():
        decl_count = len(list(DECL_RE.finditer(text)))
        abbrev_count = len(list(ABBREV_RE.finditer(text)))
        direct_alias_count = len(list(DIRECT_ALIAS_ABBREV_RE.finditer(text)))
        if decl_count == 0:
            continue
        ratio = abbrev_count / decl_count
        direct_ratio = direct_alias_count / decl_count
        if (abbrev_count >= 5 and ratio >= 0.20) or (direct_alias_count >= 3 and direct_ratio >= 0.15):
            findings.append(
                make_finding(
                    path=path,
                    declarations=decl_count,
                    abbrevs=abbrev_count,
                    direct_alias_abbrevs=direct_alias_count,
                    abbrev_ratio=round(ratio, 3),
                    direct_alias_ratio=round(direct_ratio, 3),
                )
            )
    return sorted(findings, key=lambda item: (-item["abbrev_ratio"], -item["abbrevs"], item["path"]))


def load_approved_axioms(path: Path) -> set[str]:
    if not path.exists():
        return set()
    approved: set[str] = set()
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line and not line.startswith("#"):
            approved.add(line)
    return approved


def run_axiom_report(
    included_paths: set[str],
    module_names: list[str],
    approved_axioms: set[str],
) -> dict[str, Any]:
    # If auditing the whole codebase, let the Lean script default to all modules rather than passing hundreds of arguments.
    args = module_names if len(module_names) < 50 else []
    cmd = ["lake", "env", "lean", "--run", str(AUDIT_AXIOMS_REPORT_PATH.relative_to(ROOT))] + args
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    transitive_axioms: list[dict[str, Any]] = []
    non_approved: list[dict[str, Any]] = []
    unique_axioms: Counter[str] = Counter()
    for raw_line in proc.stdout.splitlines():
        parts = raw_line.split("\t")
        if len(parts) != 4:
            continue
        module, kind, name, axioms_field = parts
        path = module_to_path(module)
        if path is None:
            continue
        rpath = rel(path)
        if rpath not in included_paths:
            continue
        axioms = [item for item in axioms_field.split(";") if item]
        if not axioms:
            continue
        unique_axioms.update(axioms)
        entry = make_finding(
            module=module,
            path=rpath,
            kind=kind,
            name=name,
            axioms=axioms,
        )
        transitive_axioms.append(entry)
        disallowed = [ax for ax in axioms if ax not in approved_axioms]
        if disallowed:
            non_approved.append(
                make_finding(
                    module=module,
                    path=rpath,
                    kind=kind,
                    name=name,
                    axioms=axioms,
                    non_approved_axioms=disallowed,
                )
            )
    return {
        "transitive_axioms": transitive_axioms,
        "non_approved_axioms": non_approved,
        "axiom_usage_summary": dict(sorted(unique_axioms.items())),
    }


def top_counts(section: list[dict[str, Any]], key: str, n: int = 10) -> dict[str, int]:
    counter = Counter(item.get(key, "<unknown>") for item in section)
    return dict(counter.most_common(n))


def summary_counts(report: dict[str, Any]) -> dict[str, int]:
    return {
        key: len(value)
        for key, value in report["sections"].items()
        if isinstance(value, list)
    }


def load_baseline(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def compare_to_baseline(current: dict[str, Any], baseline: dict[str, Any]) -> list[dict[str, Any]]:
    regressions: list[dict[str, Any]] = []
    current_counts = current["summary"]["section_counts"]
    baseline_counts = baseline.get("summary", {}).get("section_counts", {})
    for section, count in current_counts.items():
        base = int(baseline_counts.get(section, 0))
        if count > base:
            regressions.append(
                {
                    "section": section,
                    "baseline": base,
                    "current": count,
                    "delta": count - base,
                }
            )
    return regressions


def print_human_report(report: dict[str, Any]) -> None:
    print(f"Semantic audit ({report['mode']})")
    print(f"Files scanned: {report['files_scanned']}")
    for section, count in report["summary"]["section_counts"].items():
        print(f"- {section}: {count}")
    if report["sections"]["non_approved_axioms"]:
        print("- top non-approved axiom users:")
        for item in report["sections"]["non_approved_axioms"][:10]:
            print(f"  {item['name']} [{', '.join(item['non_approved_axioms'])}]")
    if report["sections"]["banned_constructs"]:
        print("- top banned constructs:")
        for kind, count in top_counts(report["sections"]["banned_constructs"], "category").items():
            print(f"  {kind}: {count}")
    if report["sections"]["raw_witness_bundles"]:
        print("- raw witness bundle examples:")
        for item in report["sections"]["raw_witness_bundles"][:10]:
            print(
                f"  {item['name']} ({item['proof_fields']} proof / {item['data_fields']} data / "
                f"{item['context_fields']} context fields)"
            )


def build_report(mode: str, approved_axioms_path: Path) -> dict[str, Any]:
    paths = iter_files(mode)
    texts = read_files(paths)
    included_paths = set(texts.keys())
    module_names = declaration_modules(texts)
    interfaces = parse_interfaces(texts)
    approved_axioms = load_approved_axioms(approved_axioms_path)
    axiom_report = run_axiom_report(included_paths, module_names, approved_axioms)
    sections: dict[str, Any] = {
        "banned_constructs": scan_banned_constructs(texts),
        "transitive_axioms": axiom_report["transitive_axioms"],
        "non_approved_axioms": axiom_report["non_approved_axioms"],
        "raw_witness_bundles": scan_raw_witness_bundles(interfaces),
        "ghost_classes": scan_ghost_classes(interfaces),
        "constant_collapse_definitions": scan_constant_collapse(texts),
        "alias_density": scan_alias_density(texts),
        "uninstantiated_interfaces": scan_uninstantiated_interfaces(texts, interfaces),
    }
    report = {
        "mode": mode,
        "files_scanned": len(paths),
        "approved_axioms": sorted(approved_axioms),
        "sections": sections,
        "summary": {
            "section_counts": {},
            "top_banned_constructs": top_counts(sections["banned_constructs"], "category"),
            "top_axioms": axiom_report["axiom_usage_summary"],
        },
    }
    report["summary"]["section_counts"] = summary_counts(report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Emit a machine-readable semantic audit report for Lean sources."
    )
    parser.add_argument("--mode", choices=("stable", "full", "review"), default="stable")
    parser.add_argument("--json-out", type=Path, default=None)
    parser.add_argument("--baseline-in", type=Path, default=None)
    parser.add_argument("--approved-axioms", type=Path, default=APPROVED_AXIOMS)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    report = build_report(args.mode, args.approved_axioms)
    regressions: list[dict[str, Any]] = []
    if args.baseline_in is not None and args.baseline_in.exists():
        baseline = load_baseline(args.baseline_in)
        regressions = compare_to_baseline(report, baseline)
        report["baseline_regressions"] = regressions

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")

    if not args.quiet:
        print_human_report(report)
        if regressions:
            print("- baseline regressions:")
            for item in regressions:
                print(
                    f"  {item['section']}: baseline {item['baseline']}, "
                    f"current {item['current']} (+{item['delta']})"
                )

    if regressions:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
