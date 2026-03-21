#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "scripts/quality/quarantine_manifest.txt"

PROJECT_PATTERNS_FULL = (
    "lean/**/*.lean",
    "scripts/**/*.lean",
    "test*.lean",
    "lakefile.lean",
)

PROJECT_PATTERNS_STABLE = (
    "lean/InfoGeometry*.lean",
    "lean/InfoGeometry/**/*.lean",
)

PROOF_HOLE_RE = re.compile(r"\b(?:sorry|admit)\b")
AXIOM_RE = re.compile(r"^\s*axiom\b", re.M)
TRUE_PROP_RE = re.compile(
    r"(?ms)^\s*(?:def|abbrev|theorem|lemma)\s+[A-Za-z0-9_']+\b"
    r"[\s\S]{0,400}?:\s*Prop\s*:=\s*(?:--[^\n]*\n\s*)*True\b"
)
FALSE_PROP_RE = re.compile(
    r"(?ms)^\s*(?:def|abbrev|theorem|lemma)\s+[A-Za-z0-9_']+\b"
    r"[\s\S]{0,400}?:\s*Prop\s*:=\s*(?:--[^\n]*\n\s*)*False\b"
)
TRIVIAL_THEOREM_RE = re.compile(
    r"(?ms)^\s*(?:theorem|lemma)\s+[A-Za-z0-9_']+\b"
    r"[\s\S]{0,500}?:=\s*(?:by\s*)?(?:exact\s+)?trivial\b"
)
UNIVERSAL_TRUE_FIELD_RE = re.compile(
    r"(?m)^\s*[A-Za-z0-9_']+\s*:\s*∀ .*?,\s*True\s*$"
)
ZERO_QUADRATIC_FORM_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+[A-Za-z0-9_']*QuadraticForm[A-Za-z0-9_']*\b"
    r"[\s\S]{0,400}?:=\s*(?:--[^\n]*\n\s*)*0\b"
)
SCALED_ZERO_QUADRATIC_FORM_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+[A-Za-z0-9_']*QuadraticForm[A-Za-z0-9_']*\b"
    r"[\s\S]{0,500}?:=\s*(?:--[^\n]*\n\s*)*[\s\S]{0,160}?•\s*zero[A-Za-z0-9_']*QuadraticForm\b"
)
REVIEW_CONSTANT_LITERAL_FUN_RE = re.compile(
    r"(?m)^\s*(?P<field>[A-Za-z0-9_']+)\s*:=\s*fun\s+"
    r"(?:_[^=]*|[A-Za-z0-9_']+(?:\s+[A-Za-z0-9_']+)*)\s*=>\s*(?P<value>0|1|True|False)\b"
)
REVIEW_IDENTITY_FUN_RE = re.compile(
    r"(?m)^\s*(?P<field>[A-Za-z0-9_']+)\s*:=\s*fun\s+(?P<arg>[A-Za-z0-9_']+)\s*=>\s*(?P=arg)\b"
)
REVIEW_ID_LINEAR_MAP_RE = re.compile(
    r"(?m)^\s*(?P<field>[A-Za-z0-9_']+)\s*:=\s*fun\s+_\s*=>\s*(?P<kind>LinearMap|ContinuousLinearMap)\.id\b"
)
LOCAL_SOURCE_RE = r"(?:[a-z][A-Za-z0-9_']*|[A-Z][A-Za-z0-9_']{0,2})"
REVIEW_PROJECTION_THEOREM_RE = re.compile(
    r"(?ms)^\s*(?:theorem|lemma)\s+(?P<name>[A-Za-z0-9_']+)\b"
    r"[\s\S]{0,700}?:=\s*by\s+"
    r"(?:intro[^\n]*\n\s+|have[^\n]*\n\s+|let[^\n]*\n\s+|refine[^\n]*\n\s+|constructor[^\n]*\n\s+)*"
    r"(?P<body>(?:exact|simpa(?:\s*\[[^\]]*\])?\s+using)\s+"
    + LOCAL_SOURCE_RE +
    r"\.[A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*)"
)


@dataclass(frozen=True)
class Finding:
    category: str
    path: str
    line: int
    detail: str


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def module_to_path(module: str) -> Path | None:
    lean_path = ROOT / "lean" / Path(module.replace(".", "/")).with_suffix(".lean")
    if lean_path.exists():
        return lean_path
    direct_path = ROOT / Path(module.replace(".", "/")).with_suffix(".lean")
    if direct_path.exists():
        return direct_path
    return None


def read_quarantine_manifest() -> dict[str, str]:
    manifest: dict[str, str] = {}
    for raw_line in MANIFEST.read_text().splitlines():
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
    for path in (ROOT / "lean/InfoGeometry/Unstable").glob("*.lean"):
        mods.add(rel(path))
    return mods


def iter_files(mode: str) -> list[Path]:
    patterns = PROJECT_PATTERNS_STABLE if mode == "stable" else PROJECT_PATTERNS_FULL
    files = sorted(
        {
            path
            for pattern in patterns
            for path in ROOT.glob(pattern)
            if path.is_file() and ".lake/" not in path.as_posix()
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


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def scan_manifest_consistency() -> list[Finding]:
    manifest = read_quarantine_manifest()
    quarantine = ROOT / "lean/InfoGeometry/Unstable/Quarantine.lean"
    imported: set[str] = set()
    for line in quarantine.read_text().splitlines():
        line = line.strip()
        if line.startswith("import "):
            imported.add(line.split()[1])

    findings: list[Finding] = []
    for module, reason in sorted(manifest.items()):
        if module not in imported:
            path = module_to_path(module)
            findings.append(
                Finding(
                    "quarantine-manifest",
                    rel(path) if path is not None else module,
                    1,
                    f"missing from InfoGeometry.Unstable.Quarantine ({reason})",
                )
            )
    return findings


def scan_file(path: Path, *, include_review: bool = False) -> list[Finding]:
    text = path.read_text()
    rpath = rel(path)
    findings: list[Finding] = []

    for match in PROOF_HOLE_RE.finditer(text):
        findings.append(Finding("proof-hole", rpath, line_of(text, match.start()), match.group(0)))
    for match in AXIOM_RE.finditer(text):
        findings.append(Finding("axiom", rpath, line_of(text, match.start()), "axiom declaration"))
    for match in TRUE_PROP_RE.finditer(text):
        findings.append(Finding("prop-constant", rpath, line_of(text, match.start()), "declaration reduces to True"))
    for match in FALSE_PROP_RE.finditer(text):
        findings.append(Finding("prop-constant", rpath, line_of(text, match.start()), "declaration reduces to False"))
    for match in TRIVIAL_THEOREM_RE.finditer(text):
        findings.append(Finding("trivial-theorem", rpath, line_of(text, match.start()), "theorem/lemma proven by trivial"))
    for match in UNIVERSAL_TRUE_FIELD_RE.finditer(text):
        findings.append(Finding("universal-true-field", rpath, line_of(text, match.start()), "field stores ∀ _, True"))
    for match in ZERO_QUADRATIC_FORM_RE.finditer(text):
        findings.append(Finding("zero-quadratic-form", rpath, line_of(text, match.start()), "quadratic form declaration reduces to 0"))
    for match in SCALED_ZERO_QUADRATIC_FORM_RE.finditer(text):
        findings.append(
            Finding(
                "scaled-zero-quadratic-form",
                rpath,
                line_of(text, match.start()),
                "quadratic form declaration scales a zero quadratic form surrogate",
            )
        )
    if include_review:
        for match in REVIEW_CONSTANT_LITERAL_FUN_RE.finditer(text):
            findings.append(
                Finding(
                    "review-constant-function",
                    rpath,
                    line_of(text, match.start()),
                    f"{match.group('field')} is a constant function returning {match.group('value')}",
                )
            )
        for match in REVIEW_IDENTITY_FUN_RE.finditer(text):
            findings.append(
                Finding(
                    "review-identity-function",
                    rpath,
                    line_of(text, match.start()),
                    f"{match.group('field')} is an identity function",
                )
            )
        for match in REVIEW_ID_LINEAR_MAP_RE.finditer(text):
            findings.append(
                Finding(
                    "review-identity-linear-map",
                    rpath,
                    line_of(text, match.start()),
                    f"{match.group('field')} is a constant {match.group('kind')}.id map",
                )
            )
        for match in REVIEW_PROJECTION_THEOREM_RE.finditer(text):
            findings.append(
                Finding(
                    "review-projection-theorem",
                    rpath,
                    line_of(text, match.start()),
                    f"{match.group('name')} reduces to `{match.group('body').strip()}`",
                )
            )

    return findings


def print_findings(mode: str, findings: list[Finding]) -> None:
    if mode == "stable":
        header = "Constructivity audit (stable surface)"
    elif mode == "review":
        header = "Constructivity audit (review-only full tree)"
    else:
        header = "Constructivity audit (full tree)"
    print(header)
    if not findings:
        print("No exact constructivity violations found.")
        return
    for finding in findings:
        print(f"{finding.category}: {finding.path}:{finding.line}: {finding.detail}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit Lean files for exact nonconstructive patterns.")
    parser.add_argument("--mode", choices=("stable", "full", "review"), default="stable")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args()

    findings: list[Finding] = scan_manifest_consistency()
    include_review = args.mode == "review"
    for path in iter_files(args.mode):
        findings.extend(scan_file(path, include_review=include_review))

    findings.sort(key=lambda item: (item.path, item.line, item.category))
    if args.as_json:
        print(json.dumps({
            "mode": args.mode,
            "findings": [finding.__dict__ for finding in findings],
        }, indent=2))
    else:
        print_findings(args.mode, findings)

    if args.mode == "stable" and findings:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
