#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.quality.common import QUARANTINE_MANIFEST_PATH, line_of, module_to_path, rel
    from tools.pathing import repo_root
else:
    from tools.quality.common import QUARANTINE_MANIFEST_PATH, line_of, module_to_path, rel
    from tools.pathing import repo_root

ROOT = repo_root()
MANIFEST = QUARANTINE_MANIFEST_PATH

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
    r"[\s\S]{0,500}?:=\s*by[ \t]*(?:\n[ \t]*)?"
    r"(?:exact[ \t]+)?trivial[ \t]*(?:--[^\n]*)?(?=\n|$)"
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


def strip_comments(
    text: str,
    *,
    strip_strings: bool = False,
    strip_quoted_identifiers: bool = False,
    keep_docstrings: bool = False,
) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    is_doc = False
    in_line = False
    in_string = False
    in_quoted_identifier = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                if is_doc:
                    out.extend(["/", "-"])
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                if is_doc:
                    out.extend(["-", "/"])
                if block_depth == 0:
                    is_doc = False
                i += 2
                continue
            if is_doc:
                out.append(ch)
            elif ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if in_quoted_identifier:
            if ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            if ch == "»":
                in_quoted_identifier = False
            i += 1
            continue

        if in_string:
            if ch == "\n":
                out.append("\n")
            elif strip_strings:
                out.append(" ")
            else:
                out.append(ch)
            if ch == '"' and (i == 0 or text[i - 1] != "\\"):
                in_string = False
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(" " if strip_strings else ch)
            i += 1
            continue
        if ch == "«" and strip_quoted_identifiers:
            in_quoted_identifier = True
            out.append(" ")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            in_line = True
            out.extend("  ")
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            nnxt = text[i + 2] if i + 2 < n else ""
            if keep_docstrings and (nnxt == "-" or nnxt == "!"):
                is_doc = True
                out.extend(["/", "-"])
            else:
                out.extend("  ")
            i += 2
            continue

        out.append(ch)
        i += 1

    return "".join(out)


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
    if not path.is_file():
        return []
    try:
        text = path.read_text()
    except (OSError, UnicodeDecodeError):
        return []
    scan_text = strip_comments(text)
    proof_hole_text = strip_comments(text, strip_strings=True, strip_quoted_identifiers=True)
    # Trace-class names may legitimately contain the token `admit` (for
    # example `DAG.Morphism.admit`).  They are diagnostics, not proof terms;
    # do not report the registration declaration as closure debt.
    proof_hole_text = re.sub(
        r"^\s*(?:initialize\s+)?registerTraceClass\b[^\n]*$",
        "",
        proof_hole_text,
        flags=re.MULTILINE,
    )
    proof_hole_text = re.sub(
        r"^\s*trace\[[^\]]*\.admit\][^\n]*$",
        "",
        proof_hole_text,
        flags=re.MULTILINE,
    )
    rpath = rel(path)
    findings: list[Finding] = []

    for match in PROOF_HOLE_RE.finditer(proof_hole_text):
        findings.append(Finding("proof-hole", rpath, line_of(proof_hole_text, match.start()), match.group(0)))
    for match in AXIOM_RE.finditer(scan_text):
        findings.append(Finding("axiom", rpath, line_of(scan_text, match.start()), "axiom declaration"))
    for match in TRUE_PROP_RE.finditer(scan_text):
        findings.append(Finding("prop-constant", rpath, line_of(scan_text, match.start()), "declaration reduces to True"))
    for match in FALSE_PROP_RE.finditer(scan_text):
        findings.append(Finding("prop-constant", rpath, line_of(scan_text, match.start()), "declaration reduces to False"))
    for match in TRIVIAL_THEOREM_RE.finditer(scan_text):
        findings.append(Finding("trivial-theorem", rpath, line_of(scan_text, match.start()), "theorem/lemma proven by trivial"))
    for match in UNIVERSAL_TRUE_FIELD_RE.finditer(scan_text):
        findings.append(Finding("universal-true-field", rpath, line_of(scan_text, match.start()), "field stores ∀ _, True"))
    for match in ZERO_QUADRATIC_FORM_RE.finditer(scan_text):
        findings.append(Finding("zero-quadratic-form", rpath, line_of(scan_text, match.start()), "quadratic form declaration reduces to 0"))
    for match in SCALED_ZERO_QUADRATIC_FORM_RE.finditer(scan_text):
        findings.append(
            Finding(
                "scaled-zero-quadratic-form",
                rpath,
                line_of(scan_text, match.start()),
                "quadratic form declaration scales a zero quadratic form surrogate",
            )
        )
    if include_review:
        for match in REVIEW_CONSTANT_LITERAL_FUN_RE.finditer(scan_text):
            findings.append(
                Finding(
                    "review-constant-function",
                    rpath,
                    line_of(scan_text, match.start()),
                    f"{match.group('field')} is a constant function returning {match.group('value')}",
                )
            )
        for match in REVIEW_IDENTITY_FUN_RE.finditer(scan_text):
            findings.append(
                Finding(
                    "review-identity-function",
                    rpath,
                    line_of(scan_text, match.start()),
                    f"{match.group('field')} is an identity function",
                )
            )
        for match in REVIEW_ID_LINEAR_MAP_RE.finditer(scan_text):
            findings.append(
                Finding(
                    "review-identity-linear-map",
                    rpath,
                    line_of(scan_text, match.start()),
                    f"{match.group('field')} is a constant {match.group('kind')}.id map",
                )
            )
        for match in REVIEW_PROJECTION_THEOREM_RE.finditer(scan_text):
            findings.append(
                Finding(
                    "review-projection-theorem",
                    rpath,
                    line_of(scan_text, match.start()),
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
