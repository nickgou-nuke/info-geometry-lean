#!/usr/bin/env python3
"""Semantic vacuity audit for proof-only Lean cleanup.

This is deliberately a code-auditor, not a theorem authority.  Lean remains the
proof authority; this script finds semantic smells where code shape indicates
that proof debt may have been hidden in carrier fields, witnesses, reexports, or
trivial promoted surfaces.

The pattern file is living policy.  When a new vacuity form is discovered, add a
category or regex to tools/quality/semantic_vacuity_patterns.json and rerun this
script so future loop iterations cannot repeat the pattern silently.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

DEFAULT_PATTERNS = Path(__file__).with_name("semantic_vacuity_patterns.json")

DECL_RE = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
CARRIER_RE = re.compile(r"^\s*(structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
TYPE_SURFACE_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)[^\n]*:\s*Type(?:\s+\d+|\s+_)\s*:?="
)
FIELD_RE = re.compile(r"^\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(?!=)(.+?)\s*$")
DIRECT_ALIAS_ABBREV_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?abbrev\s+([A-Za-z_][A-Za-z0-9_'.]*)\b[^:=\n]*:=\s*([A-Za-z0-9_'.]+)\b",
    re.MULTILINE,
)
DYNAMIC_LITERAL_DEF_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
    r"[\s\S]{0,500}?:=\s*(0|1)\b"
)
CONSTANT_FUNCTION_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*fun\s+"
    r"(?:_[^=]*|[A-Za-z0-9_']+(?:\s+[A-Za-z0-9_']+)*)\s*=>\s*(0|1|True|False)\b",
    re.MULTILINE,
)
IDENTITY_FUNCTION_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*fun\s+([A-Za-z0-9_']+)\s*=>\s*\2\b",
    re.MULTILINE,
)
IDENTITY_MAP_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*fun\s+_\s*=>\s*"
    r"(LinearMap|ContinuousLinearMap)\.id\b",
    re.MULTILINE,
)
END_TOP_RE = re.compile(r"^\s*(def|theorem|lemma|abbrev|structure|class|inductive|namespace|section|end|variable|open|import)\b")


@dataclass(frozen=True)
class Finding:
    file: str
    line: int
    category: str
    severity: str
    subject: str
    detail: str


def load_patterns(path: Path) -> dict[str, Any]:
    with path.open() as f:
        data = json.load(f)
    if not isinstance(data, dict) or not isinstance(data.get("categories"), dict):
        raise ValueError(f"invalid semantic vacuity pattern file: {path}")
    return data


def lean_files(roots: list[Path]) -> list[Path]:
    files: list[Path] = []
    for root in roots:
        if root.is_file() and root.suffix == ".lean":
            files.append(root)
        elif root.is_dir():
            for p in root.rglob("*.lean"):
                if any(part in {".lake", ".changes"} for part in p.parts):
                    continue
                files.append(p)
    return sorted(set(files))


def tracked_lean_files() -> list[Path]:
    """Return tracked/nonignored Lean sources for release audits."""
    import subprocess

    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        check=True,
        capture_output=True,
        text=True,
    )
    return sorted(
        Path(line)
        for line in result.stdout.splitlines()
        if line.startswith("lean/") and line.endswith(".lean")
    )


def theorem_window(lines: list[str], start: int) -> str:
    chunk: list[str] = []
    for line in lines[start : min(start + 18, len(lines))]:
        if chunk and re.match(r"^\s*(theorem|lemma|def|structure|class|inductive)\s+", line):
            break
        chunk.append(line)
    text = "\n".join(chunk)
    if ":=" in text:
        return text.split(":=", 1)[1].strip()
    return ""


def is_trivial_surface(proof: str, trivial_re: re.Pattern[str]) -> bool:
    proof_lines = [line.strip() for line in proof.splitlines() if line.strip()]
    if len(proof_lines) > 2 and proof_lines[0] == "by":
        return False
    return bool(trivial_re.search(proof))


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_char = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if ch == "\"":
                    in_string = False
                i += 1
            continue
        if in_char:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if ch == "'":
                    in_char = False
                i += 1
            continue
        if ch == "-" and nxt == "-":
            j = text.find("\n", i)
            if j == -1:
                out.extend(" " for _ in text[i:])
                break
            out.extend(" " for _ in text[i:j])
            out.append("\n")
            i = j + 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
            continue
        if ch == "\"":
            in_string = True
        # Apostrophes are valid in Lean identifiers.  Only enter char-literal
        # mode for the syntactic `'x'` shape, otherwise doc comments such as
        # `foo'` can hide the remainder of the file from this scanner.
        elif ch == "'" and i + 2 < len(text) and text[i + 2] == "'":
            in_char = True
        out.append(ch)
        i += 1
    return "".join(out)


def audit_text(path_label: str, raw_text: str, categories: dict[str, Any]) -> list[Finding]:
    findings: list[Finding] = []
    text = strip_comments(raw_text)
    rel = path_label
    lines = text.splitlines()

    placeholder = categories.get("placeholder_token", {})
    token_re = re.compile(r"^\s*(axiom|postulate)\b|\b(admit|sorry)\b")
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        if stripped.startswith(("--", "/-", "*")) or '"' in stripped or "`" in stripped:
            continue
        if token_re.search(stripped):
            findings.append(Finding(rel, i, "placeholder_token", placeholder.get("severity", "error"), "token", stripped))

    carrier_name_cfg = categories.get("carrier_witness_name", {})
    carrier_name_re = re.compile(carrier_name_cfg.get("name_regex", r"a^"))
    field_cfg = categories.get("proof_carrier_field", {})
    field_name_re = re.compile(field_cfg.get("name_regex", r"a^"), re.IGNORECASE)
    field_type_re = re.compile(field_cfg.get("type_regex", r"a^"))
    proof_type_cfg = categories.get("proof_like_field_type", {})

    current_carrier: str | None = None
    for i, line in enumerate(lines, 1):
        cm = CARRIER_RE.match(line)
        if cm:
            current_carrier = cm.group(2)
            if carrier_name_re.search(current_carrier):
                findings.append(
                    Finding(rel, i, "carrier_witness_name", carrier_name_cfg.get("severity", "error"), current_carrier, line.strip())
                )
            continue
        if current_carrier and END_TOP_RE.match(line) and not line.startswith((" ", "\t")):
            current_carrier = None
        if current_carrier:
            fm = FIELD_RE.match(line)
            if not fm:
                continue
            name, typ = fm.group(1), fm.group(2)
            type_core = typ.split(":=", 1)[0].strip()
            name_hit = bool(field_name_re.search(name))
            type_hit = bool(field_type_re.search(type_core))
            if type_hit and proof_type_cfg:
                findings.append(
                    Finding(
                        rel,
                        i,
                        "proof_like_field_type",
                        proof_type_cfg.get("severity", "warning"),
                        f"{current_carrier}.{name}",
                        f"{name} : {type_core}",
                    )
                )
            if name_hit and type_hit:
                findings.append(
                    Finding(
                        rel,
                        i,
                        "proof_carrier_field",
                        field_cfg.get("severity", "error"),
                        f"{current_carrier}.{name}",
                        f"{name} : {type_core}",
                    )
                )

    type_surface_cfg = categories.get("typed_surface_name", {})
    type_surface_re = re.compile(type_surface_cfg.get("name_regex", r"a^"))
    if type_surface_cfg:
        for i, line in enumerate(lines, 1):
            tm = TYPE_SURFACE_RE.match(line)
            if tm and type_surface_re.search(tm.group(1)):
                findings.append(
                    Finding(
                        rel,
                        i,
                        "typed_surface_name",
                        type_surface_cfg.get("severity", "warning"),
                        tm.group(1),
                        "definition-level Type surface uses witness/interface/packet vocabulary; inspect for a concrete owner theorem",
                    )
                )
    dynamic_cfg = categories.get("dynamic_literal_definition", {})
    dynamic_tokens = [str(t).lower() for t in dynamic_cfg.get("name_tokens", [])]
    if dynamic_cfg:
        for m in DYNAMIC_LITERAL_DEF_RE.finditer(text):
            name = m.group(1)
            if any(token in name.lower() for token in dynamic_tokens):
                findings.append(
                    Finding(
                        rel,
                        text.count("\n", 0, m.start()) + 1,
                        "dynamic_literal_definition",
                        dynamic_cfg.get("severity", "warning"),
                        name,
                        f"{name} := {m.group(2)}",
                    )
                )

    alias_cfg = categories.get("direct_alias_abbrev", {})
    if alias_cfg:
        for m in DIRECT_ALIAS_ABBREV_RE.finditer(text):
            findings.append(
                Finding(
                    rel,
                    text.count("\n", 0, m.start()) + 1,
                    "direct_alias_abbrev",
                    alias_cfg.get("severity", "warning"),
                    m.group(1),
                    f"abbrev aliases {m.group(2)}",
                )
            )

    const_cfg = categories.get("constant_function", {})
    if const_cfg:
        for m in CONSTANT_FUNCTION_RE.finditer(text):
            findings.append(
                Finding(
                    rel,
                    text.count("\n", 0, m.start()) + 1,
                    "constant_function",
                    const_cfg.get("severity", "warning"),
                    m.group(1),
                    f"function returns constant {m.group(2)}",
                )
            )

    identity_cfg = categories.get("identity_or_noop_function", {})
    if identity_cfg:
        for regex in (IDENTITY_FUNCTION_RE, IDENTITY_MAP_RE):
            for m in regex.finditer(text):
                findings.append(
                    Finding(
                        rel,
                        text.count("\n", 0, m.start()) + 1,
                        "identity_or_noop_function",
                        identity_cfg.get("severity", "warning"),
                        m.group(1),
                        "function is an identity/no-op mapping",
                    )
                )

    projection_cfg = categories.get("projection_reexport", {})
    projection_re = re.compile(projection_cfg.get("proof_regex", r"a^"))
    trivial_cfg = categories.get("trivial_surface", {})
    trivial_re = re.compile(trivial_cfg.get("proof_regex", r"a^"), re.DOTALL)
    for i, line in enumerate(lines, 1):
        dm = DECL_RE.match(line)
        if not dm:
            continue
        proof = theorem_window(lines, i - 1)
        if not proof:
            continue
        name = dm.group(2)
        if not proof.startswith("by") and projection_re.search(proof):
            findings.append(
                Finding(rel, i, "projection_reexport", projection_cfg.get("severity", "error"), name, proof.splitlines()[0][:180])
            )
        if is_trivial_surface(proof, trivial_re):
            findings.append(
                Finding(rel, i, "trivial_surface", trivial_cfg.get("severity", "warning"), name, proof.splitlines()[0][:180])
            )

    return findings


def audit_file(path: Path, categories: dict[str, Any]) -> list[Finding]:
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, FileNotFoundError):
        return []
    return audit_text(str(path), text, categories)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="*", default=["lean"], help="Lean files/directories to audit")
    ap.add_argument("--patterns", type=Path, default=DEFAULT_PATTERNS)
    ap.add_argument("--json-out", type=Path)
    ap.add_argument("--tracked", action="store_true", help="use tracked/nonignored Lean sources")
    ap.add_argument("--fail-on", choices=["none", "error", "warning"], default="error")
    ap.add_argument("--top", type=int, default=80)
    args = ap.parse_args()

    policy = load_patterns(args.patterns)
    categories = policy["categories"]
    findings: list[Finding] = []
    paths = tracked_lean_files() if args.tracked else lean_files([Path(r) for r in args.roots])
    for path in paths:
        findings.extend(audit_file(path, categories))

    counts: dict[str, int] = {}
    severity_counts: dict[str, int] = {}
    for f in findings:
        counts[f.category] = counts.get(f.category, 0) + 1
        severity_counts[f.severity] = severity_counts.get(f.severity, 0) + 1

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(
                {
                    "pattern_version": policy.get("version"),
                    "counts": counts,
                    "severity_counts": severity_counts,
                    "findings": [f.__dict__ for f in findings],
                },
                indent=2,
                sort_keys=True,
            )
            + "\n"
        )

    print("Semantic vacuity audit")
    print("======================")
    print(f"roots: {', '.join(args.roots)}")
    print(f"patterns: {args.patterns}")
    print(f"semantic_vacuity: {len(findings)}")
    for sev in sorted(severity_counts):
        print(f"{sev}: {severity_counts[sev]}")
    for cat in sorted(counts):
        print(f"{cat}: {counts[cat]}")
    for f in findings[: args.top]:
        print(f"  - {f.file}:{f.line} [{f.severity}/{f.category}] {f.subject}: {f.detail}")

    if args.fail_on == "none":
        return 0
    if args.fail_on == "warning" and findings:
        return 1
    if args.fail_on == "error" and severity_counts.get("error", 0):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
