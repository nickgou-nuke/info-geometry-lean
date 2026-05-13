#!/usr/bin/env python3
from __future__ import annotations

"""
Closure Debt Crawler for Lean repositories.

Goal:
- Crawl Lean files recursively.
- Detect temporary trust/debt constructs (proof holes, axioms, postulates, opaque stubs,
  witness packaging, placeholder assumptions, skeletal proofs, vacuous props).
- Emit per-file debt reports plus aggregate summary.

This is a heuristic auditor; Lean kernel remains theorem-truth authority.
"""

import argparse
import json
import re
import shlex
import subprocess
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality import audit_constructivity
else:
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality import audit_constructivity

ROOT = repo_root()

DECL_HEADER_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:partial\s+)?(?:private\s+|protected\s+|local\s+)?"
    r"(theorem|lemma|example|def|abbrev|structure|class|instance|axiom|postulate|inductive)\b"
    r"\s+([A-Za-z0-9_'.]+)",
    re.M,
)

# Restrict hard proof-hole detection to term-level placeholders. `sorryAx`/`admitAx`
# may appear as metadata identifiers and are handled separately as advisory context.
PROOF_HOLE_RE = re.compile(r"(?<!\.)(?<!\w)(?:sorry|admit)(?!\w)")
AXIOM_DECL_RE = re.compile(r"^\s*axiom\b", re.M)
POSTULATE_DECL_RE = re.compile(r"^\s*postulate\b", re.M)
OPAQUE_DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+|local\s+)?opaque\b", re.M)
PARTIAL_DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?partial\s+(?:def|theorem|lemma|instance)\b", re.M)
TERMINATION_HOLE_RE = re.compile(r"(?ms)\bdecreasing_by\b[\s\S]{0,500}\b(?:sorry|admit)\b")
REALITY_WARP_RE = re.compile(r"^\s*(?:local\s+)?(?:notation|infix|prefix|postfix|macro)\b", re.M)
SIMP_LAW_RE = re.compile(
    r"(?ms)^\s*@\[[^\]]*\bsimp\b[^\]]*\]\s*"
    r"(?:private\s+|protected\s+|local\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_'.]+)"
)
UNSAFE_CAST_RE = re.compile(r"\b(?:unsafeCast|cast\s+|Eq\.ndrec|Eq\.mp|Eq\.mpr|propext)\b")

VAR_ASSUME_RE = re.compile(r"^\s*variable\s*\([^\n]*:[^\n]*\)\s*$", re.M)
VARIABLE_LAW_RE = re.compile(r"(?m)^\s*variable\s*\(\s*([A-Za-z0-9_'.]+)\s*:\s*([^\n]+)\)\s*$")
WITNESS_FIELD_RE = re.compile(r"(?m)^\s*([A-Za-z0-9_']+_valid)\s*:\s*([A-Za-z0-9_'.]+)\s*$")
UNIVERSAL_TRUE_FIELD_RE = re.compile(r"(?m)^\s*[A-Za-z0-9_']+\s*:\s*∀\s+[^\n]*,\s*True\s*$")

# placeholder naming conventions discussed in the session
PLACEHOLDER_NAME_RE = re.compile(r"^(?:external|hyp|unproven|todo|stub|bridge)_", re.I)

VacuousPropRe = re.compile(
    r"(?ms)^\s*(?:theorem|lemma|def|abbrev)\s+[A-Za-z0-9_'.]+\b"
    r"[\s\S]{0,700}?:\s*Prop\s*:=\s*(?:--[^\n]*\n\s*)*(?:True|False)\b"
)

SKELETAL_ONE_LINER_RE = re.compile(
    r"(?ms)^\s*(?:theorem|lemma|example)\s+[A-Za-z0-9_'.]+\b"
    r"[\s\S]{0,900}?:=\s*(?:by\s*)?(?:rfl|trivial|simp|simpa|aesop|linarith|omega|ring|exact\s+True\.intro)\b"
)

EXIST_PACKAGING_RE = re.compile(r"\b(?:Nonempty|Exists)\b|∃")
CLASSICAL_WITNESS_RE = re.compile(
    r"\b(?:Classical\.choice|Classical\.choose|Nonempty\.some|Exists\.choose|Exists\.choose_spec|Classical\.epsilon)\b"
)
LOCAL_HYPOTHESIS_RE = re.compile(
    r"(?m)^\s*(?:have|suffices)\s+([A-Za-z0-9_']+)?\s*:\s*(.{1,240}?)\s*(?::=|by|from)"
)
BRIDGE_NAME_RE = re.compile(
    r"(?:^|[_.'])(?:bridge|compat|compatibility|readback|socket|packet|claim|witness|external|hyp|assumption|admit|stub|placeholder)(?:$|[_.'])",
    re.I,
)
PROP_LIKE_FIELD_RE = re.compile(r"(?m)^\s*([A-Za-z0-9_']+)\s*:\s*([^\n]+)$")
LEAN_IDENTIFIER_RE = re.compile(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_'.]*)(?![A-Za-z0-9_'.])")
STRUCTURE_MK_RE = re.compile(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_'.]*)\.mk(?![A-Za-z0-9_'.])")
ANNOTATED_CONSTRUCTOR_RE = re.compile(
    r"(?m):\s*([A-Za-z_][A-Za-z0-9_'.]*)\b[^\n]*(?:where|:=)"
)


def prop_like_field_type(type_text: str) -> bool:
    ty = type_text.strip()
    if not ty:
        return False
    if ty.startswith("/--") or ty.startswith("--"):
        return False
    if "Type" in ty or "Sort" in ty:
        return False
    return any(token in ty for token in ("Prop", "∀", "∃", "=", "↔", "→", "->", "<", "≤", "≥"))


@dataclass(frozen=True)
class Finding:
    category: str
    severity: str  # hard|soft|advisory
    line: int
    declaration_kind: str
    declaration_name: str
    detail: str


@dataclass(frozen=True)
class FileReport:
    path: str
    module: str
    status: str  # clean|advisory|open_gap
    debt_score: int
    hard_count: int
    soft_count: int
    advisory_count: int
    finding_count: int
    findings: list[Finding]


@dataclass(frozen=True)
class CodingAgentAuditConfig:
    command: list[str]
    timeout_seconds: int
    max_chars: int


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def module_name(path: Path) -> str:
    try:
        rp = path.resolve().relative_to(ROOT / "lean").with_suffix("").as_posix()
        return rp.replace("/", ".")
    except ValueError:
        try:
            rp = path.resolve().relative_to(ROOT).with_suffix("").as_posix()
            return rp.replace("/", ".")
        except ValueError:
            return path.stem


def line_of(text: str, offset: int) -> int:
    return audit_constructivity.line_of(text, offset)


def strip_comments(text: str) -> str:
    return audit_constructivity.strip_comments(text, strip_strings=True, strip_quoted_identifiers=True)


def iter_lean_files(root: Path) -> Iterable[Path]:
    if root.is_file():
        if root.suffix == ".lean":
            yield root
        return

    skip_dirs = {".git", ".lake", "lake-packages", ".cache", "node_modules", ".venv"}
    for path in sorted(root.rglob("*.lean")):
        if not path.is_file():
            continue
        if any(part in skip_dirs for part in path.parts):
            continue
        yield path


def find_decl_blocks(clean_text: str) -> list[tuple[str, str, int, str]]:
    blocks: list[tuple[str, str, int, str]] = []
    headers = list(DECL_HEADER_RE.finditer(clean_text))
    for idx, m in enumerate(headers):
        kind = m.group(1)
        name = m.group(2)
        start = m.start()
        end = headers[idx + 1].start() if idx + 1 < len(headers) else len(clean_text)
        blocks.append((kind, name, line_of(clean_text, start), clean_text[start:end]))
    return blocks


def proof_body(block: str) -> str:
    idx = block.find(":=")
    if idx < 0:
        return ""
    return block[idx + 2 :].strip()


def classify_block(kind: str, name: str, line: int, block: str) -> list[Finding]:
    out: list[Finding] = []

    if kind in {"axiom", "postulate"}:
        out.append(
            Finding(
                category="global-assumption",
                severity="hard",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail=f"{kind} declaration introduces global trust debt",
            )
        )

    if PROOF_HOLE_RE.search(block):
        out.append(
            Finding(
                category="proof-hole",
                severity="hard",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration body contains sorry/admit placeholder",
            )
        )

    if re.search(r"\b(?:sorryAx|admitAx)\b", block):
        out.append(
            Finding(
                category="kernel-placeholder-reference",
                severity="advisory",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration references sorryAx/admitAx symbol; verify this is metadata/lint context, not a proof hole",
            )
        )

    body = proof_body(block)

    if kind in {"theorem", "lemma", "example"} and body and SKELETAL_ONE_LINER_RE.match(block):
        out.append(
            Finding(
                category="skeletal-proof",
                severity="soft",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="proof appears to close via minimal tactic one-liner",
            )
        )

    if PLACEHOLDER_NAME_RE.match(name):
        out.append(
            Finding(
                category="placeholder-naming",
                severity="advisory",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration name indicates temporary/external hypothesis surface",
            )
        )

    if EXIST_PACKAGING_RE.search(block) and kind in {"theorem", "lemma", "def", "abbrev", "structure", "class"}:
        out.append(
            Finding(
                category="existential-packaging",
                severity="advisory",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration uses Nonempty/Exists packaging; verify eventual constructive readback",
            )
        )

    if CLASSICAL_WITNESS_RE.search(block):
        out.append(
            Finding(
                category="classical-witness-smuggling",
                severity="soft",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary",
            )
        )

    if BRIDGE_NAME_RE.search(name) and kind in {"theorem", "lemma", "def", "abbrev"}:
        out.append(
            Finding(
                category="bridge-shaped-declaration",
                severity="advisory",
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                detail="declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof",
            )
        )

    if kind in {"structure", "class"}:
        for field in PROP_LIKE_FIELD_RE.finditer(block):
            field_name = field.group(1)
            field_type = field.group(2).strip()
            if field_name in {"where", "extends"}:
                continue
            if prop_like_field_type(field_type):
                out.append(
                    Finding(
                        category="law-field-locker",
                        severity="soft",
                        line=line_of(block, field.start()) + line - 1,
                        declaration_kind=f"{kind}-field",
                        declaration_name=f"{name}.{field_name}",
                        detail=(
                            "Prop/equality/order/forall-like structure field detected; this may store a "
                            "theorem as an assumption unless instantiated from mathlib/repo proofs"
                        ),
                    )
                )

    for m in LOCAL_HYPOTHESIS_RE.finditer(block):
        hyp_type = m.group(2).strip()
        if prop_like_field_type(hyp_type):
            out.append(
                Finding(
                    category="local-hypothesis-injection",
                    severity="advisory",
                    line=line_of(block, m.start()) + line - 1,
                    declaration_kind=kind,
                    declaration_name=name,
                    detail=(
                        "local `have`/`suffices` introduces a proposition-shaped intermediate; "
                        "verify it is proved from existing context rather than restating the missing bridge"
                    ),
                )
            )

    return out


def build_coding_agent_prompt(path: Path, raw: str, heuristic_findings: list[Finding], max_chars: int) -> str:
    truncated = len(raw) > max_chars
    source = raw[:max_chars]
    heuristic_payload = [asdict(f) for f in heuristic_findings[:200]]
    return (
        "You are auditing a Lean 4 file in info-geometry-lean for missing-proof debt.\n"
        "Lean/mathlib/repo proofs are the only authority. Do not treat comments, witness fields,\n"
        "Prop packets, naming, graph proximity, or informal theorem-shape prose as proof.\n"
        "Find constructs that hide unproved theory: witness packets, law fields without owner\n"
        "derivation, theorem-like structures that merely store assumptions, vacuous readout laws,\n"
        "bridges that should be lemmas from mathlib/repo facts, custom simp laws that poison\n"
        "automation, theorem-shaped section variables, unsafe casts, notation/macro warps, and\n"
        "proof gaps not caught by regex.\n"
        "Return JSON only, with this shape:\n"
        "{\n"
        '  "findings": [\n'
        "    {\n"
        '      "severity": "hard|soft|advisory",\n'
        '      "line": 1,\n'
        '      "category": "coding-agent-missing-proof-gap",\n'
        '      "declaration_kind": "structure|def|theorem|lemma|field|file",\n'
        '      "declaration_name": "name-or-<file-level>",\n'
        '      "detail": "specific gap and what proof lineage is missing"\n'
        "    }\n"
        "  ]\n"
        "}\n"
        "Severity rule: hard only for axioms/sorries/admit/postulates or explicit false proof authority;\n"
        "soft for constructs that likely hide missing theorem work; advisory for review debt.\n"
        "Do not report stylistic issues. Do not claim a theorem is false; report missing proof lineage.\n\n"
        f"FILE: {rel(path)}\n"
        f"MODULE: {module_name(path)}\n"
        f"SOURCE_TRUNCATED: {str(truncated).lower()}\n"
        "HEURISTIC_FINDINGS_JSON:\n"
        f"{json.dumps(heuristic_payload, ensure_ascii=False)}\n\n"
        "LEAN_SOURCE:\n"
        "```lean\n"
        f"{source}\n"
        "```\n"
    )


def _json_from_coding_agent_output(text: str) -> Any:
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        start = text.find("{")
        end = text.rfind("}")
        if start >= 0 and end > start:
            return json.loads(text[start : end + 1])
        raise


def _normalize_agent_finding(raw: Any, fallback_line: int = 1) -> Finding | None:
    if not isinstance(raw, dict):
        return None

    severity = str(raw.get("severity", "advisory")).strip().lower()
    if severity not in {"hard", "soft", "advisory"}:
        severity = "advisory"

    try:
        line = int(raw.get("line", fallback_line))
    except (TypeError, ValueError):
        line = fallback_line
    if line < 1:
        line = fallback_line

    category = str(raw.get("category", "coding-agent-missing-proof-gap")).strip()
    if not category:
        category = "coding-agent-missing-proof-gap"
    if not category.startswith("coding-agent-"):
        category = f"coding-agent-{category}"

    declaration_kind = str(raw.get("declaration_kind", "file")).strip() or "file"
    declaration_name = str(raw.get("declaration_name", "<file-level>")).strip() or "<file-level>"
    detail = str(raw.get("detail", "")).strip()
    if not detail:
        detail = "coding-agent review reported missing proof lineage without detail"

    return Finding(
        category=category,
        severity=severity,
        line=line,
        declaration_kind=declaration_kind,
        declaration_name=declaration_name,
        detail=detail,
    )


def run_coding_agent_audit(
    path: Path,
    raw: str,
    heuristic_findings: list[Finding],
    config: CodingAgentAuditConfig,
) -> list[Finding]:
    prompt = build_coding_agent_prompt(path, raw, heuristic_findings, config.max_chars)
    try:
        proc = subprocess.run(
            config.command,
            input=prompt,
            text=True,
            capture_output=True,
            timeout=config.timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return [
            Finding(
                category="coding-agent-audit-timeout",
                severity="advisory",
                line=1,
                declaration_kind="file",
                declaration_name="<file-level>",
                detail=f"coding-agent audit timed out after {config.timeout_seconds}s",
            )
        ]
    except OSError as exc:
        return [
            Finding(
                category="coding-agent-audit-error",
                severity="advisory",
                line=1,
                declaration_kind="file",
                declaration_name="<file-level>",
                detail=f"coding-agent audit command failed to start: {exc}",
            )
        ]

    if proc.returncode != 0:
        stderr = proc.stderr.strip().splitlines()
        detail = stderr[-1] if stderr else f"exit code {proc.returncode}"
        return [
            Finding(
                category="coding-agent-audit-error",
                severity="advisory",
                line=1,
                declaration_kind="file",
                declaration_name="<file-level>",
                detail=f"coding-agent audit command failed: {detail}",
            )
        ]

    try:
        payload = _json_from_coding_agent_output(proc.stdout)
    except json.JSONDecodeError as exc:
        raw_output = proc.stdout.strip().replace("\n", " ")
        if len(raw_output) > 240:
            raw_output = raw_output[:240] + "..."
        return [
            Finding(
                category="coding-agent-audit-invalid-json",
                severity="advisory",
                line=1,
                declaration_kind="file",
                declaration_name="<file-level>",
                detail=f"coding-agent audit did not return JSON: {exc}; output={raw_output!r}",
            )
        ]

    raw_findings: Any
    if isinstance(payload, dict):
        raw_findings = payload.get("findings", [])
    elif isinstance(payload, list):
        raw_findings = payload
    else:
        raw_findings = []

    if not isinstance(raw_findings, list):
        return [
            Finding(
                category="coding-agent-audit-invalid-schema",
                severity="advisory",
                line=1,
                declaration_kind="file",
                declaration_name="<file-level>",
                detail="coding-agent audit JSON did not contain a list-valued `findings` field",
            )
        ]

    out: list[Finding] = []
    for item in raw_findings:
        finding = _normalize_agent_finding(item)
        if finding is not None:
            out.append(finding)
    return out


def audit_file(path: Path, coding_agent: CodingAgentAuditConfig | None = None) -> FileReport:
    raw = path.read_text(encoding="utf-8")
    clean = strip_comments(raw)

    findings: list[Finding] = []

    # File-level scans
    for m in AXIOM_DECL_RE.finditer(clean):
        findings.append(
            Finding(
                category="axiom-token",
                severity="hard",
                line=line_of(clean, m.start()),
                declaration_kind="file",
                declaration_name="<file-level>",
                detail="axiom token detected",
            )
        )

    for m in POSTULATE_DECL_RE.finditer(clean):
        findings.append(
            Finding(
                category="postulate-token",
                severity="hard",
                line=line_of(clean, m.start()),
                declaration_kind="file",
                declaration_name="<file-level>",
                detail="postulate token detected",
            )
        )

    for m in OPAQUE_DECL_RE.finditer(clean):
        findings.append(
            Finding(
                category="opaque-stub",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="opaque",
                declaration_name="<opaque>",
                detail="opaque declaration found; ensure behavior is justified by proved lemmas",
            )
        )

    for m in PARTIAL_DECL_RE.finditer(clean):
        findings.append(
            Finding(
                category="partial-bypass",
                severity="hard",
                line=line_of(clean, m.start()),
                declaration_kind="declaration",
                declaration_name="<partial>",
                detail="partial declaration bypasses Lean termination/productivity checking",
            )
        )

    for m in TERMINATION_HOLE_RE.finditer(clean):
        findings.append(
            Finding(
                category="termination-hole",
                severity="hard",
                line=line_of(clean, m.start()),
                declaration_kind="decreasing_by",
                declaration_name="<termination-proof>",
                detail="termination proof contains sorry/admit",
            )
        )

    for m in REALITY_WARP_RE.finditer(clean):
        findings.append(
            Finding(
                category="notation-or-macro-warp",
                severity="advisory",
                line=line_of(clean, m.start()),
                declaration_kind="syntax",
                declaration_name="<notation-or-macro>",
                detail="local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface",
            )
        )

    for m in SIMP_LAW_RE.finditer(clean):
        findings.append(
            Finding(
                category="simp-law-injection",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="simp-declaration",
                declaration_name=m.group(1),
                detail="custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law",
            )
        )

    for m in VAR_ASSUME_RE.finditer(clean):
        findings.append(
            Finding(
                category="injected-hypothesis-surface",
                severity="advisory",
                line=line_of(clean, m.start()),
                declaration_kind="variable",
                declaration_name="<section-variable>",
                detail="section variable assumption detected (valid pattern; track for closure debt)",
            )
        )

    for m in VARIABLE_LAW_RE.finditer(clean):
        var_name = m.group(1)
        var_type = m.group(2).strip()
        if prop_like_field_type(var_type):
            findings.append(
                Finding(
                    category="section-law-variable",
                    severity="soft",
                    line=line_of(clean, m.start()),
                    declaration_kind="variable",
                    declaration_name=var_name,
                    detail=(
                        "section variable has theorem-like type; verify this is an intended explicit "
                        "context boundary, not a hallucinated law injected as an assumption"
                    ),
                )
            )

    for m in VacuousPropRe.finditer(clean):
        findings.append(
            Finding(
                category="vacuous-prop",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="prop",
                declaration_name="<vacuous>",
                detail="Prop declaration appears to reduce to True/False",
            )
        )

    for m in WITNESS_FIELD_RE.finditer(clean):
        findings.append(
            Finding(
                category="witness-field-projection",
                severity="advisory",
                line=line_of(clean, m.start()),
                declaration_kind="structure-field",
                declaration_name=m.group(1),
                detail=f"witness field `{m.group(1)} : {m.group(2)}` detected; verify owner-level derivation",
            )
        )

    for m in UNIVERSAL_TRUE_FIELD_RE.finditer(clean):
        findings.append(
            Finding(
                category="placeholder-law",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="structure-field",
                declaration_name="<forall-true>",
                detail="field with `∀ ..., True` detected",
            )
        )

    for m in UNSAFE_CAST_RE.finditer(clean):
        findings.append(
            Finding(
                category="definitional-equality-bypass",
                severity="soft",
                line=line_of(clean, m.start()),
                declaration_kind="cast",
                declaration_name="<cast>",
                detail="cast/propext/unsafe equality transport detected; verify this is not hiding a failed `rfl` or definitional-equality hallucination",
            )
        )

    # Declaration-level scans
    for kind, name, line, block in find_decl_blocks(clean):
        findings.extend(classify_block(kind, name, line, block))

    if coding_agent is not None:
        findings.extend(run_coding_agent_audit(path, raw, findings, coding_agent))

    # Deduplicate
    dedup: dict[tuple[str, str, int, str, str], Finding] = {}
    for f in findings:
        key = (f.category, f.severity, f.line, f.declaration_kind, f.declaration_name)
        dedup[key] = f
    findings = sorted(dedup.values(), key=lambda x: (x.line, x.severity, x.category, x.declaration_name))

    hard = sum(1 for f in findings if f.severity == "hard")
    soft = sum(1 for f in findings if f.severity == "soft")
    advisory = sum(1 for f in findings if f.severity == "advisory")

    score = hard * 5 + soft * 2 + advisory
    if hard > 0:
        status = "open_gap"
    elif soft > 0 or advisory > 0:
        status = "advisory"
    else:
        status = "clean"

    return FileReport(
        path=rel(path),
        module=module_name(path),
        status=status,
        debt_score=score,
        hard_count=hard,
        soft_count=soft,
        advisory_count=advisory,
        finding_count=len(findings),
        findings=findings,
    )


def _recompute_report(report: FileReport, findings: list[Finding]) -> FileReport:
    dedup: dict[tuple[str, str, int, str, str], Finding] = {}
    for f in findings:
        key = (f.category, f.severity, f.line, f.declaration_kind, f.declaration_name)
        dedup[key] = f
    ordered = sorted(dedup.values(), key=lambda x: (x.line, x.severity, x.category, x.declaration_name))

    hard = sum(1 for f in ordered if f.severity == "hard")
    soft = sum(1 for f in ordered if f.severity == "soft")
    advisory = sum(1 for f in ordered if f.severity == "advisory")
    status = "open_gap" if hard > 0 else "advisory" if soft > 0 or advisory > 0 else "clean"

    return replace(
        report,
        status=status,
        debt_score=hard * 5 + soft * 2 + advisory,
        hard_count=hard,
        soft_count=soft,
        advisory_count=advisory,
        finding_count=len(ordered),
        findings=ordered,
    )


def apply_repo_wide_laundering_audit(files: list[Path], reports: list[FileReport]) -> list[FileReport]:
    """Add graph-ish source findings that need whole-repository context.

    This remains a triage layer. It catches proof-debt laundering patterns that are invisible in a
    single declaration: law-field structures that have no visible constructor site, and bridge-shaped
    declarations that are only referenced once downstream.
    """
    clean_by_rel: dict[str, str] = {}
    corpus_parts: list[str] = []
    for path in files:
        raw = path.read_text(encoding="utf-8")
        clean = strip_comments(raw)
        r = rel(path)
        clean_by_rel[r] = clean
        corpus_parts.append(clean)
    corpus = "\n".join(corpus_parts)
    identifier_counts = Counter(LEAN_IDENTIFIER_RE.findall(corpus))
    explicit_instantiation_names = set(STRUCTURE_MK_RE.findall(corpus))
    explicit_instantiation_names.update(ANNOTATED_CONSTRUCTOR_RE.findall(corpus))
    explicit_instantiation_names.update(name.split(".")[-1] for name in list(explicit_instantiation_names))

    by_path = {r.path: r for r in reports}
    additions: dict[str, list[Finding]] = {r.path: [] for r in reports}

    for report in reports:
        law_structures: dict[str, int] = {}
        for finding in report.findings:
            if finding.category != "law-field-locker":
                continue
            structure_name = finding.declaration_name.split(".")[0]
            law_structures.setdefault(structure_name, finding.line)

        for structure_name, line in law_structures.items():
            short_name = structure_name.split(".")[-1]
            if (
                structure_name not in explicit_instantiation_names
                and short_name not in explicit_instantiation_names
            ):
                additions[report.path].append(
                    Finding(
                        category="uninstantiated-law-locker",
                        severity="soft",
                        line=line,
                        declaration_kind="structure",
                        declaration_name=structure_name,
                        detail=(
                            "structure/class has theorem-like fields but no visible constructor site "
                            "(`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be "
                            "a proof-debt locker rather than implemented mathematics"
                        ),
                    )
                )

        for finding in report.findings:
            if finding.category != "bridge-shaped-declaration":
                continue
            name = finding.declaration_name
            if len(name) < 5:
                continue
            occurrences = identifier_counts.get(name, 0)
            if occurrences <= 2:
                additions[report.path].append(
                    Finding(
                        category="single-use-evidence-bridge",
                        severity="soft",
                        line=finding.line,
                        declaration_kind=finding.declaration_kind,
                        declaration_name=name,
                        detail=(
                            f"bridge-shaped declaration has only {occurrences} visible identifier "
                            "occurrence(s) in the scanned root; inspect whether it exists only to close "
                            "one downstream theorem instead of exposing reusable owner proof lineage"
                        ),
                    )
                )

    return [
        _recompute_report(report, [*report.findings, *additions.get(report.path, [])])
        for report in reports
        if report.path in by_path
    ]


def build_payload(
    root: Path,
    reports: list[FileReport],
    coding_agent_enabled: bool = False,
    coding_agent_command: list[str] | None = None,
) -> dict[str, object]:
    hard_total = sum(r.hard_count for r in reports)
    soft_total = sum(r.soft_count for r in reports)
    advisory_total = sum(r.advisory_count for r in reports)

    findings_by_severity = {
        "hard_failures": hard_total,
        "soft_findings": soft_total,
        "advisory_findings": advisory_total,
    }

    status_counts = {
        "clean": sum(1 for r in reports if r.status == "clean"),
        "advisory": sum(1 for r in reports if r.status == "advisory"),
        "open_gap": sum(1 for r in reports if r.status == "open_gap"),
    }

    top = sorted(reports, key=lambda r: (-r.debt_score, -r.hard_count, -r.soft_count, r.path))[:50]

    return {
        "schema": "info_geometry.closure_debt_crawler.v2",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": rel(root),
        "authority_tier": (
            "heuristic-proxy-plus-coding-agent-review"
            if coding_agent_enabled
            else "heuristic-proxy"
        ),
        "coding_agent_review": {
            "enabled": coding_agent_enabled,
            "command": coding_agent_command or [],
            "authority": "triage-only; Lean kernel/mathlib/repo proofs remain theorem authority",
        },
        "summary": {
            "file_count": len(reports),
            "status_counts": status_counts,
            "finding_count": hard_total + soft_total + advisory_total,
            "hard_count": hard_total,
            "soft_count": soft_total,
            "advisory_count": advisory_total,
            "provenance": findings_by_severity,
        },
        "top_debt_files": [asdict(r) for r in top],
        "files": [
            {
                **asdict(r),
                "findings": [
                    {
                        **asdict(f),
                        "graph_grounded_signal": "none",
                        "heuristic_signal": f.category,
                        "hard_verdict_allowed": f.severity == "hard",
                    }
                    for f in r.findings
                ],
            }
            for r in reports
        ],
    }


def build_markdown(payload: dict[str, object]) -> str:
    summary = payload["summary"]
    lines: list[str] = []
    lines.append("# Lean Closure Debt Crawler Report")
    lines.append("")
    lines.append(f"Generated: `{payload['generated_at']}`")
    lines.append(f"Root: `{payload['root']}`")
    lines.append(f"Authority tier: `{payload['authority_tier']}`")
    coding_agent = payload.get("coding_agent_review", {})
    if isinstance(coding_agent, dict) and coding_agent.get("enabled"):
        lines.append("")
        lines.append("Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Files scanned: **{summary['file_count']}**")
    lines.append(f"- Findings: **{summary['finding_count']}**")
    lines.append(f"- Hard: **{summary['hard_count']}**")
    lines.append(f"- Soft: **{summary['soft_count']}**")
    lines.append(f"- Advisory: **{summary['advisory_count']}**")
    status = summary["status_counts"]
    lines.append(
        "- File status counts: "
        f"clean={status['clean']}, advisory={status['advisory']}, open_gap={status['open_gap']}"
    )
    lines.append("")

    lines.append("## Per-file status")
    lines.append("")
    lines.append("| file | status | debt_score | hard | soft | advisory | findings |")
    lines.append("| --- | --- | ---: | ---: | ---: | ---: | ---: |")
    for row in payload["files"]:
        lines.append(
            f"| `{row['path']}` | `{row['status']}` | {row['debt_score']} | {row['hard_count']} | {row['soft_count']} | {row['advisory_count']} | {row['finding_count']} |"
        )

    lines.append("")
    lines.append("## Findings by file")
    lines.append("")
    for row in payload["files"]:
        lines.append(f"### `{row['path']}`")
        lines.append(f"- module: `{row['module']}`")
        lines.append(f"- status: `{row['status']}`")
        lines.append(f"- debt_score: `{row['debt_score']}`")
        if not row["findings"]:
            lines.append("- findings: none")
            lines.append("")
            continue
        lines.append("- findings:")
        for f in row["findings"]:
            lines.append(
                f"  - L{f['line']} [{f['severity']}] `{f['category']}` in `{f['declaration_kind']} {f['declaration_name']}` — {f['detail']}"
            )
        lines.append("")

    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Crawl Lean files and produce detailed per-file closure debt report for temporary assumptions, "
            "proof holes, stubs, and witness-packaging surfaces."
        )
    )
    parser.add_argument("--root", default=".", help="Directory or .lean file to scan")
    parser.add_argument("--json-out", default="reports/audit/closure-debt-crawler.json")
    parser.add_argument("--md-out", default="reports/audit/closure-debt-crawler.md")
    parser.add_argument("--strict", action="store_true", help="Exit nonzero when any hard finding exists")
    parser.add_argument("--limit", type=int, default=0, help="Limit files for smoke runs (0 = all)")
    parser.add_argument("--print-progress", action="store_true", help="Print per-file progress")
    parser.add_argument("--print-summary", action="store_true", help="Print compact summary to stdout")
    parser.add_argument(
        "--coding-agent-command",
        default="",
        help=(
            "External coding-agent audit command. The crawler sends one Lean-file audit prompt on stdin "
            "and expects JSON on stdout. Example: --coding-agent-command 'codex exec --json'"
        ),
    )
    parser.add_argument(
        "--llm-command",
        dest="coding_agent_command",
        help="Alias for --coding-agent-command",
    )
    parser.add_argument(
        "--coding-agent-timeout",
        type=int,
        default=120,
        help="Per-file coding-agent audit timeout in seconds",
    )
    parser.add_argument(
        "--coding-agent-max-chars",
        type=int,
        default=60000,
        help="Maximum Lean source characters sent to the coding-agent per file",
    )
    parser.add_argument(
        "--coding-agent-limit",
        type=int,
        default=0,
        help="Limit coding-agent review to first N scanned files (0 = every scanned file)",
    )
    parser.add_argument(
        "--no-repo-wide-laundering-audit",
        action="store_true",
        help="Disable whole-root checks for uninstantiated law lockers and single-use bridges",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = normalize_user_path(args.root, ROOT)
    files = list(iter_lean_files(root))
    if args.limit > 0:
        files = files[: args.limit]

    coding_agent_config: CodingAgentAuditConfig | None = None
    if args.coding_agent_command:
        command = shlex.split(args.coding_agent_command)
        if not command:
            raise SystemExit("--coding-agent-command was provided but parsed to an empty command")
        coding_agent_config = CodingAgentAuditConfig(
            command=command,
            timeout_seconds=args.coding_agent_timeout,
            max_chars=args.coding_agent_max_chars,
        )

    reports: list[FileReport] = []
    total = len(files)
    for idx, path in enumerate(files, start=1):
        if args.print_progress:
            print(f"[closure-debt-crawler] {idx}/{total} {rel(path)}")
        file_coding_agent = coding_agent_config
        if (
            coding_agent_config is not None
            and args.coding_agent_limit > 0
            and idx > args.coding_agent_limit
        ):
            file_coding_agent = None
        reports.append(audit_file(path, coding_agent=file_coding_agent))
    if not args.no_repo_wide_laundering_audit:
        reports = apply_repo_wide_laundering_audit(files, reports)
    reports.sort(key=lambda r: r.path)

    payload = build_payload(
        root,
        reports,
        coding_agent_enabled=coding_agent_config is not None,
        coding_agent_command=coding_agent_config.command if coding_agent_config is not None else None,
    )

    json_out = normalize_user_path(args.json_out, ROOT / "reports" / "audit" / "closure-debt-crawler.json")
    md_out = normalize_user_path(args.md_out, ROOT / "reports" / "audit" / "closure-debt-crawler.md")

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(build_markdown(payload), encoding="utf-8")

    if args.print_summary:
        s = payload["summary"]
        print(
            f"[closure-debt-crawler] files={s['file_count']} findings={s['finding_count']} "
            f"hard={s['hard_count']} soft={s['soft_count']} advisory={s['advisory_count']}"
        )
        print(f"[closure-debt-crawler] json={json_out}")
        print(f"[closure-debt-crawler] md={md_out}")

    if not args.strict:
        return 0

    summary = payload["summary"]
    hard_failures = summary.get("provenance", {}).get("hard_failures", summary["hard_count"])
    return 1 if hard_failures > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
