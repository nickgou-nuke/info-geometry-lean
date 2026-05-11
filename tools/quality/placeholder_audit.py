#!/usr/bin/env python3
from __future__ import annotations

"""Lean placeholder/trust audit for temporary proof shortcuts and external assumptions."""

import argparse
import json
import re
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
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

DECL_HEADER_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:partial\s+)?(?:opaque\s+)?"
    r"(?:private\s+|protected\s+|local\s+)?"
    r"(theorem|lemma|example|def|abbrev|structure|class|instance|axiom|inductive|postulate)\b"
    r"\s+([A-Za-z0-9_'.]+)",
    re.M,
)

# declaration-level and file-level placeholder discovery for high-signal trust debt
PLACEHOLDER_NAME_RE = re.compile(r"^(?:external|hyp|unproven|todo|stub|bridge)_[A-Za-z0-9_']*", re.I)
OPAQUE_DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+|local\s+)?opaque\b", re.M)
VAR_ASSUME_RE = re.compile(r"^\s*variable\s*\([^\n]*:[^\n]*\)\s*$", re.M)
WITNESS_FIELD_RE = re.compile(r"(?m)^\s*([A-Za-z0-9_']+_valid)\s*:\s*([A-Za-z0-9_'.]+)\s*$")
UNIVERSAL_TRUE_FIELD_RE = re.compile(r"(?m)^\s*[A-Za-z0-9_']+\s*:\s*∀\s+[^\n]*,\s*True\s*$")

# core placeholders that indicate trust debt in source form
HOLE_TOKEN_RE = re.compile(r"\b(?:sorry|admit|sorryAx|admitAx)\b")
POSTULATE_RE = re.compile(r"^\s*postulate\b")

TRIVIAL_BODY_LINES = (
    "rfl",
    "trivial",
    "simp",
    "simpa",
    "aesop",
    "linarith",
    "omega",
    "ring",
    "ring_nf",
    "simp_all",
    "tauto",
    "decide",
    "exact rfl",
    "exact trivial",
    "exact True.intro",
)
TRIVIAL_LINE_RE = re.compile(
    r"^(?:(?P<by>by)\s*)?(?:(?:exact\s+)?(?:"
    + "|".join(re.escape(tok) for tok in TRIVIAL_BODY_LINES)
    + r")|constructor|intro|simp\\?|aesop!?|by)\b"
)


@dataclass(frozen=True)
class TrustFinding:
    file: str
    module: str
    line: int
    declaration_kind: str
    declaration_name: str
    finding: str
    severity: str  # hard | soft
    detail: str
    snippet: str


@dataclass(frozen=True)
class AuditSignal:
    signal: str
    decl_ref: str
    file: str
    line: int
    module: str
    declaration_name: str
    declaration_kind: str
    finding: str
    severity: str
    task_hint: str
    recommendation: str
    detail: str
    snippet: str


def to_decl_ref(module: str, declaration_name: str) -> str:
    name = declaration_name.strip()
    mod = module.strip()
    if not mod:
        return name
    return name if name.startswith(f"{mod}.") else f"{mod}.{name}"


def signal_for_finding(finding: TrustFinding) -> list[AuditSignal]:
    decl_ref = to_decl_ref(finding.module, finding.declaration_name)
    evidence = f"{finding.file}:{finding.line} {finding.declaration_kind} {finding.declaration_name}"

    if finding.severity == "hard":
        return [
            AuditSignal(
                signal="leanstral.autoproof.frontier",
                decl_ref=decl_ref,
                file=finding.file,
                line=finding.line,
                module=finding.module,
                declaration_name=finding.declaration_name,
                declaration_kind=finding.declaration_kind,
                finding=finding.finding,
                severity=finding.severity,
                task_hint="leanstral.autoproof",
                recommendation=(
                    "Run Leanstral proposal/autoproof task for this declaration and replace the placeholder with an explicit proof."
                ),
                detail=(
                    "High-risk placeholder requires active repair loop: hard placeholder blocks are not allowed in promoted artifacts."
                ),
                snippet=finding.snippet,
            ),
            AuditSignal(
                signal="closure.debt.extend",
                decl_ref=decl_ref,
                file=finding.file,
                line=finding.line,
                module=finding.module,
                declaration_name=finding.declaration_name,
                declaration_kind=finding.declaration_kind,
                finding=finding.finding,
                severity=finding.severity,
                task_hint="closure.debt.extend",
                recommendation="Track this declaration as open closure debt until a verified proof bridge is in place.",
                detail="Placeholder contributes to unresolved theorem-closure debt and should be part of the debt extension plan.",
                snippet=finding.snippet,
            ),
        ]

    # soft findings are still debt but not immediate frontier blockers.
    return [
        AuditSignal(
            signal="closure.debt.extend",
            decl_ref=decl_ref,
            file=finding.file,
            line=finding.line,
            module=finding.module,
            declaration_name=finding.declaration_name,
            declaration_kind=finding.declaration_kind,
            finding=finding.finding,
            severity=finding.severity,
            task_hint="closure.debt.extend",
            recommendation="Refine this low-risk placeholder into a structured proof while keeping the declaration in debt tracking.",
            detail="Soft placeholder debt extends closure debt until replaced by stronger proof infrastructure.",
            snippet=finding.snippet,
        )
    ]


def build_signal_payload(
    findings: list[TrustFinding],
    *,
    root: Path,
) -> dict[str, Any]:
    signals: list[AuditSignal] = []
    for finding in findings:
        signals.extend(signal_for_finding(finding))

    signals = sorted(
        signals,
        key=lambda item: (item.signal, item.module, item.decl_ref, item.line, item.finding),
    )

    return {
        "schema": "info_geometry.placeholder_audit_signals.v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source": {
            "schema": "info_geometry.placeholder_audit.v1",
            "root": rel(root),
        },
        "summary": {
            "signal_count": len(signals),
            "autoproof_signal_count": len([x for x in signals if x.signal == "leanstral.autoproof.frontier"]),
            "closure_debt_signal_count": len([x for x in signals if x.signal == "closure.debt.extend"]),
            "finding_count": len(findings),
        },
        "signals": [asdict(item) for item in signals],
    }


@dataclass(frozen=True)
class ModuleAudit:
    path: str
    module: str
    finding_count: int
    hard_count: int
    soft_count: int
    findings: list[TrustFinding]


def rel(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def module_name(path: Path, root: Path | None = None) -> str:
    try:
        if root is None:
            root = ROOT / "lean"
        rel_path = path.relative_to(root).with_suffix("").as_posix()
        return rel_path.replace("/", ".")
    except ValueError:
        try:
            rel_path = path.relative_to(ROOT).with_suffix("").as_posix()
            return rel_path.replace("/", ".")
        except ValueError:
            return path.stem


def strip_comments(text: str) -> str:
    return audit_constructivity.strip_comments(text, strip_strings=True, strip_quoted_identifiers=True)


def looks_skeletal_proof(proof: str) -> bool:
    proof = proof.strip()
    if not proof:
        return False
    # single-line and small block checks are used to keep false positives low.
    lines = [ln.strip() for ln in proof.splitlines() if ln.strip()]
    if not lines:
        return False

    if len(lines) > 8:
        return False

    # tolerate either:
    # - by tactic
    # - immediate `by`-terminated skeleton
    # - nested branch lines
    normalized: list[str] = []
    first = lines[0]
    if first == "by":
        normalized = lines[1:]
    elif first.startswith("by "):
        normalized = [first[3:].strip()] + lines[1:]
    else:
        normalized = lines

    for ln in normalized:
        if ln in {"|", ":=", ","}:
            continue
        if ln.startswith("|"):
            continue
        if ln.startswith("case "):
            continue
        if ln.startswith("rename_i") or ln.startswith("aesop?"):
            continue
        if TRIVIAL_LINE_RE.match(ln):
            continue
        # allow exact one-liners like `by omega`
        if ln in TRIVIAL_BODY_LINES:
            continue
        return False
    return True


def _llm_scan_file(
    path: Path,
    *,
    endpoint: str,
    model: str,
    timeout: int,
    max_tokens: int,
    max_chars: int,
    retries: int,
) -> list[TrustFinding]:
    """Run the optional LLM closure-debt pass for this file.

    Any import/runtime errors are surfaced as soft findings so deterministic scans
    still remain usable when LLM is unavailable.
    """

    if not endpoint:
        return []

    try:
        # Import lazily to avoid heavy import cycles and make this opt-in.
        from tools.quality import llm_closure_debt_auditor

        file_audit = llm_closure_debt_auditor.audit_file(
            path,
            base_url=endpoint,
            model=model,
            timeout=timeout,
            max_tokens=max_tokens,
            max_chars=max_chars,
            retries=retries,
        )
    except Exception as ex:  # noqa: BLE001
        return [
            TrustFinding(
                file=rel(path),
                module=module_name(path),
                line=1,
                declaration_kind="file",
                declaration_name="llm-audit",
                finding="llm-audit-failure",
                severity="soft",
                detail=f"LLM audit failed: {ex}",
                snippet=source_excerpt(path.read_text(encoding="utf-8").splitlines(), 1),
            )
        ]

    out: list[TrustFinding] = []
    lines = path.read_text(encoding="utf-8").splitlines()
    for item in file_audit.findings:
        out.append(
            TrustFinding(
                file=rel(path),
                module=module_name(path),
                line=int(item.line_start),
                declaration_kind="file",
                declaration_name="llm-declaration",
                finding=f"llm-{item.category}",
                severity="hard" if item.severity == "hard" else "soft",
                detail=f"{item.why}; fix: {item.fix_strategy}".strip("; "),
                snippet=source_excerpt(lines, int(item.line_start)),
            )
        )
    return out


def _scan_file_level_findings(path: Path, clean: str) -> list[TrustFinding]:
    lines = clean.splitlines()
    findings: list[TrustFinding] = []

    def emit(
        line: int,
        declaration_kind: str,
        declaration_name: str,
        finding: str,
        severity: str,
        detail: str,
    ) -> None:
        findings.append(
            TrustFinding(
                file=rel(path),
                module=module_name(path),
                line=line,
                declaration_kind=declaration_kind,
                declaration_name=declaration_name,
                finding=finding,
                severity=severity,
                detail=detail,
                snippet=source_excerpt(lines, line),
            )
        )

    # top-level axioms and postulates are hard trust debt
    for m in re.finditer(r"^\s*axiom\b", clean, re.M):
        emit(audit_constructivity.line_of(clean, m.start()), "file", "<file-level>", "explicit-placeholder-declaration", "hard", "top-level axiom declaration")
    for m in re.finditer(r"^\s*postulate\b", clean, re.M):
        emit(audit_constructivity.line_of(clean, m.start()), "file", "<file-level>", "explicit-placeholder-declaration", "hard", "top-level postulate declaration")

    # file-level behaviors that are likely temporary placeholders and should be tracked
    for m in OPAQUE_DECL_RE.finditer(clean):
        emit(audit_constructivity.line_of(clean, m.start()), "opaque", "<file-level>", "opaque-stub", "soft", "opaque declaration without explicit proof obligations in this scan")
    for m in VAR_ASSUME_RE.finditer(clean):
        emit(audit_constructivity.line_of(clean, m.start()), "variable", "<file-level>", "injected-hypothesis-surface", "soft", "section variable assumptions detected")
    for m in WITNESS_FIELD_RE.finditer(clean):
        emit(audit_constructivity.line_of(clean, m.start()), "structure-field", m.group(1), "witness-field-projection", "soft", f"witness field `{m.group(1)} : {m.group(2)}`")
    for m in UNIVERSAL_TRUE_FIELD_RE.finditer(clean):
        emit(audit_constructivity.line_of(clean, m.start()), "structure-field", "<forall-true>", "placeholder-law", "soft", "field with ∀ ... -> True detected")

    # Deduplicate on exact keys.
    dedup: dict[tuple[str, int, str], TrustFinding] = {}
    for item in findings:
        dedup[(item.finding, item.line, item.declaration_name)] = item
    return list(dedup.values())


def is_vacuous_true_false(body: str) -> bool:
    compact = re.sub(r"\s+", " ", body.strip())
    if compact in {"True", "False", "by trivial", "by decide", "by exact True.intro", "by exact False.elim"}:
        return True
    if compact.startswith("by exact "):
        exact_term = compact.removeprefix("by exact ").strip()
        return exact_term in {"True.intro", "False.elim"}
    return bool(
        compact.startswith("by")
        and compact in {"by rfl", "by simp", "by decide", "by aesop", "by trivial"}
    )


def block_body(block: str) -> str:
    idx = block.find(":=")
    if idx < 0:
        return ""
    return block[idx + 2 :].strip()


def source_excerpt(lines: list[str], line: int, radius: int = 2) -> str:
    start = max(1, line - radius)
    end = min(len(lines), line + radius)
    out = []
    for idx in range(start, end + 1):
        out.append(f"{idx}: {lines[idx - 1].rstrip()}")
    return "\n".join(out)


def classify_declaration(
    kind: str,
    name: str,
    line: int,
    block: str,
    file_lines: list[str],
    path: Path,
) -> list[TrustFinding]:
    findings: list[TrustFinding] = []
    clean = block

    if kind in {"axiom", "postulate"}:
        findings.append(
            TrustFinding(
                file=rel(path),
                module=module_name(path),
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                finding="explicit-placeholder-declaration",
                severity="hard",
                detail=f"{kind} declaration: global trust assumption introduced",
                snippet=source_excerpt(file_lines, line),
            )
        )

    if HOLE_TOKEN_RE.search(clean):
        findings.append(
            TrustFinding(
                file=rel(path),
                module=module_name(path),
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                finding="proof-hole",
                severity="hard",
                detail="declaration body contains sorry/admit placeholder",
                snippet=source_excerpt(file_lines, line),
            )
        )
        # already highest-priority; still continue for additional tagging.

    proof = block_body(clean)
    if kind in {"theorem", "lemma", "example"}:
        if proof and is_vacuous_true_false(proof):
            findings.append(
                TrustFinding(
                    file=rel(path),
                    module=module_name(path),
                    line=line,
                    declaration_kind=kind,
                    declaration_name=name,
                    finding="vacuous-prop-constant",
                    severity="soft",
                    detail="theorem/lemma is closed by an uninformative constant",
                    snippet=source_excerpt(file_lines, line),
                )
            )
        elif proof and looks_skeletal_proof(proof):
            findings.append(
                TrustFinding(
                    file=rel(path),
                    module=module_name(path),
                    line=line,
                    declaration_kind=kind,
                    declaration_name=name,
                    finding="skeletal-proof",
                    severity="soft",
                    detail="proof appears to be tactic-automation-only or skeletal",
                    snippet=source_excerpt(file_lines, line),
                )
            )

    if POSTULATE_RE.search(clean) and kind != "postulate":
        findings.append(
            TrustFinding(
                file=rel(path),
                module=module_name(path),
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                finding="postulate-usage",
                severity="hard",
                detail="postulate token found in declaration body",
                snippet=source_excerpt(file_lines, line),
            )
            )

    if PLACEHOLDER_NAME_RE.match(name):
        findings.append(
            TrustFinding(
                file=rel(path),
                module=module_name(path),
                line=line,
                declaration_kind=kind,
                declaration_name=name,
                finding="placeholder-naming",
                severity="soft",
                detail="declaration name is marked as placeholder/bridge/hypothesis surface",
                snippet=source_excerpt(file_lines, line),
            )
        )

    # Avoid duplicate identical findings if multiple patterns overlap.
    deduped: list[TrustFinding] = []
    seen: set[tuple[str, str, int, str]] = set()
    for finding in findings:
        key = (
            finding.file,
            finding.declaration_name,
            finding.line,
            finding.finding,
        )
        if key in seen:
            continue
        seen.add(key)
        deduped.append(finding)
    return deduped


def scan_lean_file(path: Path) -> list[TrustFinding]:
    if not path.is_file():
        return []
    text = path.read_text(encoding="utf-8")
    clean = strip_comments(text)
    lines = clean.splitlines()
    findings: list[TrustFinding] = []
    headers = list(DECL_HEADER_RE.finditer(clean))
    if not headers:
        return []

    for idx, header in enumerate(headers):
        kind = header.group(1)
        name = header.group(2)
        start = header.start()
        line_no = audit_constructivity.line_of(clean, start)
        end = headers[idx + 1].start() if idx + 1 < len(headers) else len(clean)
        block = clean[start:end]
        findings.extend(classify_declaration(kind, name, line_no, block, lines, path))

    return findings


def iter_lean_files(root: Path) -> list[Path]:
    if root.is_file():
        return [root] if root.suffix == ".lean" else []
    files = sorted(
        path
        for path in root.rglob("*.lean")
        if path.is_file()
        and ".lake" not in path.parts
        and ".lake-packages" not in path.parts
    )
    return files


def run_audit(
    root: Path,
    *,
    scan_unstable: bool = True,
    scan_archive: bool = True,
    llm_endpoint: str | None = None,
    llm_model: str = "leanstral-gguf",
    llm_timeout: int = 120,
    llm_max_tokens: int = 900,
    llm_max_chars: int = 12000,
    llm_retries: int = 2,
) -> tuple[list[ModuleAudit], list[TrustFinding], list[str]]:
    root = root.resolve()
    files = iter_lean_files(root)
    findings_by_file: dict[Path, list[TrustFinding]] = {}
    scanned: list[str] = []

    def _in_skip_segment(path: Path, segment: str) -> bool:
        try:
            rel_path = path.relative_to(root)
        except ValueError:
            rel_path = path.relative_to(ROOT)
        return segment in rel_path.parts

    for path in files:
        if not scan_unstable and _in_skip_segment(path, "Unstable"):
            continue
        if not scan_archive and _in_skip_segment(path, "Archive"):
            continue
        scanned.append(rel(path))
        f = scan_lean_file(path)
        f.extend(_scan_file_level_findings(path, strip_comments(path.read_text(encoding="utf-8"))))
        if llm_endpoint:
            f.extend(
                _llm_scan_file(
                    path,
                    endpoint=llm_endpoint,
                    model=llm_model,
                    timeout=llm_timeout,
                    max_tokens=llm_max_tokens,
                    max_chars=llm_max_chars,
                    retries=llm_retries,
                )
            )
        if f:
            findings_by_file[path] = f

    all_findings: list[TrustFinding] = []
    modules: list[ModuleAudit] = []
    for path in sorted(findings_by_file):
        file_findings = findings_by_file[path]
        all_findings.extend(file_findings)
        counts = Counter(item.severity for item in file_findings)
        modules.append(
            ModuleAudit(
                path=rel(path),
                module=module_name(path),
                finding_count=len(file_findings),
                hard_count=counts.get("hard", 0),
                soft_count=counts.get("soft", 0),
                findings=file_findings,
            )
        )

    return modules, all_findings, scanned


def build_json(
    modules: list[ModuleAudit],
    *,
    root: Path,
    scanned_count: int,
) -> dict[str, object]:
    hard_count = sum(mod.hard_count for mod in modules)
    soft_count = sum(mod.soft_count for mod in modules)
    return {
        "schema": "info_geometry.placeholder_audit.v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": rel(root),
        "summary": {
            "module_count": len(modules),
            "scanned_count": scanned_count,
            "finding_count": hard_count + soft_count,
            "hard_count": hard_count,
            "soft_count": soft_count,
        },
        "modules": [
            {
                **asdict(mod),
                "findings": [asdict(item) for item in mod.findings],
            }
            for mod in modules
        ],
    }


def build_md(modules: list[ModuleAudit], *, scanned_count: int) -> str:
    hard_count = sum(mod.hard_count for mod in modules)
    soft_count = sum(mod.soft_count for mod in modules)
    lines: list[str] = []
    lines.append("# Lean Placeholder Trust Audit")
    lines.append("")
    lines.append(f"Generated: `{datetime.now(timezone.utc).isoformat()}`")
    lines.append("")
    lines.append(f"- Modules scanned: **{scanned_count}**")
    lines.append(f"- Modules with findings: **{len(modules)}**")
    lines.append(f"- Total findings: **{hard_count + soft_count}** (hard={hard_count}, soft={soft_count})")
    lines.append("")

    if not modules:
        lines.append("No placeholder-trust findings detected.")
        return "\n".join(lines) + "\n"

    for module in modules:
        lines.append(f"## `{module.module}`")
        lines.append(f"- path: `{module.path}`")
        lines.append(
            f"- findings: {module.finding_count} (hard={module.hard_count}, soft={module.soft_count})"
        )
        lines.append("")
        for item in module.findings:
            lines.append(
                f"- L{item.line}: **{item.severity.upper()}** `{item.finding}` in `{item.declaration_kind} {item.declaration_name}`"
            )
            lines.append(f"  - {item.detail}")
            lines.append(f"  - `{item.snippet.splitlines()[0] if item.snippet else ''}`")
        lines.append("")

    return "\n".join(lines) + "\n"


def format_text(modules: list[ModuleAudit], scanned_count: int) -> str:
    return build_md(modules, scanned_count=scanned_count)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Audit Lean modules for temporary-trust placeholders (axiom/postulate/sorry) and report them."
        )
    )
    parser.add_argument("--root", default="lean/InfoGeometry", help="Directory or file to scan")
    parser.add_argument("--json-out", default=None, help="Write JSON report to this path")
    parser.add_argument("--signals-out", default=None, help="Write placeholder trust signal JSON report to this path")
    parser.add_argument("--md-out", default=None, help="Write Markdown report to this path")
    parser.add_argument("--format", choices=["text", "json"], default="text")
    parser.add_argument("--include-unstable", action="store_true", help="Also scan InfoGeometry.Unstable")
    parser.add_argument("--include-archive", action="store_true", help="Also scan InfoGeometry.Archive")
    parser.add_argument("--strict", action="store_true", help="Fail on any hard finding")
    parser.add_argument("--llm-endpoint", default=None, help="Optional LLM endpoint (OpenAI-compatible) for second-pass advisory findings")
    parser.add_argument("--llm-model", default="leanstral-gguf", help="Model id for optional LLM pass")
    parser.add_argument("--llm-timeout", type=int, default=120, help="Timeout seconds for LLM calls")
    parser.add_argument("--llm-max-tokens", type=int, default=900, help="Max tokens for LLM calls")
    parser.add_argument("--llm-max-chars", type=int, default=12000, help="Max chars sent per LLM excerpt")
    parser.add_argument("--llm-retries", type=int, default=2, help="LLM retry count")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = ROOT / args.root if not Path(args.root).is_absolute() else Path(args.root)
    modules, findings, scanned = run_audit(
        root,
        scan_unstable=args.include_unstable,
        scan_archive=args.include_archive,
        llm_endpoint=args.llm_endpoint,
        llm_model=args.llm_model,
        llm_timeout=args.llm_timeout,
        llm_max_tokens=args.llm_max_tokens,
        llm_max_chars=args.llm_max_chars,
        llm_retries=args.llm_retries,
    )

    json_payload = build_json(modules, root=root, scanned_count=len(scanned))
    signal_payload = build_signal_payload(findings, root=root)

    if args.format == "json":
        print(json.dumps(json_payload, indent=2))
    else:
        print(format_text(modules, scanned_count=len(scanned)))

    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(json_payload, indent=2), encoding="utf-8")
    if args.md_out:
        out = Path(args.md_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(build_md(modules, scanned_count=len(scanned)), encoding="utf-8")
    if args.signals_out:
        out = Path(args.signals_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(signal_payload, indent=2), encoding="utf-8")

    if not args.strict:
        return 0
    return 1 if any(item.severity == "hard" for item in findings) else 0


if __name__ == "__main__":
    raise SystemExit(main())
