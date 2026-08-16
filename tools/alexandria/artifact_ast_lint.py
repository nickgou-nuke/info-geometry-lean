#!/usr/bin/env python3
"""AST-aware artifact digest and lint pipeline for papers/textbooks.

This is the front door for raw mathematical artifacts.  It combines the
existing LaTeX/Markdown structural chunker with a conservative linter and
candidate-code validator:

* papers/textbooks are split at structural math boundaries;
* Lean/Python blocks embedded in the artifact are extracted as candidates;
* Python candidates are parsed with ``ast``;
* Lean candidates can optionally be checked with ``lake env lean``;
* suspicious proof-authority language is flagged rather than trusted;
* Qwen/local-LLM purification requests are emitted with the raw content intact.

The script is an ingestion and hygiene layer only.  The Lean parser, elaborator,
and kernel remain the authority for Lean semantics.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable


if __package__ in (None, ""):
    ROOT = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT))
else:
    ROOT = Path(__file__).resolve().parents[2]

from tools.alexandria.math_paper_graphrag_ingest import (  # noqa: E402
    infer_source_format,
    input_files_from_path,
    pdf_to_markdown,
    process_document,
    unique_ordered,
)
from tools.alexandria.schema import content_hash, source_uri, stable_key  # noqa: E402
from tools.pathing import normalize_user_path, repo_root  # noqa: E402


SCHEMA = "info_geometry.alexandria.artifact_ast_lint.v1"
AUTHORITY = "artifact_context_only_not_proof_authority"

SUPPORTED_SUFFIXES = {".tex", ".md", ".markdown", ".mmd", ".txt", ".pdf"}
CODE_FENCE_RE = re.compile(
    r"(?P<fence>`{3,}|~{3,})(?P<info>[^\n]*)\n(?P<body>.*?)(?:\n(?P=fence)|\Z)",
    re.DOTALL,
)
LATEX_CODE_ENV_RE = re.compile(
    r"\\begin\{(?P<env>minted|lstlisting|verbatim)\}"
    r"(?:\[[^\]]*\])?(?:\{(?P<lang>[^}]+)\})?"
    r"(?P<body>.*?)\\end\{(?P=env)\}",
    re.DOTALL,
)
LATEX_ENV_TOKEN_RE = re.compile(r"\\(?P<kind>begin|end)\{(?P<env>[A-Za-z*]+)\}")
LEAN_HINT_RE = re.compile(
    r"^\s*(?:import\s+|namespace\s+|open\s+|variable\s+|theorem\s+|lemma\s+|def\s+|"
    r"abbrev\s+|structure\s+|class\s+|inductive\s+|example\s*:)",
    re.MULTILINE,
)
PYTHON_HINT_RE = re.compile(
    r"^\s*(?:import\s+|from\s+\S+\s+import\s+|def\s+|class\s+|if\s+__name__\s*==)",
    re.MULTILINE,
)
LEAN_CODE_START_RE = re.compile(
    r"^\s*(?:@\[.*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:import|namespace|open|variable|section|theorem|lemma|def|abbrev|structure|class|"
    r"inductive|example|instance)\b"
    r"(?=.*(?::=|:|where| by\b|=>|→|↔|∀|Prop|Type|Sort|⦃|\{|\[))"
)
LEAN_CONTINUATION_RE = re.compile(
    r"^\s*(?:\||,|\.|<;>|·|by\b|where\b|exact\b|rw\b|simp\b|ring\b|rfl\b|"
    r"intro\b|intros\b|constructor\b|cases\b|apply\b|have\b|let\b|calc\b|"
    r"\{|\}|\(|\)|\[|\]|⟨|⟩|:=|=>|fun\b|λ\b)"
)
PYTHON_CODE_START_RE = re.compile(
    r"^\s*(?:>>>[ ]*)?(?:from\s+\S+\s+import\b|import\s+\S+|def\s+\w+|class\s+\w+|"
    r"if\s+__name__\s*==)"
)
PYTHON_CONTINUATION_RE = re.compile(
    r"^\s*(?:>>>|\.\.\.|return\b|yield\b|raise\b|if\b|elif\b|else:|for\b|while\b|with\b|"
    r"try:|except\b|finally:|[A-Za-z_][A-Za-z0-9_]*\s*=)"
)
AUTHORITY_CLAIM_RE = re.compile(
    r"\b("
    r"kernel[- ]verified|compiled\s+\d+\s+jobs|zero\s+sorr(?:y|ies)|zero\s+axioms|"
    r"axiom[- ]free|proved\s+in\s+lean|lean\s+verified|linter\s+is\s+silent|"
    r"formally\s+verified|machine[- ]checked|qed"
    r")\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Finding:
    key: str
    documentKey: str
    path: str
    severity: str
    code: str
    message: str
    lineStart: int | None
    lineEnd: int | None
    evidence: str
    metadata: dict[str, Any]


@dataclass(frozen=True)
class CodeCandidate:
    key: str
    documentKey: str
    path: str
    language: str
    sourceKind: str
    lineStart: int
    lineEnd: int
    text: str
    validationStatus: str
    validationMessage: str
    metadata: dict[str, Any]


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def line_starts(text: str) -> list[int]:
    starts = [0]
    for idx, char in enumerate(text):
        if char == "\n":
            starts.append(idx + 1)
    return starts


def line_offsets(text: str) -> list[tuple[int, int, str]]:
    out: list[tuple[int, int, str]] = []
    offset = 0
    for raw in text.splitlines(keepends=True):
        start = offset
        offset += len(raw)
        out.append((start, offset, raw.rstrip("\n\r")))
    if text and not text.endswith(("\n", "\r")) and not out:
        out.append((0, len(text), text))
    return out


def line_number(starts: list[int], offset: int) -> int:
    # Avoid importing bisect into hot call sites; artifacts are small enough.
    line = 1
    for idx, start in enumerate(starts, start=1):
        if start > offset:
            break
        line = idx
    return line


def infer_code_language(info: str, body: str, *, fallback: str = "unknown") -> str:
    lang = info.strip().split(maxsplit=1)[0].lower() if info.strip() else ""
    aliases = {
        "lean": "lean4",
        "lean4": "lean4",
        "lean3": "lean",
        "py": "python",
        "python": "python",
        "sympy": "python",
    }
    if lang in aliases:
        return aliases[lang]
    if LEAN_HINT_RE.search(body):
        return "lean4"
    if PYTHON_HINT_RE.search(body):
        return "python"
    return fallback


def unescaped_dollar_count(text: str, delimiter: str) -> int:
    count = 0
    idx = 0
    while True:
        pos = text.find(delimiter, idx)
        if pos < 0:
            return count
        if pos == 0 or text[pos - 1] != "\\":
            count += 1
        idx = pos + len(delimiter)


def finding(
    *,
    document_key: str,
    path: Path,
    severity: str,
    code: str,
    message: str,
    line_start: int | None,
    line_end: int | None,
    evidence: str,
    metadata: dict[str, Any] | None = None,
) -> Finding:
    return Finding(
        key=stable_key("afind", document_key, code, line_start, evidence[:128], message),
        documentKey=document_key,
        path=path.as_posix(),
        severity=severity,
        code=code,
        message=message,
        lineStart=line_start,
        lineEnd=line_end,
        evidence=evidence,
        metadata=metadata or {},
    )


def lint_latex_balance(path: Path, text: str, document_key: str) -> list[Finding]:
    starts = line_starts(text)
    stack: list[tuple[str, int]] = []
    findings: list[Finding] = []
    for match in LATEX_ENV_TOKEN_RE.finditer(text):
        kind = match.group("kind")
        env = match.group("env")
        line = line_number(starts, match.start())
        if kind == "begin":
            stack.append((env, line))
            continue
        if not stack:
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="error",
                    code="latex_unmatched_end",
                    message=f"Found \\end{{{env}}} without a matching begin.",
                    line_start=line,
                    line_end=line,
                    evidence=match.group(0),
                )
            )
            continue
        open_env, open_line = stack.pop()
        if open_env != env:
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="error",
                    code="latex_mismatched_environment",
                    message=f"Opened \\begin{{{open_env}}} but closed \\end{{{env}}}.",
                    line_start=open_line,
                    line_end=line,
                    evidence=f"begin={open_env}; end={env}",
                )
            )
    for env, line in stack:
        findings.append(
            finding(
                document_key=document_key,
                path=path,
                severity="error",
                code="latex_unclosed_environment",
                message=f"Found \\begin{{{env}}} without a matching end.",
                line_start=line,
                line_end=line,
                evidence=env,
            )
        )
    return findings


def lint_math_delimiters(path: Path, text: str, document_key: str) -> list[Finding]:
    findings: list[Finding] = []
    display_count = unescaped_dollar_count(text, "$$")
    if display_count % 2 != 0:
        findings.append(
            finding(
                document_key=document_key,
                path=path,
                severity="warning",
                code="math_unbalanced_display_dollars",
                message="Odd number of unescaped $$ display-math delimiters.",
                line_start=None,
                line_end=None,
                evidence=f"count={display_count}",
            )
        )
    text_without_display = re.sub(r"(?<!\\)\$\$.*?(?<!\\)\$\$", "", text, flags=re.DOTALL)
    inline_count = unescaped_dollar_count(text_without_display, "$")
    if inline_count % 2 != 0:
        findings.append(
            finding(
                document_key=document_key,
                path=path,
                severity="warning",
                code="math_unbalanced_inline_dollars",
                message="Odd number of unescaped $ inline-math delimiters.",
                line_start=None,
                line_end=None,
                evidence=f"count={inline_count}",
            )
        )
    return findings


def lint_authority_claims(path: Path, text: str, document_key: str) -> list[Finding]:
    starts = line_starts(text)
    findings: list[Finding] = []
    for match in AUTHORITY_CLAIM_RE.finditer(text):
        line = line_number(starts, match.start())
        findings.append(
            finding(
                document_key=document_key,
                path=path,
                severity="warning",
                code="authority_claim_requires_kernel_evidence",
                message="Artifact prose claims formal authority; require an explicit Lean theorem/build citation.",
                line_start=line,
                line_end=line,
                evidence=match.group(0),
            )
        )
    return findings


def lint_structural_rows(
    path: Path,
    rows: dict[str, list[dict[str, Any]]],
    *,
    max_chars: int,
) -> list[Finding]:
    findings: list[Finding] = []
    documents = rows.get("alexandria_documents", [])
    if not documents:
        return findings
    document_key = str(documents[0]["_key"])
    previous_kind = ""
    previous_line_end: int | None = None
    for chunk in rows.get("alexandria_chunks", []):
        text = str(chunk.get("text", ""))
        provenance = chunk.get("provenance") if isinstance(chunk.get("provenance"), dict) else {}
        line_start = provenance.get("lineStart")
        line_end = provenance.get("lineEnd")
        line_start_i = int(line_start) if isinstance(line_start, int) else None
        line_end_i = int(line_end) if isinstance(line_end, int) else None
        kind = str(chunk.get("chunkKind", ""))
        if len(text) > max_chars:
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="warning",
                    code="oversized_structural_chunk",
                    message="Structural chunk exceeds the configured max character budget.",
                    line_start=line_start_i,
                    line_end=line_end_i,
                    evidence=f"chars={len(text)} max={max_chars}",
                    metadata={"chunkKey": chunk.get("_key"), "chunkKind": kind},
                )
            )
        if kind == "proof" and previous_kind not in {"theorem", "theorem_with_proof"}:
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="info",
                    code="proof_without_immediate_theorem",
                    message="Proof block is not immediately preceded by a theorem-like block.",
                    line_start=line_start_i,
                    line_end=line_end_i,
                    evidence=f"previousKind={previous_kind or 'none'}",
                    metadata={"chunkKey": chunk.get("_key")},
                )
            )
        if previous_kind in {"theorem", "lemma", "proposition"} and kind != "proof":
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="info",
                    code="theorem_without_immediate_proof",
                    message="Theorem-like block is not immediately followed by a proof block.",
                    line_start=previous_line_end,
                    line_end=line_start_i,
                    evidence=f"nextKind={kind or 'none'}",
                )
            )
        previous_kind = kind
        previous_line_end = line_end_i
    return findings


def validate_python_candidate(text: str) -> tuple[str, str]:
    try:
        ast.parse(text)
    except SyntaxError as exc:
        return "failed", f"{exc.__class__.__name__}: {exc}"
    return "passed", "python ast.parse accepted candidate"


def validate_lean_candidate(
    text: str,
    *,
    preamble: str,
    timeout: int,
    cwd: Path,
) -> tuple[str, str]:
    with tempfile.TemporaryDirectory(prefix="artifact-lean-") as tmp:
        candidate = Path(tmp) / "Candidate.lean"
        body = (preamble.strip() + "\n\n" if preamble.strip() else "") + text
        candidate.write_text(body, encoding="utf-8")
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(candidate)],
                cwd=cwd,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return "failed", f"lake env lean timed out after {timeout}s"
        output = (proc.stdout + "\n" + proc.stderr).strip()
        if proc.returncode == 0:
            return "passed", "lake env lean accepted candidate"
        compact = re.sub(r"\s+", " ", output).strip()
        return "failed", compact[:800] if compact else f"lean exited with code {proc.returncode}"


def overlaps_any(start: int, end: int, spans: list[tuple[int, int]]) -> bool:
    return any(not (end <= span_start or start >= span_end) for span_start, span_end in spans)


def lean_specific_plaintext(line: str) -> bool:
    stripped = line.strip()
    if re.match(r"^(theorem|lemma|example|abbrev|structure|inductive|instance|namespace|open|"
                r"variable|section)\b", stripped):
        return True
    if any(token in stripped for token in [":=", "→", "↔", "∀", "⦃", "⟨", "⟩"]):
        return True
    if re.search(r"\b(Prop|Type|Sort|where| by)\b", stripped):
        return True
    # Lean declarations usually type the name/arguments before the body; Python
    # function/class headers normally end at the colon.
    if re.match(r"^(def|class)\b", stripped) and not stripped.endswith(":") and ":" in stripped:
        return True
    return False


def classify_plaintext_code_start(line: str) -> str:
    if PYTHON_CODE_START_RE.match(line) and not lean_specific_plaintext(line):
        return "python"
    if LEAN_CODE_START_RE.match(line):
        return "lean4"
    return ""


def plaintext_code_runs(text: str, occupied: list[tuple[int, int]]) -> list[tuple[str, int, int, str]]:
    """Recover conservative Lean/Python code runs from layout-extracted text.

    This is intentionally conservative.  It is meant for PDF text layers where
    code fences are gone, not for proving that a prose line is source code.
    """
    runs: list[tuple[str, int, int, str]] = []
    lines = line_offsets(text)
    idx = 0
    while idx < len(lines):
        start_off, end_off, line = lines[idx]
        if overlaps_any(start_off, end_off, occupied):
            idx += 1
            continue
        stripped = line.strip()
        language = classify_plaintext_code_start(line)
        if not language:
            idx += 1
            continue

        run_start = start_off
        run_end = end_off
        run_lines = [line]
        idx += 1
        blank_budget = 0
        while idx < len(lines):
            next_start, next_end, next_line = lines[idx]
            if overlaps_any(next_start, next_end, occupied):
                break
            next_stripped = next_line.strip()
            if not next_stripped:
                if blank_budget >= 1:
                    break
                blank_budget += 1
                run_lines.append(next_line)
                run_end = next_end
                idx += 1
                continue
            blank_budget = 0
            if language == "lean4":
                continues = bool(
                    classify_plaintext_code_start(next_line) == "lean4"
                    or LEAN_CONTINUATION_RE.match(next_line)
                    or (line[:1].isspace() and next_line[:1].isspace() and not next_stripped.endswith("."))
                )
            else:
                continues = bool(
                    classify_plaintext_code_start(next_line) == "python"
                    or PYTHON_CONTINUATION_RE.match(next_line)
                    or next_line.startswith((" ", "\t", ">>>", "..."))
                )
            if not continues:
                break
            run_lines.append(next_line)
            run_end = next_end
            idx += 1

        body = "\n".join(run_lines).strip()
        # Discard prose-like one-liners such as "theorem 8.1," that slipped through.
        if language == "lean4" and not re.search(r":=|:| by\b|=>|→|↔|∀|Prop|Type|Sort", body):
            continue
        if language == "python" and not re.search(r"\b(def|class|import|from|return)\b|>>>", body):
            continue
        runs.append((language, run_start, run_end, body))
    return runs


def extract_code_candidates(
    path: Path,
    text: str,
    document_key: str,
    *,
    check_lean: bool,
    lean_preamble: str,
    lean_timeout: int,
    check_python: bool,
) -> tuple[list[CodeCandidate], list[Finding]]:
    starts = line_starts(text)
    candidates: list[CodeCandidate] = []
    findings: list[Finding] = []
    occupied: list[tuple[int, int]] = []

    def add_candidate(language: str, source_kind: str, body: str, start: int, end: int) -> None:
        stripped = body.strip()
        if not stripped:
            return
        line_start = line_number(starts, start)
        line_end = line_number(starts, max(start, end - 1))
        status = "not_checked"
        message = "candidate extracted but not validated"
        if language == "python" and check_python:
            status, message = validate_python_candidate(stripped)
        elif language == "lean4" and check_lean:
            status, message = validate_lean_candidate(
                stripped,
                preamble=lean_preamble,
                timeout=lean_timeout,
                cwd=repo_root(),
            )
        key = stable_key("acode", document_key, language, source_kind, line_start, content_hash(stripped))
        candidates.append(
            CodeCandidate(
                key=key,
                documentKey=document_key,
                path=path.as_posix(),
                language=language,
                sourceKind=source_kind,
                lineStart=line_start,
                lineEnd=line_end,
                text=stripped,
                validationStatus=status,
                validationMessage=message,
                metadata={"authority": AUTHORITY},
            )
        )
        if language == "lean4" and not check_lean:
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="info",
                    code="lean_candidate_not_kernel_checked",
                    message="Lean-looking artifact block was extracted but not compiled.",
                    line_start=line_start,
                    line_end=line_end,
                    evidence=source_kind,
                    metadata={"candidateKey": key},
                )
            )
        elif status == "failed":
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="warning",
                    code=f"{language}_candidate_validation_failed",
                    message="Embedded code candidate failed validation.",
                    line_start=line_start,
                    line_end=line_end,
                    evidence=message[:400],
                    metadata={"candidateKey": key, "sourceKind": source_kind},
                )
            )

    for match in CODE_FENCE_RE.finditer(text):
        info = match.group("info")
        body = match.group("body")
        occupied.append((match.start(), match.end()))
        lang = infer_code_language(info, body)
        if lang in {"lean4", "python"}:
            add_candidate(lang, "markdown_code_fence", body, match.start("body"), match.end("body"))

    for match in LATEX_CODE_ENV_RE.finditer(text):
        env = match.group("env")
        occupied.append((match.start(), match.end()))
        lang = infer_code_language(match.group("lang") or "", match.group("body"))
        if lang in {"lean4", "python"}:
            add_candidate(lang, f"latex_{env}", match.group("body"), match.start("body"), match.end("body"))

    for lang, start, end, body in plaintext_code_runs(text, occupied):
        add_candidate(lang, "plaintext_layout_code_run", body, start, end)

    for candidate in candidates:
        if candidate.language == "lean4" and re.search(r"\b(sorry|admit)\b", candidate.text):
            findings.append(
                finding(
                    document_key=document_key,
                    path=path,
                    severity="info",
                    code="lean_candidate_contains_placeholder",
                    message="Lean candidate contains `sorry` or `admit`; treat it as illustrative or open code.",
                    line_start=candidate.lineStart,
                    line_end=candidate.lineEnd,
                    evidence="sorry/admit",
                    metadata={"candidateKey": candidate.key},
                )
            )

    return candidates, findings


def purification_request(chunk: dict[str, Any], findings: list[Finding]) -> dict[str, Any]:
    chunk_key = str(chunk["_key"])
    relevant = [
        {
            "severity": finding.severity,
            "code": finding.code,
            "message": finding.message,
            "lineStart": finding.lineStart,
            "lineEnd": finding.lineEnd,
        }
        for finding in findings
        if finding.metadata.get("chunkKey") == chunk_key
    ][:8]
    raw = str(chunk.get("text", ""))
    return {
        "_key": stable_key("apurify", chunk_key),
        "schema": f"{SCHEMA}.purification_request",
        "chunkKey": chunk_key,
        "systemPrompt": (
            "You are a mathematical artifact purification agent. Produce retrieval metadata only. "
            "Do not rewrite the source, do not claim Lean proof authority, and keep raw content intact."
        ),
        "userPrompt": (
            "Analyze this paper/textbook artifact chunk. Output JSON with keys: "
            "summary, assumed_definitions, mathematical_entities, candidate_formalizations, "
            "claims_requiring_evidence, normalized_notation, lint_awareness, "
            "raw_content_unchanged. Set raw_content_unchanged=true only if you preserve the raw text.\n\n"
            f"Chunk kind: {chunk.get('chunkKind')}\n"
            f"Title: {chunk.get('title')}\n"
            f"Lint findings for this chunk: {canonical_json(relevant)}\n\n"
            f"Raw content:\n{raw}"
        ),
        "expectedAuthority": AUTHORITY,
        "rawContent": raw,
    }


def prepare_inputs(args: argparse.Namespace) -> list[Path]:
    root = repo_root()
    input_paths: list[Path] = []
    for raw in args.input:
        path = normalize_user_path(raw, root)
        input_paths.extend(input_files_from_path(path))
    if not input_paths:
        raise SystemExit("no input artifacts supplied")
    docs: list[Path] = []
    pdf_work = normalize_user_path(str(args.pdf_work_dir), root)
    for path in input_paths:
        if path.suffix.lower() == ".pdf":
            docs.append(pdf_to_markdown(path, args.pdf_parser, pdf_work / path.stem))
        elif path.suffix.lower() in SUPPORTED_SUFFIXES:
            docs.append(path)
    unique = [Path(item) for item in unique_ordered(str(path) for path in docs)]
    if args.max_docs > 0:
        return unique[: args.max_docs]
    return unique


def process_artifact(path: Path, args: argparse.Namespace) -> dict[str, list[dict[str, Any]]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    rows = process_document(
        path,
        source_format=args.source_format,
        max_chars=max(512, int(args.max_chars)),
        bind_proofs=not args.no_bind_proofs,
    )
    document_key = str(rows["alexandria_documents"][0]["_key"])
    findings = []
    findings.extend(lint_latex_balance(path, text, document_key))
    findings.extend(lint_math_delimiters(path, text, document_key))
    findings.extend(lint_authority_claims(path, text, document_key))
    findings.extend(lint_structural_rows(path, rows, max_chars=max(512, int(args.max_chars))))
    code_candidates, code_findings = extract_code_candidates(
        path,
        text,
        document_key,
        check_lean=args.check_lean_candidates,
        lean_preamble=args.lean_preamble,
        lean_timeout=max(1, int(args.lean_timeout)),
        check_python=not args.no_check_python_candidates,
    )
    findings.extend(code_findings)
    fmt = infer_source_format(path, text, args.source_format)
    digest_row = {
        "_key": stable_key("adigest", path.resolve(), content_hash(text)),
        "schema": SCHEMA,
        "documentKey": document_key,
        "path": path.as_posix(),
        "sourceUri": source_uri(path),
        "sourceFormat": fmt,
        "contentHash": content_hash(text),
        "authority": AUTHORITY,
        "counts": {
            "chunks": len(rows.get("alexandria_chunks", [])),
            "findings": len(findings),
            "codeCandidates": len(code_candidates),
        },
    }
    rows["artifact_digests"] = [digest_row]
    rows["artifact_lint_findings"] = [asdict(item) for item in findings]
    rows["artifact_code_candidates"] = [asdict(item) for item in code_candidates]
    rows["artifact_purification_requests"] = [
        purification_request(chunk, findings) for chunk in rows.get("alexandria_chunks", [])
    ]
    return rows


def merge_rows(target: dict[str, list[dict[str, Any]]], source: dict[str, list[dict[str, Any]]]) -> None:
    for key, values in source.items():
        target.setdefault(key, []).extend(values)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", action="append", default=[], help="Input artifact file or directory. Repeatable.")
    parser.add_argument("--output", type=Path, required=True, help="Output directory for JSONL artifacts.")
    parser.add_argument("--source-format", choices=["auto", "latex", "markdown"], default="auto")
    parser.add_argument("--pdf-parser", choices=["none", "marker", "nougat"], default="none")
    parser.add_argument("--pdf-work-dir", type=Path, default=Path("artifacts/alexandria/artifact_pdf_markdown"))
    parser.add_argument("--max-chars", type=int, default=3600)
    parser.add_argument("--max-docs", type=int, default=0)
    parser.add_argument("--no-bind-proofs", action="store_true")
    parser.add_argument("--check-lean-candidates", action="store_true")
    parser.add_argument("--lean-preamble", default="", help="Optional preamble prepended before Lean candidate checks.")
    parser.add_argument("--lean-timeout", type=int, default=30)
    parser.add_argument("--no-check-python-candidates", action="store_true")
    parser.add_argument("--fail-on", choices=["none", "warning", "error"], default="none")
    return parser.parse_args()


def should_fail(findings: list[dict[str, Any]], fail_on: str) -> bool:
    if fail_on == "none":
        return False
    severities = {str(row.get("severity")) for row in findings}
    if fail_on == "warning":
        return bool(severities & {"warning", "error"})
    return "error" in severities


def main() -> int:
    args = parse_args()
    output = normalize_user_path(str(args.output), repo_root())
    all_rows: dict[str, list[dict[str, Any]]] = {
        "alexandria_documents": [],
        "alexandria_sections": [],
        "alexandria_chunks": [],
        "alexandria_entities": [],
        "alexandria_document_section_edges": [],
        "alexandria_section_chunk_edges": [],
        "alexandria_chunk_entity_edges": [],
        "alexandria_chunk_adjacent_edges": [],
        "alexandria_entity_relation_edges": [],
        "math_llm_requests": [],
        "artifact_digests": [],
        "artifact_lint_findings": [],
        "artifact_code_candidates": [],
        "artifact_purification_requests": [],
    }
    inputs = prepare_inputs(args)
    for path in inputs:
        merge_rows(all_rows, process_artifact(path, args))

    counts = {collection: write_jsonl(output / f"{collection}.jsonl", rows) for collection, rows in all_rows.items()}
    manifest = {
        "schema": f"{SCHEMA}.manifest",
        "inputs": [path.as_posix() for path in inputs],
        "output": output.as_posix(),
        "counts": counts,
        "authority": AUTHORITY,
        "chunking": {
            "paperStructuralChunker": "math_paper_graphrag_ingest.structural_latex_v1",
            "embeddedCodeValidation": {
                "pythonAstParse": not args.no_check_python_candidates,
                "leanLakeEnvLean": args.check_lean_candidates,
            },
            "maxChars": max(512, int(args.max_chars)),
        },
    }
    (output / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "[artifact-ast-lint] "
        f"documents={counts.get('alexandria_documents', 0)} "
        f"chunks={counts.get('alexandria_chunks', 0)} "
        f"findings={counts.get('artifact_lint_findings', 0)} "
        f"codeCandidates={counts.get('artifact_code_candidates', 0)} "
        f"output={output}"
    )
    if should_fail(all_rows["artifact_lint_findings"], args.fail_on):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
