#!/usr/bin/env python3
"""
Universal structural chunker for mathematical ingestion.

This tool is intentionally conservative:
- Python chunks use the standard-library AST.
- Lean chunks use deterministic top-level command splitting, not tree-sitter as
  proof authority. A future backend can replace this with Lean AstExport JSON.
- Markdown chunks keep headings, fenced code, and math blocks intact.

The optional Qwen purification pass enriches chunks. It never certifies them.
Lean builds remain the authority for Lean truth.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.json_io import write_jsonl

try:
    from openai import OpenAI
except ImportError:  # pragma: no cover - depends on local environment
    OpenAI = None


SYSTEM_PROMPT = """You are a mathematical code indexer.
Analyze the provided Lean/Python/Markdown fragment without changing its raw content.
Return strict JSON with keys:
  "semantic_summary": one concise sentence,
  "extracted_formulas": array of formulas, theorem names, or API names,
  "domain_entities": array of mathematical/code entities.
Do not claim a theorem is proved unless the fragment itself is a compiled proof artifact.
"""

LEAN_COMMAND_START = re.compile(
    r"^\s*(?:"
    r"import|namespace|end|section|noncomputable\s+section|variable|variables|"
    r"universe|open|local|attribute|set_option|"
    r"def|theorem|lemma|example|abbrev|opaque|axiom|constant|"
    r"inductive|structure|class|instance|mutual|where|"
    r"notation|infix|syntax|macro|elab|declare_syntax_cat|"
    r"@[A-Za-z_]|/-!"
    r")\b"
)
LEAN_ATTACH_TO_NEXT_PREFIXES = ("/--", "/-!", "@[")
LEAN_DECL_NAME = re.compile(
    r"^\s*(?:@[^\n]*\s*)*(?:def|theorem|lemma|abbrev|opaque|axiom|constant|"
    r"inductive|structure|class|instance)\s+([A-Za-z0-9_'.]+)"
)
PY_IMPORT_OR_ASSIGN = (ast.Import, ast.ImportFrom, ast.Assign, ast.AnnAssign)
DEBT_RE = re.compile(
    r"\b(?:open debt|closure debt|remaining debt|fake debt|todo|fixme|sorry|admit|"
    r"axiom|external certificate|certificate interface|unproven)\b",
    re.IGNORECASE,
)
FORMULA_RE = re.compile(
    r"(\$\$.*?\$\$|\$[^$\n]+\$|\\begin\{[^}]+\}.*?\\end\{[^}]+\}|"
    r"\b(?:theorem|lemma|def|class|structure)\s+[A-Za-z0-9_'.]+)",
    re.DOTALL,
)


@dataclass(frozen=True)
class Chunk:
    source_file: Path
    language: str
    chunk_kind: str
    symbol: str
    start_line: int
    end_line: int
    raw_content: str


def stable_key(path: Path, idx: int, chunk: Chunk) -> str:
    digest = hashlib.sha1(
        f"{path}:{idx}:{chunk.start_line}:{chunk.end_line}:{chunk.symbol}".encode("utf-8")
    ).hexdigest()[:16]
    stem = re.sub(r"[^A-Za-z0-9_]", "_", path.stem).strip("_") or "chunk"
    return f"chunk_{stem}_{digest}"


def line_span(lines: list[str], start: int, end: int) -> str:
    return "\n".join(lines[start - 1 : end]).strip()


def chunk_python(path: Path, content: str) -> list[Chunk]:
    lines = content.splitlines()
    try:
        tree = ast.parse(content)
    except SyntaxError:
        return chunk_by_paragraphs(path, content, "python", "python_text")

    chunks: list[Chunk] = []
    module_header_lines: set[int] = set()
    for node in tree.body:
        if isinstance(node, PY_IMPORT_OR_ASSIGN):
            end_lineno = getattr(node, "end_lineno", node.lineno)
            module_header_lines.update(range(node.lineno, end_lineno + 1))
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            end_lineno = getattr(node, "end_lineno", node.lineno)
            chunks.append(
                Chunk(
                    source_file=path,
                    language="python",
                    chunk_kind=type(node).__name__,
                    symbol=node.name,
                    start_line=node.lineno,
                    end_line=end_lineno,
                    raw_content=line_span(lines, node.lineno, end_lineno),
                )
            )

    if module_header_lines:
        start = min(module_header_lines)
        end = max(module_header_lines)
        header = line_span(lines, start, end)
        if header:
            chunks.insert(
                0,
                Chunk(path, "python", "module_header", path.stem, start, end, header),
            )

    if not chunks:
        return chunk_by_paragraphs(path, content, "python", "python_text")
    return chunks


def chunk_lean(path: Path, content: str) -> list[Chunk]:
    """Split Lean source into top-level command chunks.

    This is structural only. It is useful for RAG chunk boundaries, but Lean
    AstExport or the Lean kernel remains the semantic authority.
    """
    lines = content.splitlines()
    chunks: list[Chunk] = []
    pending_start = 1
    start = 1

    def emit(end: int) -> None:
        nonlocal pending_start, start
        if end < start:
            return
        raw = line_span(lines, pending_start, end)
        if not raw:
            pending_start = end + 1
            start = end + 1
            return
        first_line = lines[start - 1] if start - 1 < len(lines) else ""
        name_match = LEAN_DECL_NAME.match(first_line)
        symbol = name_match.group(1) if name_match else first_line.strip().split(" ")[0]
        chunks.append(
            Chunk(
                source_file=path,
                language="lean",
                chunk_kind="lean_command",
                symbol=symbol or path.stem,
                start_line=pending_start,
                end_line=end,
                raw_content=raw,
            )
        )
        pending_start = end + 1
        start = end + 1

    for lineno, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith(LEAN_ATTACH_TO_NEXT_PREFIXES):
            if lineno > start and not lines[start - 1].strip().startswith(LEAN_ATTACH_TO_NEXT_PREFIXES):
                emit(lineno - 1)
            pending_start = lineno
            start = lineno
            continue
        if LEAN_COMMAND_START.match(line):
            if lineno > start and lines[start - 1].strip().startswith(LEAN_ATTACH_TO_NEXT_PREFIXES):
                start = lineno
                continue
            if lineno > start:
                emit(lineno - 1)
            start = lineno
            if pending_start > start:
                pending_start = start
    emit(len(lines))

    return [chunk for chunk in chunks if len(chunk.raw_content) > 0]


def chunk_markdown(path: Path, content: str) -> list[Chunk]:
    lines = content.splitlines()
    chunks: list[Chunk] = []
    in_fence = False
    in_math = False
    start = 1
    heading = path.stem

    def emit(end: int) -> None:
        nonlocal start
        raw = line_span(lines, start, end)
        if raw:
            chunks.append(Chunk(path, "markdown", "markdown_section", heading, start, end, raw))
        start = end + 1

    for lineno, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_fence = not in_fence
        if stripped == "$$":
            in_math = not in_math
        if not in_fence and not in_math and stripped.startswith("#") and lineno > start:
            emit(lineno - 1)
            heading = stripped.lstrip("#").strip() or path.stem
    emit(len(lines))
    return chunks


def chunk_by_paragraphs(path: Path, content: str, language: str, kind: str) -> list[Chunk]:
    chunks: list[Chunk] = []
    lines = content.splitlines()
    start = 1
    current: list[str] = []
    for lineno, line in enumerate(lines, start=1):
        if line.strip():
            if not current:
                start = lineno
            current.append(line)
            continue
        if current:
            raw = "\n".join(current).strip()
            chunks.append(Chunk(path, language, kind, path.stem, start, lineno - 1, raw))
            current = []
    if current:
        chunks.append(Chunk(path, language, kind, path.stem, start, len(lines), "\n".join(current)))
    return chunks


def chunk_file(path: Path) -> list[Chunk]:
    content = path.read_text(encoding="utf-8")
    if path.suffix == ".py":
        return chunk_python(path, content)
    if path.suffix == ".lean":
        return chunk_lean(path, content)
    if path.suffix == ".md":
        return chunk_markdown(path, content)
    return []


def fallback_purification(chunk: Chunk) -> dict:
    first = next((line.strip() for line in chunk.raw_content.splitlines() if line.strip()), "")
    formulas = [match.group(0).strip()[:240] for match in FORMULA_RE.finditer(chunk.raw_content)]
    entities = [chunk.symbol] if chunk.symbol else []
    if chunk.language == "lean":
        entities.extend(re.findall(r"\b(?:theorem|lemma|def|structure|class)\s+([A-Za-z0-9_'.]+)", chunk.raw_content))
    elif chunk.language == "python":
        entities.extend(re.findall(r"\b(?:def|class)\s+([A-Za-z0-9_]+)", chunk.raw_content))
    summary = f"{chunk.language} {chunk.chunk_kind} chunk `{chunk.symbol}` beginning: {first[:160]}"
    return {
        "semantic_summary": summary,
        "extracted_formulas": list(dict.fromkeys(formulas))[:16],
        "domain_entities": list(dict.fromkeys(entities))[:16],
    }


def purify_with_qwen(chunk: Chunk, endpoint: str, model: str, timeout: float, enabled: bool) -> dict:
    if not enabled:
        return fallback_purification(chunk)
    if OpenAI is None:
        print("LLM purification disabled: openai package is not installed.")
        return fallback_purification(chunk)
    try:
        client = OpenAI(base_url=endpoint, api_key="local-qwen", timeout=timeout, max_retries=0)
        response = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": chunk.raw_content[:4000]},
            ],
            temperature=0.1,
            response_format={"type": "json_object"},
        )
        payload = json.loads(response.choices[0].message.content)
        if not isinstance(payload, dict):
            return fallback_purification(chunk)
        return payload
    except Exception as exc:
        print(f"LLM purification failed for {chunk.source_file}:{chunk.start_line}: {exc}")
        return fallback_purification(chunk)


def lint_chunk(chunk: Chunk) -> list[dict]:
    issues: list[dict] = []
    if DEBT_RE.search(chunk.raw_content):
        issues.append(
            {
                "severity": "warning",
                "kind": "possible_stale_debt_label",
                "source_file": str(chunk.source_file),
                "start_line": chunk.start_line,
                "end_line": chunk.end_line,
                "symbol": chunk.symbol,
                "message": "Chunk contains debt/certificate/proof-placeholder language; verify against compiled owner declarations.",
            }
        )
    if chunk.language == "lean" and re.search(r"\b(by\s+)?(?:sorry|admit)\b", chunk.raw_content):
        issues.append(
            {
                "severity": "error",
                "kind": "lean_placeholder",
                "source_file": str(chunk.source_file),
                "start_line": chunk.start_line,
                "end_line": chunk.end_line,
                "symbol": chunk.symbol,
                "message": "Lean chunk contains an explicit proof placeholder.",
            }
        )
    return issues


def iter_input_files(input_path: Path) -> Iterable[Path]:
    for root, _, files in os.walk(input_path):
        for filename in sorted(files):
            path = Path(root) / filename
            if path.suffix in {".md", ".py", ".lean"}:
                yield path


def process_file(path: Path, args: argparse.Namespace) -> tuple[list[dict], list[dict]]:
    chunks = [chunk for chunk in chunk_file(path) if len(chunk.raw_content.strip()) >= args.min_chars]
    nodes: list[dict] = []
    issues: list[dict] = []
    print(f"Chunking {path} -> {len(chunks)} chunks")
    for idx, chunk in enumerate(chunks):
        purified = purify_with_qwen(
            chunk=chunk,
            endpoint=args.llm_endpoint,
            model=args.llm_model,
            timeout=args.llm_timeout,
            enabled=not args.no_llm,
        )
        node = {
            "_key": stable_key(path, idx, chunk),
            "source_file": str(path),
            "language": chunk.language,
            "chunk_kind": chunk.chunk_kind,
            "symbol": chunk.symbol,
            "start_line": chunk.start_line,
            "end_line": chunk.end_line,
            "raw_content": chunk.raw_content,
            "semantic_summary": purified.get("semantic_summary", ""),
            "extracted_formulas": purified.get("extracted_formulas", []),
            "domain_entities": purified.get("domain_entities", []),
        }
        nodes.append(node)
        issues.extend(lint_chunk(chunk))
    return nodes, issues


def main() -> None:
    parser = argparse.ArgumentParser(description="Universal structural chunker and purifier")
    parser.add_argument("--input-dir", type=str, required=True, help="Directory containing .md, .py, or .lean files")
    parser.add_argument("--output-dir", type=str, default="arango_export", help="Output directory for JSONL files")
    parser.add_argument("--llm-endpoint", type=str, default="http://localhost:8000/v1", help="Local Qwen vLLM endpoint")
    parser.add_argument("--llm-model", type=str, default="qwen-coder-math", help="Local OpenAI-compatible model name")
    parser.add_argument("--llm-timeout", type=float, default=8.0, help="Per-request timeout in seconds")
    parser.add_argument("--no-llm", action="store_true", help="Disable LLM purification and use deterministic metadata")
    parser.add_argument("--min-chars", type=int, default=40, help="Drop chunks smaller than this many characters")
    args = parser.parse_args()

    input_path = Path(args.input_dir)
    out_path = Path(args.output_dir)
    out_path.mkdir(parents=True, exist_ok=True)

    all_nodes: list[dict] = []
    all_issues: list[dict] = []
    for path in iter_input_files(input_path):
        nodes, issues = process_file(path, args)
        all_nodes.extend(nodes)
        all_issues.extend(issues)

    nodes_file = out_path / "decls.jsonl"
    issues_file = out_path / "lint_issues.jsonl"
    node_count = write_jsonl(nodes_file, all_nodes)
    issue_count = write_jsonl(issues_file, all_issues)

    print(f"Successfully processed {node_count} semantic chunks.")
    print(f"Lint issues: {issue_count}")
    print(f"Wrote ArangoDB nodes to: {nodes_file}")
    print(f"Wrote lint issues to: {issues_file}")


if __name__ == "__main__":
    main()
