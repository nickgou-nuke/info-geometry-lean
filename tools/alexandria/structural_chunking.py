from __future__ import annotations

import ast
import re
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Iterable, Mapping

from tools.alexandria.schema import SCHEMA_VERSION, source_uri, stable_key

HEADER_RE = re.compile(r"^(#{1,6})\s+(.*\S)\s*$")
LATEX_ENV_RE = re.compile(
    r"\\begin\{(?P<env>theorem|lemma|proposition|corollary|definition|proof|remark|equation|align)\}"
    r"(?P<option>\[[^\]]+\])?(?P<body>.*?)\\end\{(?P=env)\}",
    re.DOTALL,
)
LATEX_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


@dataclass
class StructuralSection:
    key: str
    documentKey: str
    title: str
    level: int
    ordinal: int


@dataclass
class StructuralChunk:
    key: str
    documentKey: str
    sectionKey: str
    ordinal: int
    chunkKind: str
    chunkingStrategy: str
    title: str
    text: str
    tokens: list[str]
    provenance: dict[str, object]


@dataclass
class ChunkingResult:
    sections: list[StructuralSection]
    chunks: list[StructuralChunk]
    adjacent_edges: list[dict]


DEFAULT_CAST_MAX_CHARS = 2400
DEFAULT_CAST_MIN_CHARS = 240


def tokenize(text: str) -> list[str]:
    return sorted({tok.lower() for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{2,}", text)})


def base_provenance(
    path: Path,
    resolved: Path,
    document: Mapping[str, object],
    section_title: str,
    ordinal: int,
    domain: str,
    source_format: str,
) -> dict[str, object]:
    return {
        "path": path.as_posix(),
        "sourceUri": source_uri(resolved),
        "contentHash": document["contentHash"],
        "section": section_title,
        "ordinal": ordinal,
        "domain": domain,
        "sourceKind": document["sourceKind"],
        "sourceFormat": source_format,
        "schema": SCHEMA_VERSION,
    }


def adjacent_edge(prev_chunk_key: str, chunk_key: str) -> dict:
    return {
        "_key": stable_key("adj", prev_chunk_key, chunk_key),
        "fromChunkKey": prev_chunk_key,
        "toChunkKey": chunk_key,
        "kind": "adjacent",
        "weight": 1.0,
    }


def rebuild_adjacent_edges(chunks: list[StructuralChunk]) -> list[dict]:
    edges: list[dict] = []
    prev_key: str | None = None
    for chunk in chunks:
        if prev_key is not None:
            edges.append(adjacent_edge(prev_key, chunk.key))
        prev_key = chunk.key
    return edges


def structural_segments(text: str, max_chars: int) -> list[str]:
    if len(text) <= max_chars:
        return [text]
    paragraphs = [part.strip() for part in re.split(r"\n\s*\n", text) if part.strip()]
    if len(paragraphs) <= 1:
        lines = [part.rstrip() for part in text.splitlines() if part.strip()]
        paragraphs = lines if lines else [text]

    segments: list[str] = []
    current: list[str] = []
    current_len = 0
    for paragraph in paragraphs:
        separator_len = 2 if current else 0
        if current and current_len + separator_len + len(paragraph) > max_chars:
            segments.append("\n\n".join(current).strip())
            current = []
            current_len = 0
        if len(paragraph) > max_chars:
            if current:
                segments.append("\n\n".join(current).strip())
                current = []
                current_len = 0
            # Do not blindly window an indivisible structural unit. Preserve it
            # and mark it as oversized in provenance.
            segments.append(paragraph.strip())
            continue
        current.append(paragraph)
        current_len += separator_len + len(paragraph)
    if current:
        segments.append("\n\n".join(current).strip())
    return [segment for segment in segments if segment]


def cast_clone_chunk(
    chunk: StructuralChunk,
    *,
    text: str,
    ordinal: int,
    title: str,
    parent_keys: list[str],
    max_chars: int,
    base_strategy: str,
    split_ordinal: int | None = None,
    merge_group: int | None = None,
) -> StructuralChunk:
    provenance = dict(chunk.provenance)
    provenance.update(
        {
            "chunkingStrategy": "cast_split_merge",
            "baseChunkingStrategy": base_strategy,
            "parentChunkKeys": parent_keys,
            "castMaxChars": max_chars,
            "castOversized": len(text) > max_chars,
        }
    )
    if split_ordinal is not None:
        provenance["castSplitOrdinal"] = split_ordinal
    if merge_group is not None:
        provenance["castMergeGroup"] = merge_group
    return replace(
        chunk,
        key=stable_key("chunk", chunk.sectionKey, "cast", ordinal, parent_keys, content_hash_local(text)),
        ordinal=ordinal,
        chunkingStrategy="cast_split_merge",
        title=title,
        text=text,
        tokens=tokenize(text),
        provenance=provenance,
    )


def content_hash_local(text: str) -> str:
    # Local helper avoids importing schema.content_hash into this low-level module
    # just for derived chunk keys.
    import hashlib

    return hashlib.sha1(text.encode("utf-8")).hexdigest()[:16]


def apply_cast_split_merge(
    result: ChunkingResult,
    *,
    max_chars: int = DEFAULT_CAST_MAX_CHARS,
    min_chars: int = DEFAULT_CAST_MIN_CHARS,
) -> ChunkingResult:
    """Apply cAST-style size-aware split/merge over deterministic chunks.

    The pass preserves parser-derived packet boundaries where possible. Large
    packets are split only at paragraph/line boundaries. Small adjacent packets
    are merged only when they share document, section, kind, and base strategy.
    Indivisible oversized units are retained and marked in provenance instead of
    being blindly windowed.
    """
    if max_chars <= 0:
        raise ValueError("max_chars must be positive")
    if min_chars < 0:
        raise ValueError("min_chars must be non-negative")

    split_chunks: list[StructuralChunk] = []
    ordinal = 0
    for chunk in result.chunks:
        base_strategy = chunk.chunkingStrategy
        segments = structural_segments(chunk.text, max_chars)
        if len(segments) == 1 and len(chunk.text) <= max_chars:
            ordinal += 1
            split_chunks.append(
                cast_clone_chunk(
                    chunk,
                    text=chunk.text,
                    ordinal=ordinal,
                    title=chunk.title,
                    parent_keys=[chunk.key],
                    max_chars=max_chars,
                    base_strategy=base_strategy,
                )
            )
            continue
        for split_idx, segment in enumerate(segments, start=1):
            ordinal += 1
            title = f"{chunk.title} part {split_idx}" if len(segments) > 1 else chunk.title
            split_chunks.append(
                cast_clone_chunk(
                    chunk,
                    text=segment,
                    ordinal=ordinal,
                    title=title,
                    parent_keys=[chunk.key],
                    max_chars=max_chars,
                    base_strategy=base_strategy,
                    split_ordinal=split_idx,
                )
            )

    merged_chunks: list[StructuralChunk] = []
    group: list[StructuralChunk] = []
    merge_group = 0

    def flush_group() -> None:
        nonlocal merge_group
        if not group:
            return
        if len(group) == 1:
            merged_chunks.append(group[0])
            group.clear()
            return
        merge_group += 1
        first = group[0]
        text = "\n\n".join(chunk.text for chunk in group)
        parent_keys: list[str] = []
        for chunk in group:
            keys = chunk.provenance.get("parentChunkKeys")
            if isinstance(keys, list):
                parent_keys.extend(str(key) for key in keys)
            else:
                parent_keys.append(chunk.key)
        merged = cast_clone_chunk(
            first,
            text=text,
            ordinal=len(merged_chunks) + 1,
            title=f"{first.title} merged",
            parent_keys=parent_keys,
            max_chars=max_chars,
            base_strategy=str(first.provenance.get("baseChunkingStrategy", first.chunkingStrategy)),
            merge_group=merge_group,
        )
        merged_chunks.append(merged)
        group.clear()

    for chunk in split_chunks:
        if len(chunk.text) >= min_chars or len(chunk.text) > max_chars:
            flush_group()
            merged_chunks.append(replace(chunk, ordinal=len(merged_chunks) + 1))
            continue
        if not group:
            group.append(chunk)
            continue
        first = group[0]
        candidate_len = sum(len(item.text) for item in group) + len(chunk.text) + 2 * len(group)
        compatible = (
            first.documentKey == chunk.documentKey
            and first.sectionKey == chunk.sectionKey
            and first.chunkKind == chunk.chunkKind
            and first.provenance.get("baseChunkingStrategy") == chunk.provenance.get("baseChunkingStrategy")
            and candidate_len <= max_chars
        )
        if compatible:
            group.append(chunk)
        else:
            flush_group()
            group.append(chunk)
    flush_group()

    normalized = [replace(chunk, ordinal=idx) for idx, chunk in enumerate(merged_chunks, start=1)]
    return ChunkingResult(result.sections, normalized, rebuild_adjacent_edges(normalized))


def looks_like_lean_ast(data: Any) -> bool:
    return isinstance(data, dict) and isinstance(data.get("commands"), list)


def ast_token_text(node: Any) -> list[str]:
    if isinstance(node, dict):
        values: list[str] = []
        val = node.get("rawVal", node.get("val"))
        if isinstance(val, str):
            values.append(val)
        for arg in node.get("args", []):
            values.extend(ast_token_text(arg))
        return values
    if isinstance(node, list):
        values: list[str] = []
        for item in node:
            values.extend(ast_token_text(item))
        return values
    return []


def ast_command_kind(command: Any) -> str:
    if not isinstance(command, dict):
        return "lean_command"
    kind = str(command.get("kind", "Lean.Parser.Command"))
    tokens = {tok.lower() for tok in ast_token_text(command)}
    if "theorem" in tokens or "lemma" in tokens:
        return "theorem"
    if "def" in tokens or "abbrev" in tokens:
        return "definition"
    if "structure" in tokens or "class" in tokens or "inductive" in tokens:
        return "definition"
    if "example" in tokens:
        return "proof"
    if "#check" in tokens or "#eval" in tokens or "#print" in tokens:
        return "remark"
    if kind.endswith(".declaration"):
        return "definition"
    return "lean_command"


def ast_command_title(command: Any, ordinal: int) -> str:
    tokens = ast_token_text(command)
    for idx, tok in enumerate(tokens[:-1]):
        if tok in {"def", "theorem", "lemma", "abbrev", "structure", "class", "inductive", "example"}:
            if tok == "example":
                return f"Lean example {ordinal}"
            return f"Lean {tok} {tokens[idx + 1]}"
    return f"Lean command {ordinal}"


def ast_command_text(command: Any) -> str:
    tokens = ast_token_text(command)
    return " ".join(tok for tok in tokens if tok).strip()


def chunk_lean_ast(
    path: Path,
    document: Mapping[str, object],
    resolved: Path,
    domain: str,
    ast_data: Mapping[str, Any],
) -> ChunkingResult:
    document_key = str(document["_key"])
    section = StructuralSection(
        key=stable_key("section", document_key, 1, "Lean AST"),
        documentKey=document_key,
        title="Lean AST",
        level=1,
        ordinal=1,
    )
    chunks: list[StructuralChunk] = []
    adjacent_edges: list[dict] = []
    prev_chunk_key: str | None = None
    chunk_ordinal = 0
    for command_ordinal, command in enumerate(ast_data.get("commands", []), start=1):
        block = ast_command_text(command)
        if not block:
            continue
        chunk_ordinal += 1
        title = ast_command_title(command, command_ordinal)
        provenance = base_provenance(path, resolved, document, section.title, chunk_ordinal, domain, "lean_ast")
        provenance.update(
            {
                "chunkingStrategy": "lean_ast_command",
                "astCommandOrdinal": command_ordinal,
            }
        )
        chunk = StructuralChunk(
            key=stable_key("chunk", section.key, command_ordinal, block[:80]),
            documentKey=document_key,
            sectionKey=section.key,
            ordinal=chunk_ordinal,
            chunkKind=ast_command_kind(command),
            chunkingStrategy="lean_ast_command",
            title=title,
            text=block,
            tokens=tokenize(block),
            provenance=provenance,
        )
        chunks.append(chunk)
        if prev_chunk_key is not None:
            adjacent_edges.append(adjacent_edge(prev_chunk_key, chunk.key))
        prev_chunk_key = chunk.key
    return ChunkingResult([section], chunks, adjacent_edges)


def latex_packet_title(env: str, option: str | None, ordinal: int, body: str) -> str:
    label_match = LATEX_LABEL_RE.search(body)
    label = label_match.group(1) if label_match else f"{env}-{ordinal}"
    title = option.strip("[]") if option else label
    return f"LaTeX {env} {title}"


def chunk_latex(
    path: Path,
    text: str,
    document: Mapping[str, object],
    resolved: Path,
    domain: str,
) -> ChunkingResult:
    document_key = str(document["_key"])
    section = StructuralSection(
        key=stable_key("section", document_key, 1, "LaTeX Structure"),
        documentKey=document_key,
        title="LaTeX Structure",
        level=1,
        ordinal=1,
    )
    chunks: list[StructuralChunk] = []
    adjacent_edges: list[dict] = []
    prev_chunk_key: str | None = None
    for env_ordinal, match in enumerate(LATEX_ENV_RE.finditer(text), start=1):
        env = match.group("env")
        body = match.group("body").strip()
        block = match.group(0).strip()
        chunk_kind = "theorem" if env in {"theorem", "lemma", "proposition", "corollary"} else "definition" if env == "definition" else env
        provenance = base_provenance(path, resolved, document, section.title, env_ordinal, domain, "latex")
        provenance.update(
            {
                "chunkingStrategy": "latex_environment",
                "latexEnvironment": env,
            }
        )
        chunk = StructuralChunk(
            key=stable_key("chunk", section.key, env_ordinal, block[:80]),
            documentKey=document_key,
            sectionKey=section.key,
            ordinal=env_ordinal,
            chunkKind=chunk_kind,
            chunkingStrategy="latex_environment",
            title=latex_packet_title(env, match.group("option"), env_ordinal, body),
            text=block,
            tokens=tokenize(block),
            provenance=provenance,
        )
        chunks.append(chunk)
        if prev_chunk_key is not None:
            adjacent_edges.append(adjacent_edge(prev_chunk_key, chunk.key))
        prev_chunk_key = chunk.key
    return ChunkingResult([section], chunks, adjacent_edges)


def chunk_python_ast(
    path: Path,
    text: str,
    document: Mapping[str, object],
    resolved: Path,
    domain: str,
) -> ChunkingResult:
    tree = ast.parse(text)
    document_key = str(document["_key"])
    section = StructuralSection(
        key=stable_key("section", document_key, 1, "Python AST"),
        documentKey=document_key,
        title="Python AST",
        level=1,
        ordinal=1,
    )
    chunks: list[StructuralChunk] = []
    adjacent_edges: list[dict] = []
    prev_chunk_key: str | None = None
    ordinal = 0
    for node in tree.body:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Import, ast.ImportFrom)):
            continue
        ordinal += 1
        if isinstance(node, ast.ClassDef):
            kind = "definition"
            title = f"Python class {node.name}"
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            kind = "definition"
            title = f"Python function {node.name}"
        elif isinstance(node, ast.ImportFrom):
            kind = "import"
            module = node.module or ""
            title = f"Python import from {module}"
        else:
            kind = "import"
            title = "Python import"
        block = ast.get_source_segment(text, node) or ast.dump(node, include_attributes=False)
        provenance = base_provenance(path, resolved, document, section.title, ordinal, domain, "python_ast")
        provenance.update(
            {
                "chunkingStrategy": "python_ast_node",
                "astNodeType": type(node).__name__,
                "lineStart": getattr(node, "lineno", None),
                "lineEnd": getattr(node, "end_lineno", None),
            }
        )
        chunk = StructuralChunk(
            key=stable_key("chunk", section.key, ordinal, title, block[:80]),
            documentKey=document_key,
            sectionKey=section.key,
            ordinal=ordinal,
            chunkKind=kind,
            chunkingStrategy="python_ast_node",
            title=title,
            text=block,
            tokens=tokenize(block),
            provenance=provenance,
        )
        chunks.append(chunk)
        if prev_chunk_key is not None:
            adjacent_edges.append(adjacent_edge(prev_chunk_key, chunk.key))
        prev_chunk_key = chunk.key
    return ChunkingResult([section], chunks, adjacent_edges)


def split_sections(text: str) -> list[tuple[int, str, list[str]]]:
    sections: list[tuple[int, str, list[str]]] = []
    current_title = "Front Matter"
    current_level = 1
    current_lines: list[str] = []
    for line in text.splitlines():
        match = HEADER_RE.match(line)
        if match:
            if current_lines or not sections:
                sections.append((current_level, current_title, current_lines))
            current_level = len(match.group(1))
            current_title = match.group(2).strip()
            current_lines = []
        else:
            current_lines.append(line)
    sections.append((current_level, current_title, current_lines))
    return [section for section in sections if section[2] or section[1]]


def chunk_section_lines(lines: Iterable[str]) -> list[str]:
    blocks: list[str] = []
    current: list[str] = []
    for line in lines:
        if not line.strip():
            if current:
                blocks.append("\n".join(current).strip())
                current = []
            continue
        current.append(line)
    if current:
        blocks.append("\n".join(current).strip())
    return [block for block in blocks if block]


def classify_markdown_chunk(title: str, text: str) -> str:
    blob = f"{title}\n{text}".lower()
    if any(word in blob for word in ["theorem", "lemma", "proposition", "corollary"]):
        return "theorem"
    if "proof" in blob:
        return "proof"
    if any(word in blob for word in ["hypothesis", "assume", "suppose", "given"]):
        return "hypothesis"
    if "definition" in blob:
        return "definition"
    if "remark" in blob:
        return "remark"
    return "chunk"


def chunk_markdown_blocks(
    path: Path,
    text: str,
    document: Mapping[str, object],
    resolved: Path,
    domain: str,
    source_format: str = "text",
) -> ChunkingResult:
    document_key = str(document["_key"])
    sections: list[StructuralSection] = []
    chunks: list[StructuralChunk] = []
    adjacent_edges: list[dict] = []
    prev_chunk_key: str | None = None
    chunk_ordinal = 0
    for section_ordinal, (level, title, lines) in enumerate(split_sections(text), start=1):
        section = StructuralSection(
            key=stable_key("section", document_key, section_ordinal, title),
            documentKey=document_key,
            title=title,
            level=level,
            ordinal=section_ordinal,
        )
        sections.append(section)
        for block_index, block in enumerate(chunk_section_lines(lines), start=1):
            chunk_ordinal += 1
            provenance = base_provenance(path, resolved, document, title, chunk_ordinal, domain, source_format)
            provenance["chunkingStrategy"] = "markdown_blocks"
            chunk = StructuralChunk(
                key=stable_key("chunk", section.key, block_index, block[:80]),
                documentKey=document_key,
                sectionKey=section.key,
                ordinal=chunk_ordinal,
                chunkKind=classify_markdown_chunk(title, block),
                chunkingStrategy="markdown_blocks",
                title=title,
                text=block,
                tokens=tokenize(block),
                provenance=provenance,
            )
            chunks.append(chunk)
            if prev_chunk_key is not None:
                adjacent_edges.append(adjacent_edge(prev_chunk_key, chunk.key))
            prev_chunk_key = chunk.key
    return ChunkingResult(sections, chunks, adjacent_edges)
