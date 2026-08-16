#!/usr/bin/env python3
"""LaTeX-aware math paper chunking for Alexandria/GraphRAG.

This pipeline is structural first:

1. Prefer raw arXiv/source LaTeX or already layout-parsed Markdown.
2. Split deterministically at sections and complete LaTeX/math environments.
3. Never split inside theorem/proof/equation/align-style environments.
4. Add a lightweight semantic layer and graph entities without using an LLM.
5. Optionally emit LLM enrichment requests that wrap the exact raw chunk.

The emitted JSONL files use the Alexandria collection names so they can be
loaded by ``tools/alexandria/arango_ingest.py``.
"""

from __future__ import annotations

import argparse
import bisect
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable, Iterator


if __package__ in (None, ""):
    ROOT = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT))
else:
    ROOT = Path(__file__).resolve().parents[2]

from tools.alexandria.schema import content_hash, source_uri, stable_key  # noqa: E402
from tools.pathing import normalize_user_path, repo_root  # noqa: E402


SECTION_RE = re.compile(
    r"\\(?P<kind>part|chapter|section|subsection|subsubsection|paragraph)\*?"
    r"(?:\[[^\]]*\])?\{(?P<title>[^{}\n]*(?:\{[^{}\n]*\}[^{}\n]*)*)\}",
    re.MULTILINE,
)
BEGIN_RE = re.compile(r"\\begin\{(?P<env>[A-Za-z*]+)\}(?P<option>\[[^\]]+\])?", re.MULTILINE)
END_TEMPLATE = r"\\end\{%s\}"
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:eqref|ref|autoref|cref|Cref)\{([^}]+)\}")
CITE_RE = re.compile(r"\\(?:cite|citet|citep|parencite|textcite)(?:\[[^\]]*\])*\{([^}]+)\}")
COMMAND_RE = re.compile(r"\\([A-Za-z][A-Za-z0-9]*)")
INLINE_MATH_RE = re.compile(r"(?<!\\)\$(?!\$)(.+?)(?<!\\)\$", re.DOTALL)
DISPLAY_DOLLAR_RE = re.compile(r"(?<!\\)\$\$(.+?)(?<!\\)\$\$", re.DOTALL)
DISPLAY_BRACKET_RE = re.compile(r"\\\[(.+?)\\\]", re.DOTALL)
MARKDOWN_HEADER_RE = re.compile(r"^(?P<marks>#{1,6})\s+(?P<title>.*\S)\s*$", re.MULTILINE)
TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_'.-]{2,}")

THEOREM_ENVS = {
    "theorem",
    "thm",
    "lemma",
    "lem",
    "proposition",
    "prop",
    "corollary",
    "cor",
    "claim",
    "conjecture",
}
DEFINITION_ENVS = {
    "definition",
    "defn",
    "notation",
    "example",
    "examples",
    "remark",
    "remarks",
    "assumption",
    "hypothesis",
}
PROOF_ENVS = {"proof"}
MATH_ENVS = {
    "equation",
    "equation*",
    "align",
    "align*",
    "aligned",
    "gather",
    "gather*",
    "multline",
    "multline*",
    "split",
    "cases",
    "matrix",
    "pmatrix",
    "bmatrix",
    "vmatrix",
    "Vmatrix",
    "array",
}
ATOMIC_ENVS = THEOREM_ENVS | DEFINITION_ENVS | PROOF_ENVS | MATH_ENVS
PAIRABLE_WITH_PROOF = THEOREM_ENVS | {"definition", "defn", "claim"}
COMMAND_STOPLIST = {
    "begin",
    "end",
    "label",
    "ref",
    "eqref",
    "autoref",
    "cref",
    "Cref",
    "cite",
    "citet",
    "citep",
    "parencite",
    "textcite",
    "frac",
    "left",
    "right",
    "big",
    "Big",
    "bigl",
    "bigr",
    "Bigl",
    "Bigr",
    "quad",
    "qquad",
    "mathrm",
    "mathbf",
    "mathbb",
    "mathcal",
    "operatorname",
    "text",
    "emph",
}


@dataclass
class SectionSpan:
    key: str
    title: str
    level: int
    ordinal: int
    start: int
    end: int


@dataclass
class Block:
    kind: str
    title: str
    text: str
    start: int
    end: int
    line_start: int
    line_end: int
    section: SectionSpan
    environments: list[str] = field(default_factory=list)
    labels: list[str] = field(default_factory=list)
    refs: list[str] = field(default_factory=list)
    citations: list[str] = field(default_factory=list)
    commands: list[str] = field(default_factory=list)
    ordinal: int = 0


@dataclass
class EntityRow:
    key: str
    entityType: str
    surface: str
    normalized: str
    confidence: float
    metadata: dict[str, Any]


def tokenize(text: str) -> list[str]:
    return sorted({tok.lower() for tok in TOKEN_RE.findall(text)})


def normalized_surface(text: str) -> str:
    return re.sub(r"\s+", " ", text.strip().strip("`"))


def strip_latex_for_summary(text: str) -> str:
    text = re.sub(r"\\(begin|end)\{[^}]+\}", " ", text)
    text = re.sub(r"\\[A-Za-z]+\*?(?:\[[^\]]*\])?(?:\{([^{}]*)\})?", lambda m: m.group(1) or " ", text)
    text = re.sub(r"[$_{}^]", " ", text)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def line_starts(text: str) -> list[int]:
    starts = [0]
    for idx, char in enumerate(text):
        if char == "\n":
            starts.append(idx + 1)
    return starts


def line_number(starts: list[int], offset: int) -> int:
    return bisect.bisect_right(starts, offset)


def extract_braced_values(regex: re.Pattern[str], text: str) -> list[str]:
    values: list[str] = []
    for match in regex.finditer(text):
        raw = match.group(1)
        for item in raw.split(","):
            item = item.strip()
            if item:
                values.append(item)
    return values


def unique_ordered(values: Iterable[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for value in values:
        value = str(value).strip()
        if not value or value in seen:
            continue
        seen.add(value)
        out.append(value)
    return out


def find_matching_env_end(text: str, env: str, search_start: int) -> int | None:
    begin_pat = re.compile(r"\\begin\{%s\}" % re.escape(env))
    end_pat = re.compile(END_TEMPLATE % re.escape(env))
    depth = 1
    pos = search_start
    while depth > 0:
        next_begin = begin_pat.search(text, pos)
        next_end = end_pat.search(text, pos)
        if next_end is None:
            return None
        if next_begin is not None and next_begin.start() < next_end.start():
            depth += 1
            pos = next_begin.end()
        else:
            depth -= 1
            pos = next_end.end()
    return pos


def env_kind(env: str) -> str:
    if env in THEOREM_ENVS:
        return "theorem"
    if env in DEFINITION_ENVS:
        return "definition" if env not in {"remark", "remarks", "example", "examples"} else "remark"
    if env in PROOF_ENVS:
        return "proof"
    if env in MATH_ENVS:
        return "equation"
    return "latex_environment"


def env_title(env: str, option: str | None, body: str, ordinal: int) -> str:
    labels = extract_braced_values(LABEL_RE, body)
    if option:
        detail = option.strip("[]").strip()
    elif labels:
        detail = labels[0]
    else:
        detail = str(ordinal)
    return f"{env} {detail}"


def latex_env_spans(text: str, starts: list[int], occupied: list[tuple[int, int]] | None = None) -> list[Block]:
    blocks: list[Block] = []
    occupied_until = -1
    occupied = occupied or []
    dummy_section = SectionSpan("pending", "pending", 1, 0, 0, len(text))

    def overlaps(start: int, end: int) -> bool:
        return any(not (end <= a or start >= b) for a, b in occupied)

    for ordinal, match in enumerate(BEGIN_RE.finditer(text), start=1):
        if match.start() < occupied_until:
            continue
        env = match.group("env")
        if env not in ATOMIC_ENVS:
            continue
        end = find_matching_env_end(text, env, match.end())
        if end is None:
            continue
        if overlaps(match.start(), end):
            continue
        block_text = text[match.start() : end]
        labels = unique_ordered(extract_braced_values(LABEL_RE, block_text))
        refs = unique_ordered(extract_braced_values(REF_RE, block_text))
        citations = unique_ordered(extract_braced_values(CITE_RE, block_text))
        commands = unique_ordered(
            cmd
            for cmd in COMMAND_RE.findall(block_text)
            if cmd not in COMMAND_STOPLIST and len(cmd) > 1
        )
        blocks.append(
            Block(
                kind=env_kind(env),
                title=env_title(env, match.group("option"), block_text, ordinal),
                text=block_text.strip(),
                start=match.start(),
                end=end,
                line_start=line_number(starts, match.start()),
                line_end=line_number(starts, max(match.start(), end - 1)),
                section=dummy_section,
                environments=[env],
                labels=labels,
                refs=refs,
                citations=citations,
                commands=commands,
            )
        )
        occupied_until = end
    return blocks


def math_display_spans(text: str, starts: list[int], occupied: list[tuple[int, int]]) -> list[Block]:
    dummy_section = SectionSpan("pending", "pending", 1, 0, 0, len(text))
    blocks: list[Block] = []

    def overlaps(start: int, end: int) -> bool:
        return any(not (end <= a or start >= b) for a, b in occupied)

    patterns = [
        ("display_math", DISPLAY_DOLLAR_RE),
        ("display_math", DISPLAY_BRACKET_RE),
    ]
    for kind, pattern in patterns:
        for idx, match in enumerate(pattern.finditer(text), start=1):
            if overlaps(match.start(), match.end()):
                continue
            block_text = match.group(0)
            blocks.append(
                Block(
                    kind="equation",
                    title=f"{kind} {idx}",
                    text=block_text.strip(),
                    start=match.start(),
                    end=match.end(),
                    line_start=line_number(starts, match.start()),
                    line_end=line_number(starts, max(match.start(), match.end() - 1)),
                    section=dummy_section,
                    environments=[kind],
                    labels=unique_ordered(extract_braced_values(LABEL_RE, block_text)),
                    refs=unique_ordered(extract_braced_values(REF_RE, block_text)),
                    citations=unique_ordered(extract_braced_values(CITE_RE, block_text)),
                    commands=unique_ordered(
                        cmd for cmd in COMMAND_RE.findall(block_text) if cmd not in COMMAND_STOPLIST
                    ),
                )
            )
    return blocks


def markdown_sections(text: str, document_key: str) -> list[SectionSpan]:
    matches = list(MARKDOWN_HEADER_RE.finditer(text))
    if not matches:
        return [SectionSpan(stable_key("section", document_key, 1, "Document"), "Document", 1, 1, 0, len(text))]
    spans: list[SectionSpan] = []
    if matches[0].start() > 0:
        spans.append(SectionSpan(stable_key("section", document_key, 1, "Front Matter"), "Front Matter", 1, 1, 0, matches[0].start()))
    ordinal_offset = len(spans)
    for raw_idx, match in enumerate(matches):
        idx = ordinal_offset + raw_idx + 1
        end = matches[raw_idx + 1].start() if raw_idx + 1 < len(matches) else len(text)
        level = len(match.group("marks"))
        title = match.group("title").strip()
        spans.append(SectionSpan(stable_key("section", document_key, idx, title), title, level, idx, match.start(), end))
    return [span for span in spans if span.start < span.end]


def latex_sections(text: str, document_key: str) -> list[SectionSpan]:
    matches = list(SECTION_RE.finditer(text))
    if not matches:
        if MARKDOWN_HEADER_RE.search(text):
            return markdown_sections(text, document_key)
        return [SectionSpan(stable_key("section", document_key, 1, "Document"), "Document", 1, 1, 0, len(text))]
    level_map = {"part": 1, "chapter": 1, "section": 2, "subsection": 3, "subsubsection": 4, "paragraph": 5}
    spans: list[SectionSpan] = []
    if matches[0].start() > 0:
        spans.append(SectionSpan(stable_key("section", document_key, 1, "Front Matter"), "Front Matter", 1, 1, 0, matches[0].start()))
    offset = len(spans)
    for raw_idx, match in enumerate(matches, start=1):
        ordinal = offset + raw_idx
        end = matches[raw_idx].start() if raw_idx < len(matches) else len(text)
        kind = match.group("kind")
        title = strip_latex_for_summary(match.group("title")) or kind
        spans.append(SectionSpan(stable_key("section", document_key, ordinal, title), title, level_map.get(kind, 2), ordinal, match.start(), end))
    return [span for span in spans if span.start < span.end]


def split_prose(text: str, start_offset: int, starts: list[int], section: SectionSpan, *, max_chars: int) -> list[Block]:
    blocks: list[Block] = []
    cursor = 0
    paragraphs: list[tuple[int, int, str]] = []
    for match in re.finditer(r"\n\s*\n", text):
        raw = text[cursor : match.start()]
        if raw.strip():
            paragraphs.append((cursor, match.start(), raw))
        cursor = match.end()
    tail = text[cursor:]
    if tail.strip():
        paragraphs.append((cursor, len(text), tail))

    current: list[tuple[int, int, str]] = []
    current_len = 0

    def flush() -> None:
        nonlocal current, current_len
        if not current:
            return
        local_start = current[0][0]
        local_end = current[-1][1]
        raw_text = "\n\n".join(item[2].strip() for item in current).strip()
        if raw_text:
            abs_start = start_offset + local_start
            abs_end = start_offset + local_end
            blocks.append(
                Block(
                    kind="prose",
                    title=f"Prose in {section.title}",
                    text=raw_text,
                    start=abs_start,
                    end=abs_end,
                    line_start=line_number(starts, abs_start),
                    line_end=line_number(starts, max(abs_start, abs_end - 1)),
                    section=section,
                    labels=unique_ordered(extract_braced_values(LABEL_RE, raw_text)),
                    refs=unique_ordered(extract_braced_values(REF_RE, raw_text)),
                    citations=unique_ordered(extract_braced_values(CITE_RE, raw_text)),
                    commands=unique_ordered(
                        cmd for cmd in COMMAND_RE.findall(raw_text) if cmd not in COMMAND_STOPLIST
                    ),
                )
            )
        current = []
        current_len = 0

    for paragraph in paragraphs:
        para_len = len(paragraph[2])
        if current and current_len + para_len + 2 > max_chars:
            flush()
        if para_len > max_chars:
            flush()
            lines = paragraph[2].splitlines()
            chunk_start = paragraph[0]
            acc: list[str] = []
            acc_len = 0
            local_cursor = paragraph[0]
            for line in lines:
                if acc and acc_len + len(line) + 1 > max_chars:
                    local_text = "\n".join(acc)
                    abs_start = start_offset + chunk_start
                    abs_end = start_offset + local_cursor
                    blocks.append(
                        Block(
                            kind="prose",
                            title=f"Prose in {section.title}",
                            text=local_text.strip(),
                            start=abs_start,
                            end=abs_end,
                            line_start=line_number(starts, abs_start),
                            line_end=line_number(starts, max(abs_start, abs_end - 1)),
                            section=section,
                        )
                    )
                    acc = []
                    acc_len = 0
                    chunk_start = local_cursor
                acc.append(line)
                acc_len += len(line) + 1
                local_cursor += len(line) + 1
            if acc:
                local_text = "\n".join(acc)
                abs_start = start_offset + chunk_start
                abs_end = start_offset + paragraph[1]
                blocks.append(
                    Block(
                        kind="prose",
                        title=f"Prose in {section.title}",
                        text=local_text.strip(),
                        start=abs_start,
                        end=abs_end,
                        line_start=line_number(starts, abs_start),
                        line_end=line_number(starts, max(abs_start, abs_end - 1)),
                        section=section,
                    )
                )
            continue
        current.append(paragraph)
        current_len += para_len + 2
    flush()
    return blocks


def assign_sections(blocks: list[Block], sections: list[SectionSpan]) -> list[Block]:
    out: list[Block] = []
    for block in blocks:
        section = next((s for s in sections if s.start <= block.start < s.end), sections[0])
        block.section = section
        out.append(block)
    return out


def bind_adjacent_proofs(blocks: list[Block], starts: list[int]) -> list[Block]:
    ordered = sorted(blocks, key=lambda b: (b.start, b.end))
    bound: list[Block] = []
    idx = 0
    while idx < len(ordered):
        current = ordered[idx]
        if (
            idx + 1 < len(ordered)
            and current.environments
            and current.environments[-1] in PAIRABLE_WITH_PROOF
            and ordered[idx + 1].environments
            and ordered[idx + 1].environments[0] in PROOF_ENVS
            and current.section.key == ordered[idx + 1].section.key
        ):
            proof = ordered[idx + 1]
            gap = current.text and proof.start >= current.end
            gap_text = "" if not gap else ""
            text = current.text.rstrip() + "\n\n" + gap_text + proof.text.lstrip()
            start = current.start
            end = proof.end
            bound.append(
                Block(
                    kind="theorem_with_proof",
                    title=f"{current.title} with proof",
                    text=text.strip(),
                    start=start,
                    end=end,
                    line_start=line_number(starts, start),
                    line_end=line_number(starts, max(start, end - 1)),
                    section=current.section,
                    environments=current.environments + proof.environments,
                    labels=unique_ordered(current.labels + proof.labels),
                    refs=unique_ordered(current.refs + proof.refs),
                    citations=unique_ordered(current.citations + proof.citations),
                    commands=unique_ordered(current.commands + proof.commands),
                )
            )
            idx += 2
        else:
            bound.append(current)
            idx += 1
    return bound


def structural_blocks(text: str, document_key: str, *, source_format: str, max_chars: int, bind_proofs: bool) -> tuple[list[SectionSpan], list[Block]]:
    starts = line_starts(text)
    sections = markdown_sections(text, document_key) if source_format == "markdown" else latex_sections(text, document_key)
    math_blocks = math_display_spans(text, starts, [])
    occupied = [(block.start, block.end) for block in math_blocks]
    env_blocks = latex_env_spans(text, starts, occupied)
    atomic = sorted(env_blocks + math_blocks, key=lambda block: (block.start, block.end))
    atomic = assign_sections(atomic, sections)

    blocks: list[Block] = []
    for section in sections:
        cursor = section.start
        atoms = [block for block in atomic if section.start <= block.start < section.end]
        for atom in atoms:
            if cursor < atom.start:
                blocks.extend(split_prose(text[cursor : atom.start], cursor, starts, section, max_chars=max_chars))
            blocks.append(atom)
            cursor = max(cursor, atom.end)
        if cursor < section.end:
            blocks.extend(split_prose(text[cursor : section.end], cursor, starts, section, max_chars=max_chars))

    blocks = sorted(blocks, key=lambda block: (block.start, block.end))
    if bind_proofs:
        blocks = bind_adjacent_proofs(blocks, starts)
    for ordinal, block in enumerate(blocks, start=1):
        block.ordinal = ordinal
    return sections, blocks


def infer_source_format(path: Path, text: str, requested: str) -> str:
    if requested != "auto":
        return requested
    suffix = path.suffix.lower()
    if suffix in {".md", ".markdown", ".mmd"}:
        return "markdown"
    if "\\begin{" in text or "\\section" in text or suffix == ".tex":
        return "latex"
    return "markdown"


def extract_symbols(block: Block) -> list[str]:
    symbols: list[str] = []
    for math_text in INLINE_MATH_RE.findall(block.text):
        symbols.extend(re.findall(r"\\?[A-Za-z][A-Za-z0-9_]*", math_text))
    for math_text in DISPLAY_DOLLAR_RE.findall(block.text):
        symbols.extend(re.findall(r"\\?[A-Za-z][A-Za-z0-9_]*", math_text))
    for symbol in symbols:
        symbol = symbol.lstrip("\\")
        if symbol and symbol not in COMMAND_STOPLIST and len(symbol) <= 48:
            yield symbol


def semantic_layer(block: Block) -> dict[str, Any]:
    labels = block.labels
    refs = block.refs
    citations = block.citations
    commands = [cmd for cmd in block.commands if cmd not in COMMAND_STOPLIST]
    symbols = unique_ordered(extract_symbols(block))[:24]
    entities = unique_ordered(
        block.environments
        + [f"label:{label}" for label in labels]
        + [f"ref:{ref}" for ref in refs]
        + [f"cite:{cite}" for cite in citations]
        + [f"cmd:{cmd}" for cmd in commands[:16]]
        + [f"symbol:{sym}" for sym in symbols[:16]]
    )
    assumed = unique_ordered([f"ref:{ref}" for ref in refs] + [f"cite:{cite}" for cite in citations] + [f"symbol:{sym}" for sym in symbols[:12]])
    summary_text = strip_latex_for_summary(block.text)
    first_sentence = re.split(r"(?<=[.!?])\s+", summary_text, maxsplit=1)[0].strip()
    if not first_sentence:
        first_sentence = f"{block.kind} fragment in section {block.section.title}"
    if len(first_sentence) > 240:
        first_sentence = first_sentence[:237].rstrip() + "..."
    summary = f"{block.kind}: {first_sentence}"
    triplets: list[list[str]] = []
    subject = labels[0] if labels else block.title
    for ref in refs:
        triplets.append([subject, "REFERENCES", ref])
    for cite in citations:
        triplets.append([subject, "CITES", cite])
    if block.kind == "theorem_with_proof":
        triplets.append([subject, "VALIDATED_BY", "proof"])
    if block.kind == "proof":
        triplets.append([subject, "VALIDATES", "previous_theorem_like_block"])
    return {
        "summary": summary,
        "assumed_definitions": assumed,
        "mathematical_entities": entities,
        "graph_triplets": triplets,
        "raw_content": block.text,
        "semantic_mode": "heuristic_structural_v1",
    }


def entity_kind(surface: str) -> str:
    if surface.startswith("label:"):
        return "latex_label"
    if surface.startswith("ref:"):
        return "latex_reference"
    if surface.startswith("cite:"):
        return "citation"
    if surface.startswith("cmd:"):
        return "latex_command"
    if surface.startswith("symbol:"):
        return "math_symbol"
    if surface in ATOMIC_ENVS:
        return "latex_environment"
    return "math_entity"


def build_entity(surface: str, *, document_key: str) -> EntityRow:
    normalized = normalized_surface(surface)
    kind = entity_kind(normalized)
    confidence = {
        "latex_label": 1.0,
        "latex_reference": 0.92,
        "citation": 0.9,
        "latex_environment": 0.88,
        "latex_command": 0.72,
        "math_symbol": 0.62,
    }.get(kind, 0.55)
    return EntityRow(
        key=stable_key("entity", document_key, kind, normalized.lower()),
        entityType=kind,
        surface=surface,
        normalized=normalized,
        confidence=confidence,
        metadata={"documentKey": document_key},
    )


def safe_extract_tar(archive: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive) as tar:
        for member in tar.getmembers():
            target = (destination / member.name).resolve()
            if not str(target).startswith(str(destination.resolve())):
                raise RuntimeError(f"unsafe tar member path: {member.name}")
        tar.extractall(destination)


def download_arxiv_source(arxiv_id: str, work_dir: Path) -> list[Path]:
    safe_id = arxiv_id.replace("/", "_")
    target_dir = work_dir / safe_id
    target_dir.mkdir(parents=True, exist_ok=True)
    archive = target_dir / "source"
    url = f"https://arxiv.org/e-print/{arxiv_id}"
    urllib.request.urlretrieve(url, archive)
    extracted = target_dir / "src"
    try:
        safe_extract_tar(archive, extracted)
    except tarfile.TarError:
        try:
            raw = gzip.decompress(archive.read_bytes())
            tex = extracted / f"{safe_id}.tex"
            extracted.mkdir(parents=True, exist_ok=True)
            tex.write_bytes(raw)
        except OSError:
            tex = extracted / f"{safe_id}.tex"
            extracted.mkdir(parents=True, exist_ok=True)
            tex.write_bytes(archive.read_bytes())
    return sorted(extracted.rglob("*.tex"))


def pdf_to_markdown(pdf: Path, parser: str, out_dir: Path) -> Path:
    if parser == "none":
        raise RuntimeError(f"{pdf}: PDF input requires --pdf-parser marker|nougat or pre-parsed Markdown")
    out_dir.mkdir(parents=True, exist_ok=True)
    before = {p.resolve() for p in out_dir.rglob("*") if p.is_file()}
    if parser == "marker":
        binary = shutil.which("marker_single")
        if not binary:
            raise RuntimeError("marker_single not found; install Marker or pass pre-parsed Markdown")
        subprocess.run([binary, str(pdf), "--output_dir", str(out_dir)], check=True)
    elif parser == "nougat":
        binary = shutil.which("nougat")
        if not binary:
            raise RuntimeError("nougat not found; install Nougat or pass pre-parsed Markdown")
        subprocess.run([binary, str(pdf), "-o", str(out_dir)], check=True)
    else:
        raise RuntimeError(f"unsupported PDF parser: {parser}")
    after = [p for p in out_dir.rglob("*") if p.is_file() and p.resolve() not in before and p.suffix.lower() in {".md", ".mmd", ".markdown"}]
    if not after:
        after = [p for p in out_dir.rglob("*") if p.is_file() and p.suffix.lower() in {".md", ".mmd", ".markdown"}]
    if not after:
        raise RuntimeError(f"{parser} produced no Markdown file under {out_dir}")
    return sorted(after, key=lambda p: (len(p.parts), p.as_posix()))[0]


def input_files_from_path(path: Path) -> list[Path]:
    if path.is_file():
        return [path]
    suffixes = {".tex", ".md", ".markdown", ".mmd", ".txt", ".pdf"}
    return sorted(p for p in path.rglob("*") if p.is_file() and p.suffix.lower() in suffixes)


def document_title(path: Path, text: str) -> str:
    title_match = re.search(r"\\title(?:\[[^\]]*\])?\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", text)
    if title_match:
        title = strip_latex_for_summary(title_match.group(1))
        if title:
            return title
    for match in MARKDOWN_HEADER_RE.finditer(text):
        return match.group("title").strip()
    return path.stem


def llm_prompt(chunk_row: dict[str, Any]) -> dict[str, Any]:
    raw = chunk_row["text"]
    return {
        "_key": stable_key("llmreq", chunk_row["_key"]),
        "chunkKey": chunk_row["_key"],
        "system": (
            "You are a mathematical knowledge engineer. Analyze the document fragment. "
            "Provide a structured semantic layer. Do not alter the raw mathematical content."
        ),
        "user": (
            "Output exactly this JSON shape: "
            '{"summary": "...", "assumed_definitions": [], "mathematical_entities": [], '
            '"graph_triplets": [], "raw_content": "..."}\n\n'
            f"Fragment:\n{raw}"
        ),
    }


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def process_document(path: Path, *, source_format: str, max_chars: int, bind_proofs: bool) -> dict[str, list[dict[str, Any]]]:
    raw_text = path.read_text(encoding="utf-8", errors="replace")
    fmt = infer_source_format(path, raw_text, source_format)
    document_key = stable_key("doc", path.resolve(), content_hash(raw_text))
    sections, blocks = structural_blocks(raw_text, document_key, source_format=fmt, max_chars=max_chars, bind_proofs=bind_proofs)
    doc = {
        "_key": document_key,
        "path": path.as_posix(),
        "title": document_title(path, raw_text),
        "sourceType": path.suffix.lower().lstrip(".") or fmt,
        "sourceFormat": fmt,
        "sourceUri": source_uri(path),
        "contentHash": content_hash(raw_text),
        "domain": "math_paper",
        "parser": "math_paper_graphrag_ingest.structural_latex_v1",
    }

    entity_by_key: dict[str, EntityRow] = {}
    rows: dict[str, list[dict[str, Any]]] = {
        "alexandria_documents": [doc],
        "alexandria_sections": [],
        "alexandria_chunks": [],
        "alexandria_entities": [],
        "alexandria_document_section_edges": [],
        "alexandria_section_chunk_edges": [],
        "alexandria_chunk_entity_edges": [],
        "alexandria_chunk_adjacent_edges": [],
        "alexandria_entity_relation_edges": [],
        "math_llm_requests": [],
    }

    for section in sections:
        section_row = {
            "_key": section.key,
            "documentKey": document_key,
            "title": section.title,
            "level": section.level,
            "ordinal": section.ordinal,
            "lineStart": None,
            "lineEnd": None,
        }
        rows["alexandria_sections"].append(section_row)
        rows["alexandria_document_section_edges"].append(
            {
                "_key": stable_key("docsec", document_key, section.key),
                "_from": f"alexandria_documents/{document_key}",
                "_to": f"alexandria_sections/{section.key}",
                "ordinal": section.ordinal,
            }
        )

    prev_chunk_key: str | None = None
    for block in blocks:
        semantic = semantic_layer(block)
        chunk_key = stable_key("chunk", document_key, block.ordinal, block.start, block.end, block.kind)
        chunk_row = {
            "_key": chunk_key,
            "documentKey": document_key,
            "sectionKey": block.section.key,
            "ordinal": block.ordinal,
            "chunkKind": block.kind,
            "title": block.title,
            "text": block.text,
            "rawContent": block.text,
            "tokens": tokenize(block.text + " " + semantic["summary"]),
            "semantic": semantic,
            "provenance": {
                "path": path.as_posix(),
                "sourceFormat": fmt,
                "chunkingStrategy": "latex_environment_aware",
                "lineStart": block.line_start,
                "lineEnd": block.line_end,
                "charStart": block.start,
                "charEnd": block.end,
                "section": block.section.title,
                "environments": block.environments,
                "labels": block.labels,
                "refs": block.refs,
                "citations": block.citations,
            },
        }
        rows["alexandria_chunks"].append(chunk_row)
        rows["math_llm_requests"].append(llm_prompt(chunk_row))
        rows["alexandria_section_chunk_edges"].append(
            {
                "_key": stable_key("secchunk", block.section.key, chunk_key),
                "_from": f"alexandria_sections/{block.section.key}",
                "_to": f"alexandria_chunks/{chunk_key}",
                "ordinal": block.ordinal,
                "chunkKind": block.kind,
            }
        )
        if prev_chunk_key is not None:
            rows["alexandria_chunk_adjacent_edges"].append(
                {
                    "_key": stable_key("adj", prev_chunk_key, chunk_key),
                    "_from": f"alexandria_chunks/{prev_chunk_key}",
                    "_to": f"alexandria_chunks/{chunk_key}",
                    "kind": "adjacent",
                    "weight": 1.0,
                }
            )
        prev_chunk_key = chunk_key

        chunk_entity_keys: set[str] = set()
        for surface in semantic["mathematical_entities"]:
            entity = build_entity(surface, document_key=document_key)
            entity_by_key.setdefault(entity.key, entity)
            chunk_entity_keys.add(entity.key)
            rows["alexandria_chunk_entity_edges"].append(
                {
                    "_key": stable_key("chunkent", chunk_key, entity.key),
                    "_from": f"alexandria_chunks/{chunk_key}",
                    "_to": f"alexandria_entities/{entity.key}",
                    "entityType": entity.entityType,
                    "confidence": entity.confidence,
                }
            )

        for src_surface, relation, dst_surface in semantic["graph_triplets"]:
            src = build_entity(src_surface, document_key=document_key)
            dst = build_entity(dst_surface, document_key=document_key)
            entity_by_key.setdefault(src.key, src)
            entity_by_key.setdefault(dst.key, dst)
            rows["alexandria_entity_relation_edges"].append(
                {
                    "_key": stable_key("rel", src.key, relation, dst.key, chunk_key),
                    "_from": f"alexandria_entities/{src.key}",
                    "_to": f"alexandria_entities/{dst.key}",
                    "relationType": relation.lower(),
                    "chunkKey": chunk_key,
                    "evidence": "heuristic_structural_semantic_layer",
                    "weight": 0.75,
                }
            )

    rows["alexandria_entities"] = [{"_key": entity.key, **asdict(entity)} for entity in entity_by_key.values()]
    return rows


def merge_rows(target: dict[str, list[dict[str, Any]]], source: dict[str, list[dict[str, Any]]]) -> None:
    for key, values in source.items():
        target.setdefault(key, []).extend(values)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", action="append", default=[], help="Input .tex/.md/.mmd/.txt/.pdf file or directory. Repeatable.")
    parser.add_argument("--arxiv-id", action="append", default=[], help="arXiv id to download via https://arxiv.org/e-print/<id>. Repeatable.")
    parser.add_argument("--work-dir", type=Path, default=Path("artifacts/alexandria/math_papers/source_work"))
    parser.add_argument("--output", type=Path, required=True, help="Output directory for Alexandria JSONL artifacts.")
    parser.add_argument("--source-format", choices=["auto", "latex", "markdown"], default="auto")
    parser.add_argument("--pdf-parser", choices=["none", "marker", "nougat"], default="none")
    parser.add_argument("--pdf-work-dir", type=Path, default=Path("artifacts/alexandria/math_papers/pdf_markdown"))
    parser.add_argument("--max-chars", type=int, default=3600)
    parser.add_argument("--max-docs", type=int, default=0, help="Limit documents processed; 0 means unlimited.")
    parser.add_argument("--no-bind-proofs", action="store_true", help="Do not merge theorem/lemma blocks with following proof blocks.")
    parser.add_argument("--emit-llm-requests", action="store_true", help="Keep math_llm_requests.jsonl in output.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    input_paths: list[Path] = []
    for raw in args.input:
        input_paths.extend(input_files_from_path(normalize_user_path(raw, root)))
    if args.arxiv_id:
        for arxiv_id in args.arxiv_id:
            input_paths.extend(download_arxiv_source(arxiv_id, normalize_user_path(str(args.work_dir), root)))
    if not input_paths:
        raise SystemExit("no input documents supplied")

    docs: list[Path] = []
    pdf_work = normalize_user_path(str(args.pdf_work_dir), root)
    for path in input_paths:
        if path.suffix.lower() == ".pdf":
            docs.append(pdf_to_markdown(path, args.pdf_parser, pdf_work / path.stem))
        else:
            docs.append(path)
    docs = unique_ordered(str(path) for path in docs)
    doc_paths = [Path(path) for path in docs]
    if args.max_docs > 0:
        doc_paths = doc_paths[: args.max_docs]

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
    }
    for path in doc_paths:
        merge_rows(
            all_rows,
            process_document(
                path,
                source_format=args.source_format,
                max_chars=max(512, int(args.max_chars)),
                bind_proofs=not args.no_bind_proofs,
            ),
        )

    output = normalize_user_path(str(args.output), root)
    counts: dict[str, int] = {}
    for collection, rows in all_rows.items():
        if collection == "math_llm_requests" and not args.emit_llm_requests:
            continue
        counts[collection] = write_jsonl(output / f"{collection}.jsonl", rows)
    manifest = {
        "schema": "info_geometry.alexandria.math_paper_graphrag.manifest.v1",
        "inputs": [path.as_posix() for path in doc_paths],
        "output": output.as_posix(),
        "counts": counts,
        "chunking": {
            "structural_first": True,
            "bind_proofs": not args.no_bind_proofs,
            "max_chars": max(512, int(args.max_chars)),
            "source_format": args.source_format,
            "pdf_parser": args.pdf_parser,
        },
        "authority": "semantic_graph_context_only_not_proof_authority",
    }
    (output / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "[math-paper-graphrag] "
        f"documents={counts.get('alexandria_documents', 0)} "
        f"chunks={counts.get('alexandria_chunks', 0)} "
        f"entities={counts.get('alexandria_entities', 0)} "
        f"relations={counts.get('alexandria_entity_relation_edges', 0)} "
        f"output={output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
