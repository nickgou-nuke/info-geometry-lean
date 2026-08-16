#!/usr/bin/env python3
"""Recover text-layer source fragments from math PDFs.

This is a reconstruction tool, not an original-source oracle.  If a PDF does
not embed its TeX sources, the best available path is to use coordinates and
fonts from the PDF text layer.  This script reads ``pdftohtml -xml`` output,
finds monospaced/code font spans, reconstructs line-oriented code blocks, and
emits candidate ``.lean``/``.py`` snippets plus JSONL metadata.

Lean authority still begins only after ``lake env lean`` accepts a recovered
candidate.  Python authority here is only ``ast.parse`` syntax acceptance.
"""

from __future__ import annotations

import argparse
import ast
import html
import json
import re
import statistics
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable


if __package__ in (None, ""):
    ROOT = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT))
else:
    ROOT = Path(__file__).resolve().parents[2]

from tools.alexandria.schema import content_hash, stable_key  # noqa: E402
from tools.pathing import normalize_user_path, repo_root  # noqa: E402


SCHEMA = "info_geometry.alexandria.pdf_source_recovery.v1"
AUTHORITY = "pdf_text_layer_reconstruction_not_original_source"

LEAN_HINT_RE = re.compile(
    r"^\s*(?:import|namespace|open|variable|section|theorem|lemma|def|abbrev|"
    r"structure|class|inductive|example|instance)\b",
    re.MULTILINE,
)
PYTHON_HINT_RE = re.compile(
    r"^\s*(?:@[\w.]+|from\s+\S+\s+import\b|import\s+\S+|def\s+\w+|class\s+\w+|"
    r"if\s+__name__\s*==|>>>|\.\.\.)",
    re.MULTILINE,
)
LEAN_SPECIFIC_RE = re.compile(r":=|→|↔|∀|⟨|⟩|\b(?:Prop|Type|Sort|where|by)\b")
PYTHON_SPECIFIC_RE = re.compile(r"^\s*(?:def|class)\s+\w+\(.*\):|^\s*@[\w.]+", re.MULTILINE)


@dataclass(frozen=True)
class FontSpec:
    id: str
    size: float
    family: str
    color: str


@dataclass(frozen=True)
class TextSpan:
    page: int
    pageWidth: float
    pageHeight: float
    top: float
    left: float
    width: float
    height: float
    font: str
    family: str
    color: str
    text: str


@dataclass(frozen=True)
class RecoveredLine:
    key: str
    page: int
    top: float
    left: float
    right: float
    text: str
    sourceKind: str
    fonts: list[str]
    colors: list[str]
    metadata: dict[str, Any]


@dataclass(frozen=True)
class RecoveredCodeBlock:
    key: str
    language: str
    pageStart: int
    pageEnd: int
    lineStart: int
    lineEnd: int
    left: float
    right: float
    text: str
    validationStatus: str
    validationMessage: str
    metadata: dict[str, Any]


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def clean_text(text: str) -> str:
    text = html.unescape(text)
    text = text.replace("\xa0", " ").replace("\u00ad", "")
    text = re.sub(r"\s+", " ", text)
    return text


def as_float(value: str | None, default: float = 0.0) -> float:
    if value is None:
        return default
    try:
        return float(value)
    except ValueError:
        return default


def run_pdftohtml_xml(pdf: Path, output_base: Path, *, first_page: int, last_page: int) -> Path:
    output_base.parent.mkdir(parents=True, exist_ok=True)
    cmd = ["pdftohtml", "-xml", "-i"]
    if first_page > 0:
        cmd.extend(["-f", str(first_page)])
    if last_page > 0:
        cmd.extend(["-l", str(last_page)])
    cmd.extend([str(pdf), str(output_base)])
    proc = subprocess.run(cmd, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        output = (proc.stdout + "\n" + proc.stderr).strip()
        raise SystemExit(f"pdftohtml failed with code {proc.returncode}: {output}")
    xml_path = output_base.with_suffix(".xml")
    if not xml_path.exists():
        raise SystemExit(f"pdftohtml did not create expected XML file: {xml_path}")
    return xml_path


def load_xml(xml_path: Path) -> tuple[dict[str, FontSpec], list[TextSpan]]:
    root = ET.parse(xml_path).getroot()
    fonts: dict[str, FontSpec] = {}
    for font in root.iter("fontspec"):
        font_id = str(font.attrib.get("id", ""))
        if not font_id:
            continue
        fonts[font_id] = FontSpec(
            id=font_id,
            size=as_float(font.attrib.get("size")),
            family=str(font.attrib.get("family", "")),
            color=str(font.attrib.get("color", "")),
        )

    spans: list[TextSpan] = []
    for page in root.iter("page"):
        page_no = int(as_float(page.attrib.get("number"), 0))
        page_width = as_float(page.attrib.get("width"))
        page_height = as_float(page.attrib.get("height"))
        for text_node in page.iter("text"):
            raw_text = "".join(text_node.itertext())
            text = clean_text(raw_text)
            if not text.strip():
                continue
            font_id = str(text_node.attrib.get("font", ""))
            spec = fonts.get(font_id, FontSpec(font_id, 0.0, "", ""))
            spans.append(
                TextSpan(
                    page=page_no,
                    pageWidth=page_width,
                    pageHeight=page_height,
                    top=as_float(text_node.attrib.get("top")),
                    left=as_float(text_node.attrib.get("left")),
                    width=as_float(text_node.attrib.get("width")),
                    height=as_float(text_node.attrib.get("height")),
                    font=font_id,
                    family=spec.family,
                    color=spec.color,
                    text=text,
                )
            )
    return fonts, spans


def group_by_line(spans: list[TextSpan], *, y_tolerance: float) -> list[list[TextSpan]]:
    groups: list[list[TextSpan]] = []
    for span in sorted(spans, key=lambda item: (item.page, item.top, item.left)):
        if not groups:
            groups.append([span])
            continue
        current = groups[-1]
        current_top = statistics.median(item.top for item in current)
        if span.page == current[-1].page and abs(span.top - current_top) <= y_tolerance:
            current.append(span)
        else:
            groups.append([span])
    return groups


def median_char_width(spans: list[TextSpan]) -> float:
    widths = [span.width / max(len(span.text), 1) for span in spans if span.width > 0 and span.text]
    if not widths:
        return 6.0
    return max(3.0, statistics.median(widths))


def split_line_columns(spans: list[TextSpan], *, column_gap: float) -> list[list[TextSpan]]:
    ordered = sorted(spans, key=lambda item: item.left)
    if not ordered:
        return []
    groups: list[list[TextSpan]] = [[ordered[0]]]
    previous_right = ordered[0].left + ordered[0].width
    for span in ordered[1:]:
        gap = span.left - previous_right
        if gap > column_gap:
            groups.append([span])
        else:
            groups[-1].append(span)
        previous_right = max(previous_right, span.left + span.width)
    return groups


def build_text_from_spans(spans: list[TextSpan], *, preserve_layout: bool) -> str:
    ordered = sorted(spans, key=lambda item: item.left)
    if not ordered:
        return ""
    if not preserve_layout:
        return "".join(span.text for span in ordered).strip()
    char_width = median_char_width(ordered)
    parts = [ordered[0].text]
    previous_right = ordered[0].left + ordered[0].width
    for span in ordered[1:]:
        gap = span.left - previous_right
        if gap > char_width * 0.75:
            spaces = max(1, round(gap / char_width))
            parts.append(" " * spaces)
        parts.append(span.text)
        previous_right = max(previous_right, span.left + span.width)
    return "".join(parts).rstrip()


def is_code_span(span: TextSpan, code_font_substrings: tuple[str, ...]) -> bool:
    family = span.family.lower()
    return any(item.lower() in family for item in code_font_substrings)


def recover_lines(
    spans: list[TextSpan],
    *,
    code_font_substrings: tuple[str, ...],
    y_tolerance: float,
    column_gap: float,
) -> tuple[list[RecoveredLine], list[RecoveredLine]]:
    all_lines: list[RecoveredLine] = []
    code_lines: list[RecoveredLine] = []
    for line_spans in group_by_line(spans, y_tolerance=y_tolerance):
        page = line_spans[0].page
        top = statistics.median(item.top for item in line_spans)
        left = min(item.left for item in line_spans)
        right = max(item.left + item.width for item in line_spans)
        text = build_text_from_spans(line_spans, preserve_layout=False)
        fonts = sorted({item.family for item in line_spans if item.family})
        colors = sorted({item.color for item in line_spans if item.color})
        key = stable_key("pdfline", page, round(top, 2), round(left, 2), content_hash(text))
        all_lines.append(
            RecoveredLine(
                key=key,
                page=page,
                top=top,
                left=left,
                right=right,
                text=text,
                sourceKind="pdf_text_layer",
                fonts=fonts,
                colors=colors,
                metadata={"authority": AUTHORITY},
            )
        )

        code_spans = [span for span in line_spans if is_code_span(span, code_font_substrings)]
        if not code_spans:
            continue
        for segment in split_line_columns(code_spans, column_gap=column_gap):
            segment_text = build_text_from_spans(segment, preserve_layout=True)
            if not segment_text.strip():
                continue
            segment_left = min(item.left for item in segment)
            segment_right = max(item.left + item.width for item in segment)
            fonts = sorted({item.family for item in segment if item.family})
            colors = sorted({item.color for item in segment if item.color})
            key = stable_key("pdfcodeline", page, round(top, 2), round(segment_left, 2), content_hash(segment_text))
            code_lines.append(
                RecoveredLine(
                    key=key,
                    page=page,
                    top=top,
                    left=segment_left,
                    right=segment_right,
                    text=segment_text,
                    sourceKind="pdf_code_font_line",
                    fonts=fonts,
                    colors=colors,
                    metadata={"authority": AUTHORITY},
                )
            )
    return all_lines, code_lines


def assign_column_clusters(lines: list[RecoveredLine], *, tolerance: float) -> dict[str, int]:
    by_page: dict[int, list[RecoveredLine]] = {}
    for line in lines:
        by_page.setdefault(line.page, []).append(line)
    clusters: dict[str, int] = {}
    for page, page_lines in by_page.items():
        centers: list[float] = []
        for line in sorted(page_lines, key=lambda item: (item.left, item.top)):
            assigned = None
            for idx, center in enumerate(centers):
                if abs(line.left - center) <= tolerance:
                    assigned = idx
                    centers[idx] = (center + line.left) / 2
                    break
            if assigned is None:
                centers.append(line.left)
                assigned = len(centers) - 1
            clusters[line.key] = assigned
    return clusters


def drop_probable_line_number(line: str) -> str:
    return re.sub(r"^\s*\d{1,4}\s+(?=\S)", "", line)


def infer_language(text: str) -> str:
    if PYTHON_SPECIFIC_RE.search(text) or (PYTHON_HINT_RE.search(text) and not LEAN_SPECIFIC_RE.search(text)):
        return "python"
    if LEAN_HINT_RE.search(text) or LEAN_SPECIFIC_RE.search(text):
        return "lean4"
    if ">>>" in text:
        return "python"
    return "unknown"


def validate_python(text: str) -> tuple[str, str]:
    try:
        ast.parse(text)
    except SyntaxError as exc:
        return "failed", f"{exc.__class__.__name__}: {exc}"
    return "passed", "python ast.parse accepted candidate"


def validate_lean(text: str, *, preamble: str, timeout: int, cwd: Path) -> tuple[str, str]:
    with tempfile.TemporaryDirectory(prefix="pdf-recovered-lean-") as tmp:
        path = Path(tmp) / "Candidate.lean"
        path.write_text((preamble.strip() + "\n\n" if preamble.strip() else "") + text, encoding="utf-8")
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(path)],
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
        return "failed", re.sub(r"\s+", " ", output).strip()[:800]


def recover_code_blocks(
    code_lines: list[RecoveredLine],
    *,
    column_tolerance: float,
    vertical_gap: float,
    drop_line_numbers: bool,
    check_lean: bool,
    lean_preamble: str,
    lean_timeout: int,
    check_python: bool,
) -> list[RecoveredCodeBlock]:
    clusters = assign_column_clusters(code_lines, tolerance=column_tolerance)
    grouped: dict[tuple[int, int], list[RecoveredLine]] = {}
    for line in code_lines:
        grouped.setdefault((line.page, clusters[line.key]), []).append(line)

    blocks: list[RecoveredCodeBlock] = []
    for (page, column), lines in sorted(grouped.items()):
        current: list[RecoveredLine] = []
        previous_top: float | None = None

        def flush() -> None:
            if not current:
                return
            base_left = min(line.left for line in current)
            raw_lines = []
            for line in current:
                indent = max(0, round((line.left - base_left) / 6.0))
                raw_lines.append((" " * indent) + line.text)
            if drop_line_numbers:
                raw_lines = [drop_probable_line_number(line) for line in raw_lines]
            text = "\n".join(raw_lines).strip()
            if not text:
                return
            language = infer_language(text)
            if language == "unknown":
                return
            status = "not_checked"
            message = "candidate extracted but not validated"
            if language == "python" and check_python:
                status, message = validate_python(text)
            elif language == "lean4" and check_lean:
                status, message = validate_lean(
                    text,
                    preamble=lean_preamble,
                    timeout=lean_timeout,
                    cwd=repo_root(),
                )
            line_start = len(blocks) + 1
            key = stable_key("pdfcode", page, column, current[0].top, content_hash(text))
            blocks.append(
                RecoveredCodeBlock(
                    key=key,
                    language=language,
                    pageStart=current[0].page,
                    pageEnd=current[-1].page,
                    lineStart=line_start,
                    lineEnd=line_start + len(current) - 1,
                    left=min(line.left for line in current),
                    right=max(line.right for line in current),
                    text=text,
                    validationStatus=status,
                    validationMessage=message,
                    metadata={
                        "authority": AUTHORITY,
                        "page": page,
                        "column": column,
                        "topStart": current[0].top,
                        "topEnd": current[-1].top,
                        "sourceLineKeys": [line.key for line in current],
                    },
                )
            )

        for line in sorted(lines, key=lambda item: item.top):
            if previous_top is not None and line.top - previous_top > vertical_gap:
                flush()
                current = []
            current.append(line)
            previous_top = line.top
        flush()
    return blocks


def recovered_text_markdown(lines: list[RecoveredLine]) -> str:
    out: list[str] = [
        "<!-- Reconstructed from PDF text coordinates. This is not original TeX source. -->",
        "",
    ]
    previous_page: int | None = None
    for line in sorted(lines, key=lambda item: (item.page, item.top, item.left)):
        if line.page != previous_page:
            if previous_page is not None:
                out.append("")
            out.append(f"<!-- page {line.page} -->")
            previous_page = line.page
        out.append(line.text)
    return "\n".join(out).rstrip() + "\n"


def emit_code_files(blocks: list[RecoveredCodeBlock], output: Path) -> dict[str, int]:
    counts = {"lean4": 0, "python": 0}
    for idx, block in enumerate(blocks, start=1):
        if block.language not in counts:
            continue
        counts[block.language] += 1
        subdir = output / ("recovered_lean" if block.language == "lean4" else "recovered_python")
        suffix = ".lean" if block.language == "lean4" else ".py"
        path = subdir / f"block_{idx:04d}_p{block.pageStart:03d}_{block.language}{suffix}"
        path.parent.mkdir(parents=True, exist_ok=True)
        header = (
            f"-- Recovered from PDF text layer; not original source; {block.validationStatus}: "
            f"{block.validationMessage}\n"
            if block.language == "lean4"
            else f"# Recovered from PDF text layer; not original source; {block.validationStatus}: "
            f"{block.validationMessage}\n"
        )
        path.write_text(header + block.text + "\n", encoding="utf-8")
    return counts


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--pdf", type=Path, help="PDF file to convert with pdftohtml -xml.")
    source.add_argument("--xml", type=Path, help="Existing pdftohtml -xml output.")
    parser.add_argument("--output", type=Path, required=True, help="Recovery output directory.")
    parser.add_argument("--xml-work-dir", type=Path, default=Path("artifacts/alexandria/pdf_xml_recovery"))
    parser.add_argument("--first-page", type=int, default=0, help="First PDF page passed to pdftohtml; 0 means default.")
    parser.add_argument("--last-page", type=int, default=0, help="Last PDF page passed to pdftohtml; 0 means default.")
    parser.add_argument("--code-font", action="append", default=["JuliaMono"], help="Substring identifying code fonts.")
    parser.add_argument("--y-tolerance", type=float, default=3.0)
    parser.add_argument("--column-gap", type=float, default=48.0)
    parser.add_argument("--column-tolerance", type=float, default=80.0)
    parser.add_argument("--vertical-gap", type=float, default=28.0)
    parser.add_argument("--drop-line-numbers", action="store_true", default=True)
    parser.add_argument("--keep-line-numbers", action="store_false", dest="drop_line_numbers")
    parser.add_argument("--check-lean", action="store_true")
    parser.add_argument("--lean-preamble", default="")
    parser.add_argument("--lean-timeout", type=int, default=30)
    parser.add_argument("--no-check-python", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    output = normalize_user_path(str(args.output), root)
    output.mkdir(parents=True, exist_ok=True)
    if args.xml:
        xml_path = normalize_user_path(str(args.xml), root)
        source_path = xml_path
    else:
        pdf = normalize_user_path(str(args.pdf), root)
        xml_base = normalize_user_path(str(args.xml_work_dir), root) / pdf.stem
        xml_path = run_pdftohtml_xml(
            pdf,
            xml_base,
            first_page=max(0, int(args.first_page)),
            last_page=max(0, int(args.last_page)),
        )
        source_path = pdf

    fonts, spans = load_xml(xml_path)
    lines, code_lines = recover_lines(
        spans,
        code_font_substrings=tuple(args.code_font),
        y_tolerance=max(0.5, float(args.y_tolerance)),
        column_gap=max(1.0, float(args.column_gap)),
    )
    blocks = recover_code_blocks(
        code_lines,
        column_tolerance=max(1.0, float(args.column_tolerance)),
        vertical_gap=max(1.0, float(args.vertical_gap)),
        drop_line_numbers=args.drop_line_numbers,
        check_lean=args.check_lean,
        lean_preamble=args.lean_preamble,
        lean_timeout=max(1, int(args.lean_timeout)),
        check_python=not args.no_check_python,
    )

    line_rows = [asdict(line) for line in lines]
    code_line_rows = [asdict(line) for line in code_lines]
    block_rows = [asdict(block) for block in blocks]
    counts = {
        "recovered_pdf_lines": write_jsonl(output / "recovered_pdf_lines.jsonl", line_rows),
        "recovered_pdf_code_lines": write_jsonl(output / "recovered_pdf_code_lines.jsonl", code_line_rows),
        "recovered_pdf_code_blocks": write_jsonl(output / "recovered_pdf_code_blocks.jsonl", block_rows),
    }
    output.joinpath("recovered_text.md").write_text(recovered_text_markdown(lines), encoding="utf-8")
    output.joinpath("recovered_text.tex").write_text(
        "% Reconstructed from PDF text coordinates. This is not original TeX source.\n"
        + recovered_text_markdown(lines),
        encoding="utf-8",
    )
    emitted = emit_code_files(blocks, output)
    validation_counts: dict[str, int] = {}
    language_counts: dict[str, int] = {}
    for block in blocks:
        validation_counts[block.validationStatus] = validation_counts.get(block.validationStatus, 0) + 1
        language_counts[block.language] = language_counts.get(block.language, 0) + 1
    manifest = {
        "schema": f"{SCHEMA}.manifest",
        "source": source_path.as_posix(),
        "xml": xml_path.as_posix(),
        "output": output.as_posix(),
        "authority": AUTHORITY,
        "counts": counts,
        "fontSpecs": len(fonts),
        "textSpans": len(spans),
        "codeFontSubstrings": args.code_font,
        "languages": language_counts,
        "validationStatuses": validation_counts,
        "emittedCodeFiles": emitted,
        "notes": [
            "Exact original TeX/Lean source cannot be recovered from a PDF text layer alone.",
            "Recovered Lean fragments are candidates until accepted by lake env lean.",
            "Recovered Python fragments are syntax candidates when ast.parse passes.",
        ],
    }
    output.joinpath("manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "[pdf-source-recovery] "
        f"spans={len(spans)} lines={len(lines)} codeLines={len(code_lines)} "
        f"blocks={len(blocks)} languages={language_counts} statuses={validation_counts} "
        f"output={output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
