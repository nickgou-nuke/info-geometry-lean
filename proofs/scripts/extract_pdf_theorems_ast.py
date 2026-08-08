#!/usr/bin/env python3
"""Extract theorem/proposition-style statements from downloaded paper texts.

Inputs: PDF-text files under /tmp/paper_ingest/*.pdf.txt (created by pdftotext).
If a .txt file is missing, it will try to regenerate it from the matching .pdf.
Output: JSON + Markdown report.
"""

from __future__ import annotations

import os
import re
import json
import subprocess
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import List, Optional

ROOT = Path('/tmp/paper_ingest')
OUT_JSON = Path('/home/goutev/auto/proofs/pdf_theorem_extraction.json')
OUT_MD = Path('/home/goutev/auto/proofs/pdf_theorem_extraction.md')

HEADING_RE = re.compile(
    r'^\s*'
    r'(?:(?P<label>(?:Theorem|Lemma|Proposition|Corollary|Conjecture|Axiom|Definition|Hypothesis|Claim|Criterion|Principle|Result|Remark|Remark\w*|Example|Theorem/Lemma|Lemma/Proposition))\b)'
    r'(?:\s*(?:\([^)]+\)|\[[^]]+\]|[0-9]+(?:\.[0-9]+)*)?)?'
    r'\s*[:.-]?\s*$',
    re.IGNORECASE,
)

INLINE_RE = re.compile(
    r'(?:(?:^|[\n\r])\s*(?:' 
    r'(Theorem|Lemma|Proposition|Corollary|Conjecture|Axiom|Definition|Hypothesis|Claim|Criterion|Principle|Result)'
    r')\s*[A-Za-z0-9\-:.()\\/]*)',
    re.MULTILINE,
)

# Some PDFs emit headings like "Theorem 1. …" in the same line with trailing text.
FULL_START_RE = re.compile(
    r'^\s*(Theorem|Lemma|Proposition|Corollary|Conjecture|Axiom|Definition|Hypothesis|Claim|Criterion|Principle|Result)\s*'
    r'([0-9]+(?:\.[0-9]+)*)?\s*[:.)-]?\s*(.*)$',
    re.IGNORECASE,
)

STOP_RE = re.compile(
    r'^\s*(Introduction|Background|Methods|Theory|Model|Discussion|Conclusion|Acknowledgements|Appendix|References)\b',
    re.IGNORECASE,
)

@dataclass
class Extracted:
    paper_file: str
    doc_id: str
    kind: str
    title: str
    heading: str
    body: str
    line_start: int
    line_end: int
    raw: str


def ensure_txt(pdf_path: Path) -> Path:
    txt_path = pdf_path.with_suffix(pdf_path.suffix + '.txt')
    if txt_path.exists() and txt_path.stat().st_size > 0:
        return txt_path

    if not txt_path.exists():
        try:
            subprocess.run(['pdftotext', str(pdf_path), str(txt_path)], check=True, timeout=120, capture_output=True)
            print(f"converted {pdf_path.name}")
        except Exception as exc:
            raise RuntimeError(f'pdftotext failed for {pdf_path}: {exc}')
    return txt_path


def normalize_ws(s: str) -> str:
    s = re.sub(r'\r', '', s)
    s = re.sub(r'\n{3,}', '\n\n', s)
    s = re.sub(r'\s+\n', '\n', s)
    return s.strip()


def extract_blocks(text: str) -> List[Extracted]:
    lines = text.split('\n')
    n = len(lines)
    blocks: List[Extracted] = []
    i = 0
    while i < n:
        raw = lines[i]
        m_full = FULL_START_RE.match(raw)
        if not m_full:
            i += 1
            continue

        kind = m_full.group(1)
        title_num = m_full.group(2) or ''
        title_tail = (m_full.group(3) or '').strip()
        heading = ' '.join([kind, title_num]).strip()
        title = title_tail or '(untitled)'

        # Skip very short lines that are likely section markers only.
        if heading == '' and title == '(untitled)':
            i += 1
            continue

        body_lines = [title_tail] if title_tail else []
        j = i + 1
        while j < n:
            line = lines[j]
            if line.strip() == '':
                body_lines.append('')
                j += 1
                continue

            # stop when next theorem-like heading appears
            if FULL_START_RE.match(line) and len(line.strip()) < 140:
                break
            if HEADING_RE.match(line):
                break
            if STOP_RE.match(line.strip()):
                break

            body_lines.append(line)
            j += 1

        body = '\n'.join(body_lines).strip()
        body = normalize_ws(body)

        # keep only non-empty and not too short
        if body and len(body) > 20:
            blocks.append(Extracted(
                paper_file='',
                doc_id='',
                kind=kind.title(),
                title=title,
                heading=heading,
                body=body,
                line_start=i + 1,
                line_end=j + 1,
                raw='\n'.join(lines[i:j]).strip(),
            ))
        i = j
    return blocks


def sanitize_file_label(path: Path) -> str:
    return path.name.replace('.pdf.txt', '')


def extract_inline_mentions(text: str, paper_file: str, doc_id: str) -> List[Extracted]:
    out: List[Extracted] = []
    for m in INLINE_RE.finditer(text):
        pass
    return out


def main() -> int:
    if not ROOT.exists():
        print(f'ERROR: {ROOT} not found')
        return 1

    extracted: List[Extracted] = []
    pdf_files = sorted(ROOT.glob('*.pdf'))

    if not pdf_files:
        print('No pdf files in /tmp/paper_ingest')

    for pdf in pdf_files:
        try:
            txt = ensure_txt(pdf)
        except Exception as exc:
            print(exc)
            continue

        text = txt.read_text(errors='ignore')
        blocks = extract_blocks(text)
        doc_id = sanitize_file_label(txt)
        for b in blocks:
            b.paper_file = txt.name
            b.doc_id = doc_id
        extracted.extend(blocks)

    out_payload = {
        'source_dir': str(ROOT),
        'files_scanned': [p.name for p in sorted(ROOT.glob('*.pdf'))],
        'count': len(extracted),
        'items': [asdict(e) for e in extracted],
    }
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(out_payload, ensure_ascii=False, indent=2), encoding='utf-8')

    # Markdown summary grouped per paper
    lines = ['# AST-style theorem/proposition extraction from downloaded PDFs', '', f'Total extracted items: `{len(extracted)}`', '']
    by_paper = {}
    for e in extracted:
        by_paper.setdefault(e.doc_id, []).append(e)

    for paper, items in sorted(by_paper.items()):
        lines.append(f"## {paper}")
        lines.append('')
        for e in items:
            lines.append(f"### {e.kind}: `{e.heading}`")
            lines.append(f"- source file: `{e.paper_file}`")
            lines.append(f"- lines: {e.line_start}-{e.line_end}")
            lines.append('')
            lines.append('```text')
            lines.append(e.body[:4000] + (' ...' if len(e.body) > 4000 else ''))
            lines.append('```')
            lines.append('')

    OUT_MD.write_text('\n'.join(lines), encoding='utf-8')

    print(f'scan done: {len(extracted)} candidate items')
    print(f'JSON: {OUT_JSON}')
    print(f'MD: {OUT_MD}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
