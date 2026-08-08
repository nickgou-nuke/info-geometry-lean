#!/usr/bin/env python3
"""Stricter extractor: theorem/proposition/lemma/corollary style statements from PDFs.
"""

from __future__ import annotations

import re
import json
import subprocess
from pathlib import Path

ROOT = Path('/tmp/paper_ingest')
OUT_JSON = Path('/home/goutev/auto/proofs/pdf_theorem_strict.json')
OUT_MD = Path('/home/goutev/auto/proofs/pdf_theorem_strict.md')

KEYWORDS = ['Theorem', 'Lemma', 'Proposition', 'Corollary', 'Conjecture', 'Criterion', 'Claim']

HEADING_RE = re.compile(
    r'^\s*'
    r'(?:[0-9]+(?:[.:][0-9]+)*\s+)?'
    r'(' + '|'.join(KEYWORDS) + r')\b'
    r'[^A-Za-z]*\s*(?:\([^)]+\)|\[[^]]+\])?\s*(?:[0-9A-Za-z-]+)?\s*[:\-.]?\s*',
    re.IGNORECASE,
)

# Stop at next heading-like line that likely starts another numbered section/subsection
NEXT_HEADING = re.compile(
    r'^\s*(\d+\.|\w+\.|[A-Z][A-Za-z ]{1,40}:|Appendix|References|Supplementary|Methods|Results|Discussion|Conclusion|Introduction|Acknowledg|Supplementary|Proof|Derivation|Figure|Eq\.?\s*\d+)'
)

def ensure_txt(pdf: Path) -> Path:
    txt = pdf.with_suffix(pdf.suffix + '.txt')
    if txt.exists() and txt.stat().st_size > 50:
        return txt
    subprocess.run(['pdftotext', str(pdf), str(txt)], check=True, timeout=120)
    return txt


def is_noise_line(s: str) -> bool:
    return len(s.strip()) < 3 or s.strip().startswith(('\f', 'Fig', 'Figure', 'FIG.'))


def clean(s: str) -> str:
    s = s.replace('\r', '')
    s = re.sub(r'\n{3,}', '\n\n', s)
    return s.strip()


def is_heading_like(line: str) -> bool:
    return bool(HEADING_RE.match(line))


def stop_line(line: str) -> bool:
    l = line.strip()
    if not l:
        return False
    return bool(NEXT_HEADING.match(l))


def extract(text: str):
    lines = text.split('\n')
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = HEADING_RE.match(line)
        if not m:
            i += 1
            continue

        keyword = m.group(1)
        # keep only strong theorem/proposition-ish headings
        if keyword.lower() not in [k.lower() for k in ['theorem', 'lemma', 'proposition', 'corollary', 'conjecture', 'criterion']]:
            i += 1
            continue

        title_bits = line[m.end():].strip() or '(untitled)'
        heading = ' '.join(line[:m.end()].strip().split())

        j = i + 1
        body_lines = []
        while j < len(lines):
            l2 = lines[j]
            if is_noise_line(l2):
                if body_lines and l2.strip() and l2.strip().startswith('...'):
                    pass
                j += 1
                if not is_noise_line(l2) and not l2.strip():
                    pass
                continue
            if is_heading_like(l2) or stop_line(l2):
                break
            body_lines.append(l2)
            j += 1

        body = clean('\\n'.join(body_lines))
        # ignore tiny fragments
        if body and len(body) > 40:
            out.append({
                'start_line': i + 1,
                'end_line': j,
                'heading': heading,
                'kind': keyword.capitalize(),
                'title': title_bits,
                'statement': body[:4000]
            })
        i = j
    return out


def main():
    all_items = []
    pdfs = sorted(ROOT.glob('*.pdf'))
    for p in pdfs:
        txt = ensure_txt(p)
        text = txt.read_text(errors='ignore')
        hits = extract(text)
        for h in hits:
            all_items.append({
                'paper': p.name,
                'doc': p.name.replace('.pdf', ''),
                **h,
            })

    OUT_JSON.write_text(json.dumps({'source': str(ROOT), 'count': len(all_items), 'items': all_items}, indent=2), encoding='utf-8')

    with OUT_MD.open('w', encoding='utf-8') as f:
        f.write('# PDF theorem/proposition/lemma extraction (strict)\n')
        f.write(f'Total: {len(all_items)}\n\n')
        cur = None
        for it in all_items:
            if it['paper'] != cur:
                cur = it['paper']
                f.write(f'## {cur}\n\n')
            f.write(f"### {it['kind']}: `{it['heading']}`\n")
            f.write(f"- lines: {it['start_line']}-{it['end_line']}\n")
            f.write('- statement:\n')
            f.write('```text\n')
            f.write(it['statement'])
            f.write('\n```\n\n')

    print(f'Extracted {len(all_items)} strict items')
    print(OUT_JSON)
    print(OUT_MD)


if __name__ == '__main__':
    main()
