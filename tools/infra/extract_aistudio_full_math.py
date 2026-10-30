#!/usr/bin/env python3
"""Extract a native AI Studio export without treating generated math as proved.

Keep source text and attachment bytes; index explicit TeX and inline-code spans.
Ordinary prose mathematics remains available in the complete transcript.
"""
import argparse
import base64
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def spans(text):
    """Yield fenced code, TeX delimiters, and inline code with source offsets."""
    token = re.compile(r"(?m)^[ \t]*(`{3,}|~{3,})([^\n]*)\n|\$\$|(?<!\\)\$|\\\[|\\\(|`+")
    pos = 0
    while match := token.search(text, pos):
        opening = match.group(0)
        if match.group(1):
            fence = match.group(1)
            end = re.search(r"(?m)^[ \t]*" + re.escape(fence[0]) +
                            "{" + str(len(fence)) + r",}[ \t]*(?:\n|$)", text[match.end():])
            close_start = match.end() + end.start() if end else len(text)
            stop = match.end() + end.end() if end else len(text)
            kind, language = 'code', match.group(2).strip()
        else:
            delimiter = {'\\[': '\\]', '\\(': '\\)'}.get(opening, opening)
            end = re.search(r'(?<!\\)' + re.escape(delimiter), text[match.end():])
            close_start = match.end() + end.start() if end else len(text)
            stop = match.end() + end.end() if end else len(text)
            kind = 'inline_code' if opening.startswith('`') else 'tex'
            language = ''
        yield {'kind': kind, 'language': language, 'start': match.start(),
               'end': stop, 'line': text.count('\n', 0, match.start()) + 1,
               'closed': end is not None, 'text': text[match.end():close_start]}
        pos = stop


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    raw = args.source.read_bytes()
    data = json.loads(raw)
    turns = data['chunkedPrompt']['chunks']
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    documents, attachments, parts_checks = [], [], []
    system = data.get('systemInstruction', {})
    if system:
        documents.append({'turn': 0, 'role': 'system', 'origin': 'systemInstruction',
                          'text': system.get('text', '') or ''.join(p.get('text', '') for p in system.get('parts', []))})
    for i, turn in enumerate(turns, 1):
        body = turn.get('text', '')
        parts = ''.join(p.get('text', '') for p in turn.get('parts', []))
        if parts:
            parts_checks.append({'turn': i, 'matches_text': parts == body})
        documents.append({'turn': i, 'role': turn.get('role'), 'origin': 'text',
                          'timestamp': turn.get('createTime'), 'text': body or parts})
        if file := turn.get('inlineFile'):
            content = base64.b64decode(file['data'], validate=True)
            path = out / f'attachment_turn_{i:04d}.txt'
            path.write_bytes(content)
            attachments.append({'turn': i, 'name': file.get('displayName'),
                                'mime': file.get('mimeType'), 'bytes': len(content),
                                'sha256': hashlib.sha256(content).hexdigest(), 'file': path.name})
            if file.get('mimeType', '').startswith('text/'):
                documents.append({'turn': i, 'role': turn.get('role'),
                                  'origin': 'attachment', 'text': content.decode('utf-8')})
    def jsonl(name, rows):
        (out / name).write_text(''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in rows))
    jsonl('turns.jsonl', documents)
    transcript = ''.join(f"\n===== TURN {d['turn']:04d} | {d['role']} | {d['origin']} =====\n" + d['text'] + '\n' for d in documents)
    (out / 'full_chat.txt').write_text(transcript)
    records = []
    for document in documents:
        body = document['text']
        extracted = ([{'kind': 'code', 'language': 'lean', 'start': 0,
                       'end': len(body), 'line': 1, 'closed': True, 'text': body}]
                     if body.lstrip().startswith('import Mathlib') else spans(body))
        for span in extracted:
            records.append({**{k: document[k] for k in ('turn', 'role', 'origin')}, **span})
    jsonl('math_and_code.jsonl', records)
    code = [r for r in records if r['kind'] == 'code']
    tex = [r for r in records if r['kind'] == 'tex']
    jsonl('code_blocks.jsonl', code)
    jsonl('formulas.jsonl', tex)
    declarations = []
    for index, block in enumerate(code, 1):
        for match in re.finditer(r'(?m)^\s*(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev|structure|class|example)\s+([^\s:(]+)', block['text']):
            declarations.append({'turn': block['turn'], 'origin': block['origin'],
                                 'block': index, 'kind': match.group(1),
                                 'name': match.group(2),
                                 'line_in_block': block['text'].count('\n', 0, match.start()) + 1})
    jsonl('declarations.jsonl', declarations)
    (out / 'all_formulas.tex.txt').write_text('\n\n'.join(
        f"% Turn {r['turn']}, {r['origin']}, line {r['line']}\n{r['text']}" for r in tex))
    (out / 'all_code.txt').write_text('\n\n'.join(
        f"===== Turn {r['turn']}, {r['origin']}, line {r['line']}, language={r['language']} =====\n{r['text']}" for r in code))
    manifest = {'source': str(args.source), 'source_bytes': len(raw),
                'source_sha256': hashlib.sha256(raw).hexdigest(),
                'turns': len(turns), 'roles': dict(Counter(t.get('role') for t in turns)),
                'documents': len(documents), 'attachments': attachments,
                'counts': dict(Counter(r['kind'] for r in records)),
                'code_languages': dict(Counter(r['language'] for r in code)),
                'declaration_occurrences': len(declarations),
                'unclosed_spans': [dict(turn=r['turn'], line=r['line'], kind=r['kind']) for r in records if not r['closed']],
                'streaming_parts_checks': parts_checks,
                'scope': 'Complete exported text and embedded text attachments. Explicit TeX and code indexed; prose mathematics preserved in full_chat.txt. No claim of mathematical or Lean verification.'}
    (out / 'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(manifest, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
