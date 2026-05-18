#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2] / 'external_refs' / 'pyw'
INDEX = ROOT / 'keyword_index.json'
FULL_INDEX = ROOT / 'index.json'


def load():
    kw = json.loads(INDEX.read_text(encoding='utf-8'))
    full = json.loads(FULL_INDEX.read_text(encoding='utf-8'))
    return kw, full


def query(q: str, limit: int):
    kw, full = load()
    qterms = [t.lower() for t in q.split() if t.strip()]
    decls = full['declarations']
    results = []
    for d in decls:
        hay = f"{d.get('file','')} {d.get('kind','')} {d.get('name','')}".lower()
        score = sum(1 for t in qterms if t in hay)
        if score:
            results.append((score, d))
    results.sort(key=lambda x: (-x[0], x[1]['file'], x[1].get('line', 0), x[1]['name']))
    return results[:limit]


def main():
    ap = argparse.ArgumentParser(description='Query the mirrored pyw external corpus by keyword or declaration name.')
    ap.add_argument('query', nargs='+')
    ap.add_argument('--limit', type=int, default=20)
    args = ap.parse_args()
    q = ' '.join(args.query)
    results = query(q, args.limit)
    print(json.dumps({
        'query': q,
        'limit': args.limit,
        'results': [
            {'score': s, **d}
            for s, d in results
        ]
    }, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
