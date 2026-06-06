#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

DEFAULT_MIRROR = Path(__file__).resolve().parents[2] / 'external_refs' / 'pyw'


def corpus_root(path: str | None) -> Path:
    return Path(path) if path else DEFAULT_MIRROR


def load(root: Path):
    index = root / 'keyword_index.json'
    full_index = root / 'index.json'
    kw = json.loads(index.read_text(encoding='utf-8'))
    full = json.loads(full_index.read_text(encoding='utf-8'))
    return kw, full


def query(q: str, limit: int, root: Path):
    kw, full = load(root)
    qterms = [t.lower() for t in q.split() if t.strip()]
    decls = full['declarations']
    results = []
    for d in decls:
        hay = " ".join(
            str(d.get(k, "")) for k in ("file", "kind", "module", "name", "doc", "type", "context")
        ).lower()
        score = sum(1 for t in qterms if t in hay)
        if score:
            results.append((score, d))
    results.sort(key=lambda x: (-x[0], x[1]['file'], x[1].get('line', 0), x[1]['name']))
    return results[:limit]


def list_corpora(base: Path) -> list[Path]:
    out = []
    if not base.exists():
        return out
    for p in sorted(base.iterdir()):
        if p.is_dir() and (p / 'index.json').exists() and (p / 'keyword_index.json').exists():
            out.append(p)
    return out


def main():
    ap = argparse.ArgumentParser(description='Query a mirrored external corpus by keyword or declaration name.')
    ap.add_argument('query', nargs='*', help='Query keywords / declaration fragments')
    ap.add_argument('--corpus', help='Mirror root (e.g. external_refs/pyw)')
    ap.add_argument('--list', action='store_true', help='List available mirrored corpora under external_refs')
    ap.add_argument('--limit', type=int, default=20)
    args = ap.parse_args()

    if args.list:
        base = DEFAULT_MIRROR.parent
        corpora = list_corpora(base)
        print(json.dumps({'base': str(base), 'corpora': [str(p) for p in corpora]}, indent=2, ensure_ascii=False))
        return

    if not args.query:
        ap.error('query terms are required unless --list is used')

    q = ' '.join(args.query)
    root = corpus_root(args.corpus)
    results = query(q, args.limit, root)
    print(json.dumps({
        'corpus': str(root),
        'query': q,
        'limit': args.limit,
        'results': [
            {'score': s, **d}
            for s, d in results
        ]
    }, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
