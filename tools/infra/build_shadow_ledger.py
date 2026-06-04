#!/usr/bin/env python3
"""Build the shadow ledger — a ranked index of all `:= by sorry` debt.

Outputs:
  - artifacts/shadow_ledger/shadows.jsonl    — per-shadow entries
  - artifacts/shadow_ledger/ledger.json       — summary report
  - artifacts/shadow_ledger/ranked.txt        — human-readable ranking
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
INFO_GEOMETRY = REPO / "lean" / "InfoGeometry"

# ── 1. Scan ──────────────────────────────────────────────────────────

COMMENT_RE = re.compile(r'--.*$|/\*.*?\*/|/\-\-.*?\-/', re.DOTALL | re.MULTILINE)
SORRY_RE = re.compile(r':=\s*by\s+sorry')
DECL_RE = re.compile(r'(theorem|def)\s+(\w+)')

CACHED_DOWNSTREAM: dict[str, list[str]] = {}


def strip_comments(text: str) -> str:
    return COMMENT_RE.sub('', text)


def count_downstream(module: str, decl: str) -> int:
    """Count how many declarations reference this shadow."""
    # Simple text search across the repo
    count = 0
    for root, _dirs, files in os.walk(INFO_GEOMETRY):
        for f in files:
            if not f.endswith('.lean'):
                continue
            path = Path(root) / f
            try:
                content = path.read_text()
            except Exception:
                continue
            # Count occurrences of decl name in other files
            if path == module:
                continue
            count += content.count(decl)
    return count


def get_git_age(filepath: Path) -> int:
    """Get number of commits since file was created (proxy for age)."""
    try:
        result = subprocess.run(
            ['git', 'log', '--oneline', '--follow', '--format=%H', str(filepath.relative_to(REPO))],
            capture_output=True, text=True, cwd=REPO, timeout=10
        )
        return len(result.stdout.strip().split('\n')) if result.stdout.strip() else 0
    except Exception:
        return 0


def build_ledger() -> dict:
    shadows = []
    total = 0
    
    for root, _dirs, files in os.walk(INFO_GEOMETRY):
        for f in sorted(files):
            if not f.endswith('.lean'):
                continue
            path = Path(root) / f
            rel = path.relative_to(REPO / 'lean')
            module = str(rel).replace('.lean', '')
            mod_path = str(rel)
            
            try:
                content = path.read_text(encoding='utf-8')
            except Exception:
                continue
            
            no_comments = strip_comments(content)
            lines = content.split('\n')
            
            for m in SORRY_RE.finditer(no_comments):
                total += 1
                # Find line number
                line_num = content[:m.start()].count('\n') + 1
                
                # Find declaration name
                before = content[:m.start()]
                decls = list(DECL_RE.finditer(before))
                decl_name = decls[-1].group(2) if decls else 'unknown'
                
                # Get description (first doc comment above)
                ctx_start = max(0, m.start() - 200)
                ctx_before = content[ctx_start:m.start()]
                desc_match = re.search(r'/\-\-(.*?)\-/', ctx_before, re.DOTALL)
                description = desc_match.group(1).strip() if desc_match else ''
                # Clean description
                description = re.sub(r'\s+', ' ', description).strip()[:200]
                
                # Downstream count
                downstream = count_downstream(path, decl_name)
                
                # Age proxy
                age = get_git_age(path)
                
                # Hash for dedup
                hash_id = hashlib.sha256(f'{module}:{decl_name}:{line_num}'.encode()).hexdigest()[:12]
                
                shadow = {
                    'id': hash_id,
                    'module': mod_path,
                    'file': str(rel),
                    'line': line_num,
                    'declaration': decl_name,
                    'description': description,
                    'downstream_count': downstream,
                    'age_commits': age,
                    'status': 'untouched',
                    'attempts': [],
                    'weight': max(downstream, 1),
                    'priority_score': downstream * 10 + age * 3,
                }
                shadows.append(shadow)
    
    # Sort by priority score
    shadows.sort(key=lambda s: s['priority_score'], reverse=True)
    
    # Build summary
    unresolved = [s for s in shadows if s['status'] != 'resolved']
    
    # Distribution by module
    by_module = defaultdict(list)
    for s in shadows:
        top_dir = s['module'].split('/')[0]
        by_module[top_dir].append(s)
    
    # Top 10 heaviest shadows
    top_10 = shadows[:10]
    
    ledger = {
        'generated_at': datetime.now(timezone.utc).isoformat(),
        'total_shadows': total,
        'unresolved': len(unresolved),
        'resolution_rate': f"{total - len(unresolved)}/{total}",
        'by_module': {k: len(v) for k, v in sorted(by_module.items())},
        'top_10_heaviest': [{
            'file': s['file'],
            'line': s['line'],
            'declaration': s['declaration'],
            'weight': s['weight'],
            'downstream_count': s['downstream_count'],
            'priority_score': s['priority_score'],
            'description': s['description'][:120],
        } for s in top_10],
        'shadows': shadows,
    }
    
    return ledger


def write_outputs(ledger: dict) -> None:
    out_dir = REPO / 'artifacts' / 'shadow_ledger'
    out_dir.mkdir(parents=True, exist_ok=True)
    
    # JSONL per shadow
    with open(out_dir / 'shadows.jsonl', 'w') as f:
        for s in ledger['shadows']:
            f.write(json.dumps(s, sort_keys=True) + '\n')
    
    # Full ledger JSON (without per-shadow details to keep it manageable)
    ledger_summary = {k: v for k, v in ledger.items() if k != 'shadows'}
    ledger_summary['shadow_count'] = len(ledger['shadows'])
    with open(out_dir / 'ledger.json', 'w') as f:
        json.dump(ledger_summary, f, indent=2)
    
    # Human-readable ranking
    with open(out_dir / 'ranked.txt', 'w') as f:
        f.write(f"=== SHADOW LEDGER ===\n")
        f.write(f"Generated: {ledger['generated_at']}\n")
        f.write(f"Total shadows: {ledger['total_shadows']}\n")
        f.write(f"Unresolved: {ledger['unresolved']}\n")
        f.write(f"Resolution rate: {ledger['resolution_rate']}\n\n")
        
        f.write(f"Distribution by module:\n")
        for k, v in sorted(ledger['by_module'].items()):
            f.write(f"  {k}: {v}\n")
        
        f.write(f"\n=== TOP 10 HEAVIEST SHADOWS ===\n")
        for i, s in enumerate(ledger['top_10_heaviest'], 1):
            f.write(f"\n{i}. {s['file']}:{s['line']}  {s['declaration']}\n")
            f.write(f"   Weight: {s['weight']}  Downstream: {s['downstream_count']}\n")
            f.write(f"   Score: {s['priority_score']}\n")
            if s['description']:
                f.write(f"   {s['description'][:120]}\n")


if __name__ == '__main__':
    ledger = build_ledger()
    write_outputs(ledger)
    print(f"Ledger built: {ledger['total_shadows']} shadows, {ledger['unresolved']} unresolved")
    print(f"Top shadow: {ledger['top_10_heaviest'][0]['file']}:{ledger['top_10_heaviest'][0]['line']}  {ledger['top_10_heaviest'][0]['declaration']}")
    print(f"Output: artifacts/shadow_ledger/")
