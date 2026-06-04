#!/usr/bin/env python3
"""Shadow Cone Scanner — scan `:= by sorry` declarations and build ShadowCone records.

For each shadow candidate:
  1. Extract terms, constants, theorem names.
  2. Map constants to de Bruijn / InfoTree declaration nodes.
  3. Compute past cone: dependencies that support the shadow.
  4. Compute future cone: declarations blocked by the shadow.
  5. Score attachment:
       no incidence       → roaming
       one-sided incidence → incident
       two-sided incidence → paired
       proof exists        → integrated
       contradiction found → rejected

Output:
  - artifacts/shadow_cones/shadows.jsonl   — per-shadow records
  - artifacts/shadow_cones/summary.json    — summary statistics
  - artifacts/shadow_cones/ranked.txt      — human-readable ranking
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
INFO_GEOMETRY = REPO / "lean" / "InfoGeometry"

# Regex patterns
COMMENT_RE = re.compile(r'--.*$|/\*.*?\*/|/\-\-.*?\-/', re.DOTALL | re.MULTILINE)
SORRY_RE = re.compile(r':=\s*by\s+sorry')
DECL_RE = re.compile(r'(theorem|def)\s+(\w+)')
IMPORT_RE = re.compile(r'^import\s+(\S+)', re.MULTILINE)

# Known ShadowKind mapping
KIND_KEYWORDS: dict[str, str] = {
    'sorry': 'sorryDebt',
    'missing': 'missingPremise',
    'bridge': 'overclaimedBridge',
    'archetype': 'archetypeRecurrence',
    'failed': 'failedSynthesis',
    'analogy': 'boundaryAnalogy',
    'conjecture': 'roamingConjecture',
}


def strip_comments(text: str) -> str:
    return COMMENT_RE.sub('', text)


def compute_dependency_graph() -> dict[str, set[str]]:
    """Build a simple dependency graph from import statements."""
    deps: dict[str, set[str]] = {}
    for root, _dirs, files in os.walk(INFO_GEOMETRY):
        for f in files:
            if not f.endswith('.lean'):
                continue
            path = Path(root) / f
            rel = str(path.relative_to(INFO_GEOMETRY))
            module = rel.replace('.lean', '').replace('/', '.')
            try:
                content = path.read_text(encoding='utf-8')
            except Exception:
                continue
            deps[module] = set()
            for m in IMPORT_RE.finditer(content):
                dep = m.group(1)
                deps[module].add(dep)
    return deps


def compute_declaration_map() -> dict[str, str]:
    """Map declaration names to their module paths."""
    decl_map: dict[str, str] = {}
    for root, _dirs, files in os.walk(INFO_GEOMETRY):
        for f in files:
            if not f.endswith('.lean'):
                continue
            path = Path(root) / f
            rel = str(path.relative_to(INFO_GEOMETRY))
            try:
                content = path.read_text(encoding='utf-8')
            except Exception:
                continue
            no_comments = strip_comments(content)
            for m in DECL_RE.finditer(no_comments):
                decl_map[m.group(2)] = rel
    return decl_map


def compute_past_cone(
    decl_name: str,
    file_content: str,
    decl_map: dict[str, str],
    deps: dict[str, set[str]],
    max_depth: int = 3,
) -> list[str]:
    """Compute the past cone: declarations that feed into this shadow."""
    incidences: list[str] = []
    seen: set[str] = set()
    
    # Extract terms from the context around the sorry
    no_comments = strip_comments(file_content)
    names = set(DECL_RE.findall(no_comments))
    for (_, name) in names:
        if name in decl_map and name not in seen:
            seen.add(name)
            incidences.append(f"{decl_map[name]}:{name}")
    
    # Add module-level dependencies
    current_module = "unknown"
    for m in IMPORT_RE.finditer(file_content):
        dep = m.group(1)
        if dep not in seen:
            seen.add(dep)
            incidences.append(f"import:{dep}")
    
    return incidences[:50]  # Limit to top 50


def compute_future_cone(
    decl_name: str,
    decl_map: dict[str, str],
    deps: dict[str, set[str]],
    max_depth: int = 2,
) -> list[str]:
    """Compute the future cone: declarations blocked by this shadow."""
    incidences: list[str] = []
    seen: set[str] = set()
    
    # Find declarations that might depend on this one
    for module, module_deps in deps.items():
        if decl_name.lower() in module.lower():
            if module not in seen:
                seen.add(module)
                incidences.append(module)
        for dep in module_deps:
            if decl_name.lower() in dep.lower():
                if module not in seen:
                    seen.add(module)
                    incidences.append(module)
    
    return incidences[:30]  # Limit to top 30


def classify_shadow_kind(decl_name: str, context: str) -> str:
    """Classify the shadow kind based on context."""
    ctx_lower = (decl_name + ' ' + context).lower()
    for keyword, kind in KIND_KEYWORDS.items():
        if keyword in ctx_lower:
            return kind
    return 'sorryDebt'


def compute_priority(past: list[str], future: list[str]) -> int:
    """Compute priority score from incidence counts."""
    return len(past) * 5 + len(future) * 10


def compute_status(past: list[str], future: list[str]) -> str:
    """Determine shadow status from incidences."""
    if not past and not future:
        return 'roaming'
    elif past and future:
        return 'paired'
    elif past or future:
        return 'incident'
    return 'roaming'


def scan_shadows() -> list[dict]:
    """Scan the entire repository for `:= by sorry` shadows."""
    shadows = []
    
    decl_map = compute_declaration_map()
    deps = compute_dependency_graph()
    
    for root, _dirs, files in os.walk(INFO_GEOMETRY):
        for f in sorted(files):
            if not f.endswith('.lean'):
                continue
            path = Path(root) / f
            rel = str(path.relative_to(INFO_GEOMETRY))
            
            try:
                content = path.read_text(encoding='utf-8')
            except Exception:
                continue
            
            no_comments = strip_comments(content)
            lines = content.split('\n')
            
            for m in SORRY_RE.finditer(no_comments):
                line_num = content[:m.start()].count('\n') + 1
                
                # Find declaration name
                before = content[:m.start()]
                decls = list(DECL_RE.finditer(before))
                decl_name = decls[-1].group(2) if decls else f"anonymous_{line_num}"
                
                # Get context (doc comment)
                ctx_start = max(0, m.start() - 300)
                ctx_before = content[ctx_start:m.start()]
                desc_match = re.search(r'/\-\-(.*?)\-/', ctx_before, re.DOTALL)
                context = desc_match.group(1).strip() if desc_match else ''
                context = re.sub(r'\s+', ' ', context).strip()[:200]
                
                # Compute incidences
                past = compute_past_cone(decl_name, content, decl_map, deps)
                future = compute_future_cone(decl_name, decl_map, deps)
                
                # Classify
                kind = classify_shadow_kind(decl_name, context)
                status = compute_status(past, future)
                priority = compute_priority(past, future)
                
                # Unique hash
                shadow_id = hashlib.sha256(
                    f'{rel}:{line_num}:{decl_name}'.encode()
                ).hexdigest()[:12]
                
                shadow = {
                    'id': shadow_id,
                    'file': rel,
                    'line': line_num,
                    'apex_name': decl_name,
                    'kind': kind,
                    'status': status,
                    'priority': priority,
                    'past_count': len(past),
                    'future_count': len(future),
                    'past_incidences': past[:10],
                    'future_incidences': future[:10],
                    'context': context,
                    'obstruction': None,
                }
                shadows.append(shadow)
    
    # Sort by priority
    shadows.sort(key=lambda s: s['priority'], reverse=True)
    return shadows


def write_outputs(shadows: list[dict]) -> None:
    """Write shadow cone records and summary."""
    out_dir = REPO / 'artifacts' / 'shadow_cones'
    out_dir.mkdir(parents=True, exist_ok=True)
    
    # Per-shadow JSONL
    with open(out_dir / 'shadows.jsonl', 'w') as f:
        for s in shadows:
            f.write(json.dumps(s, sort_keys=True) + '\n')
    
    # Summary statistics
    by_status = defaultdict(int)
    by_kind = defaultdict(int)
    by_module = defaultdict(int)
    
    for s in shadows:
        by_status[s['status']] += 1
        by_kind[s['kind']] += 1
        top_dir = s['file'].split('/')[0]
        by_module[top_dir] += 1
    
    summary = {
        'generated_at': datetime.now(timezone.utc).isoformat(),
        'total_shadows': len(shadows),
        'by_status': dict(by_status),
        'by_kind': dict(by_kind),
        'by_module': dict(by_module),
        'top_10': [
            {'file': s['file'], 'line': s['line'], 'apex': s['apex_name'],
             'status': s['status'], 'priority': s['priority'],
             'past': s['past_count'], 'future': s['future_count']}
            for s in shadows[:10]
        ],
    }
    
    with open(out_dir / 'summary.json', 'w') as f:
        json.dump(summary, f, indent=2)
    
    # Human-readable ranking
    with open(out_dir / 'ranked.txt', 'w') as f:
        f.write(f"=== SHADOW CONE SCAN ===\n")
        f.write(f"Generated: {summary['generated_at']}\n")
        f.write(f"Total shadows: {len(shadows)}\n\n")
        
        f.write(f"By status:\n")
        for k, v in sorted(by_status.items()):
            f.write(f"  {k}: {v}\n")
        f.write(f"\nBy kind:\n")
        for k, v in sorted(by_kind.items()):
            f.write(f"  {k}: {v}\n")
        f.write(f"\nBy module:\n")
        for k, v in sorted(by_module.items()):
            f.write(f"  {k}: {v}\n")
        
        f.write(f"\n=== TOP 20 SHADOWS BY PRIORITY ===\n")
        for i, s in enumerate(shadows[:20], 1):
            f.write(f"\n{i}. [{s['status']}] {s['file']}:{s['line']}  {s['apex_name']}\n")
            f.write(f"   Kind: {s['kind']}  Score: {s['priority']}\n")
            f.write(f"   Past: {s['past_count']}  Future: {s['future_count']}\n")
            if s['context']:
                f.write(f"   {s['context'][:120]}\n")


def main():
    shadows = scan_shadows()
    write_outputs(shadows)
    
    by_status = defaultdict(int)
    for s in shadows:
        by_status[s['status']] += 1
    
    print(f"Scanned {len(shadows)} shadows")
    for k, v in sorted(by_status.items()):
        print(f"  {k}: {v}")
    print(f"Output: artifacts/shadow_cones/")


if __name__ == '__main__':
    main()
