#!/usr/bin/env python3
"""
Build lightweight declaration-side ExprFingerprint proxies from decls.jsonl.

This is a non-destructive, additive sidecar generator meant for Arango ingestion.
It does NOT claim kernel-level term normalization; it computes structural proxies
from declaration metadata/text until full expr extraction is wired.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Dict, Iterable, List

TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+|\S")
CAMEL_SPLIT_RE = re.compile(r"(?<!^)(?=[A-Z])")


def sha256_hex(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def tokenize(text: str) -> List[str]:
    return TOKEN_RE.findall(text or "")


def binder_depth_proxy(name: str) -> int:
    # Heuristic: namespace depth as proxy for binder/context layering.
    return max(0, name.count("."))


def split_name_atoms(full_name: str) -> List[str]:
    atoms: List[str] = []
    for part in full_name.split("."):
        atoms.extend([x for x in CAMEL_SPLIT_RE.split(part) if x])
    return atoms


def redex_proxy(tokens: List[str]) -> int:
    # Heuristic proxy for syntactic contraction opportunities.
    marks = {"fun", "match", "let", "=>", "by", "simp", "rw"}
    return sum(1 for t in tokens if t in marks)


def kind_one_hot(kind: str) -> Dict[str, int]:
    kinds = ["theorem", "def", "inductive", "structure", "constructor", "axiom", "lemma"]
    return {f"kind_{k}": int(kind == k) for k in kinds}


def process_decl(decl: Dict) -> Dict:
    name = decl.get("name", "")
    module = decl.get("module", "")
    kind = decl.get("kind", "")
    doc = decl.get("doc", "") or ""
    file = decl.get("file", "")
    attrs = decl.get("attrs", []) or []

    atoms = split_name_atoms(name)
    atom_tokens = [a.lower() for a in atoms]
    doc_tokens = [t.lower() for t in tokenize(doc)]
    merged_tokens = atom_tokens + doc_tokens

    counts = {
        "token_count": len(merged_tokens),
        "name_atom_count": len(atom_tokens),
        "doc_token_count": len(doc_tokens),
        "digit_token_count": sum(1 for t in merged_tokens if t.isdigit()),
        "upper_token_count": sum(1 for t in atoms if t.isupper()),
        "redex_proxy": redex_proxy(merged_tokens),
        "binder_depth_proxy": binder_depth_proxy(name),
        "attr_count": len(attrs),
    }

    base_sig = {
        "name": name,
        "module": module,
        "kind": kind,
        "file": file,
        "line": decl.get("line", 0),
        "col": decl.get("column", 0),
        "tokens_head": merged_tokens[:64],
        "counts": counts,
    }
    level0_hash = sha256_hex(json.dumps(base_sig, sort_keys=True, ensure_ascii=False))

    # L1 local patch hash: module + kind + local name stem + features
    local_stem = name.split(".")[-1] if name else ""
    l1_sig = {
        "module": module,
        "kind": kind,
        "local_stem": local_stem,
        "counts": counts,
    }
    level1_hash = sha256_hex(json.dumps(l1_sig, sort_keys=True, ensure_ascii=False))

    out = {
        "schema": "hive.packet.expr_fingerprint.v1",
        "decl_name": name,
        "module": module,
        "kind": kind,
        "file": file,
        "line": decl.get("line", 0),
        "column": decl.get("column", 0),
        "level_0_decl_hash": level0_hash,
        "level_1_local_hash": level1_hash,
        "feature_counts": counts,
        "feature_kind": kind_one_hot(kind),
        "flags": {
            "has_doc": bool(doc.strip()),
            "has_attrs": bool(attrs),
            "unresolved_metavar_proxy": False,
        },
        "provenance": {
            "source": "artifacts/dag/index/decls.jsonl",
            "method": "metadata_proxy_v1",
        },
    }
    return out


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--decls", default="artifacts/dag/index/decls.jsonl")
    ap.add_argument("--out", default="artifacts/dag/index/expr_fingerprints.jsonl")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()

    decls_path = Path(args.decls)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    n = 0
    with out_path.open("w", encoding="utf-8") as w:
        for d in iter_jsonl(decls_path):
            w.write(json.dumps(process_decl(d), ensure_ascii=False) + "\n")
            n += 1
            if args.limit and n >= args.limit:
                break

    print(json.dumps({"ok": True, "written": n, "out": str(out_path)}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
