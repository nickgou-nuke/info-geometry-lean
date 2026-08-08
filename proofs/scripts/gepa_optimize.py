#!/usr/bin/env python3
"""GEPA: Graph Extraction & Parsing Architecture — declaration-graph passes.

This script runs between ExtractGraph.lean (JSON generation) and ArangoDB
ingestion.  It transforms declaration-graph metadata, optionally canonicalizes
raw proof-graph JSON when the canonicalizer module is available, and flags graph
shapes that may deserve human review. It does not prove or repair Lean theorems.

Usage:
  python3 scripts/gepa_optimize.py < proof_graph.json > proof_graph_optimized.json
  python3 scripts/gepa_optimize.py proof_graph.json proof_graph_optimized.json
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    from tools.lean_graph.canonicalize_proof_graph import canonicalize as _canonicalize
except Exception:  # pragma: no cover - compatibility fallback for older checkouts
    _canonicalize = None


def canonicalize_if_available(decls):
    """Run the repository canonicalizer when present; otherwise return input."""
    if _canonicalize is None:
        summary = {
            "declarations": len(decls),
            "modules": len({d.get("name", "").split(".")[0] for d in decls if d.get("name")}),
            "auto_generated_hint_count": 0,
            "duplicate_edges_removed": 0,
            "files_scanned": 0,
        }
        print("GEPA canonical: skipped (canonicalizer module unavailable)", file=sys.stderr)
        return decls, summary
    return _canonicalize(decls)


def load(path=None):
    if path:
        with open(path, encoding="utf-8") as f:
            return json.load(f)

    if sys.stdin.isatty():
        print("Usage: python3 scripts/gepa_optimize.py < proof_graph.json > proof_graph_optimized.json", file=sys.stderr)
        return None

    raw = sys.stdin.read().strip()
    if not raw:
        print("No input JSON found on stdin.", file=sys.stderr)
        return None
    return json.loads(raw)


def save(data, path=None):
    out = json.dumps(data, indent=2, ensure_ascii=False)
    if path:
        with open(path, "w", encoding="utf-8") as f:
            f.write(out)
    else:
        sys.stdout.write(out)


# ── Pass 1: Normalize ──────────────────────────────────────────────

def pass_normalize(decls):
    """Remove compiler-generated Lean internals from the GEPA stream.

    The raw/canonical audit graph can keep these declarations, but most GEPA
    consumers want a smaller graph focused on user-facing declarations.
    """
    skip_patterns = [
        ".mk.injEq", ".mk.sizeOf_spec", ".noConfusion",
        "._proof_", ".rec.", ".mk.", "._cstage",
    ]
    result = []
    removed = 0
    for d in decls:
        if d.get("auto_generated_hint"):
            removed += 1
            continue
        name = d["name"]
        if any(p in name for p in skip_patterns):
            removed += 1
            continue
        result.append(d)
    print(f"  [normalize] removed {removed} auto-generated decls, {len(result)} remain", file=sys.stderr)
    return result


# ── Pass 2: Classify by module ─────────────────────────────────────

def pass_classify_modules(decls):
    """Tag each declaration with its top-level module."""
    for d in decls:
        d["module"] = d["name"].split(".")[0]
    modules = Counter(d["module"] for d in decls)
    top = sorted(modules.items(), key=lambda kv: (-kv[1], kv[0]))[:10]
    print(f"  [classify] modules={len(modules)} top={top}", file=sys.stderr)
    return decls


# ── Pass 3: Classify by proof style ────────────────────────────────

MATRIX_MODULES = {"TLChain", "YangBaxterQSwap", "ChiralTLDescent"}
TENSOR_MODULES = {"ChiralTensorRecoupling", "ChiralTensorMatrixBridge", "BraidIdealDescent"}
ALGEBRA_MODULES = {
    "ChiralCausalCone", "JonesBraidB3", "B3PresentedGroup",
    "YangBaxterQuotientDescent", "IdealDescentProof",
}


def classify_style(name):
    module = name.split(".")[0]
    if module in MATRIX_MODULES:
        return "matrix_computation"
    if module in TENSOR_MODULES:
        return "tensor_algebra"
    if module in ALGEBRA_MODULES:
        return "algebraic"
    return "unknown"


def pass_classify_style(decls):
    """Tag each declaration with a coarse proof-style hint based on module."""
    for d in decls:
        d["style"] = classify_style(d["name"])
    styles = Counter(d["style"] for d in decls)
    print(f"  [style] {dict(styles)}", file=sys.stderr)
    return decls


# ── Pass 4: Compute reuse score ─────────────────────────────────────

def pass_reuse_score(decls):
    """Count how many other declarations depend on each one."""
    incoming = Counter()
    for d in decls:
        for dep in d.get("deps", []):
            incoming[dep] += 1
    for d in decls:
        d["reused_by"] = incoming.get(d["name"], 0)
    top = [(d["name"], d["reused_by"]) for d in decls if d["reused_by"] > 5]
    top.sort(key=lambda x: -x[1])
    if top:
        print(f"  [reuse] top reused: {top[:5]}", file=sys.stderr)
    return decls


# ── Pass 5: Compute dependency depth ────────────────────────────────

def pass_dependency_depth(decls):
    """Compute a bounded breadth-first dependency depth for each declaration."""
    name_to_deps = {d["name"]: set(d.get("deps", [])) for d in decls}
    all_names = set(name_to_deps.keys())

    for d in decls:
        name = d["name"]
        visited = set()
        queue = list(name_to_deps.get(name, set()))
        depth = 0
        while queue:
            depth += 1
            next_q = []
            for dep in queue:
                if dep not in visited and dep in all_names:
                    visited.add(dep)
                    next_q.extend(name_to_deps.get(dep, set()))
            queue = next_q
            if depth > 20:  # safety cutoff for cyclic/noisy graphs
                break
        d["dep_depth"] = depth

    deep = [(d["name"], d["dep_depth"]) for d in decls if d["dep_depth"] > 5]
    deep.sort(key=lambda x: -x[1])
    if deep:
        print(f"  [depth] deepest chains: {deep[:5]}", file=sys.stderr)
    return decls


# ── Pass 6: Anti-pattern detection ──────────────────────────────────

def pass_antipatterns(decls):
    """Flag simple graph-shape hints that may deserve human review."""
    warnings = []
    for d in decls:
        name = d["name"]
        deps = set(d.get("deps", []))

        # Socket detection: definitions depending only on boundary-marker names.
        if d["kind"] == "def" and len(deps) > 3:
            if all(dep.endswith("Socket") or dep.endswith("Target") or "Prop" in dep or "True" in dep
                   for dep in deps if dep.split(".")[-1] not in ("mk", "injEq")):
                warnings.append({"name": name, "type": "likely_socket", "deps": list(deps)})

        if d.get("vacuity_hint") == "zero_dep_user_theorem_check_source":
            warnings.append({"name": name, "type": "zero_dep_theorem", "deps": list(deps)})

    for w in warnings[:5]:
        print(f"  [warn] {w['type']}: {w['name']}", file=sys.stderr)
    return decls


# ── Main pipeline ──────────────────────────────────────────────────

def main() -> int:
    input_path = sys.argv[1] if len(sys.argv) > 1 else None
    output_path = sys.argv[2] if len(sys.argv) > 2 else None

    decls = load(input_path)
    if decls is None:
        return 2

    print(f"GEPA: optimizing {len(decls)} declarations", file=sys.stderr)

    decls, summary = canonicalize_if_available(decls)
    print(
        "GEPA canonical: "
        + " ".join(
            f"{key}={value}"
            for key, value in {
                "decls": summary["declarations"],
                "modules": summary["modules"],
                "auto": summary["auto_generated_hint_count"],
                "dup_edges": summary["duplicate_edges_removed"],
                "vacuity_files": summary.get("files_scanned", 0),
            }.items()
        ),
        file=sys.stderr,
    )

    decls = pass_normalize(decls)
    decls = pass_classify_modules(decls)
    decls = pass_classify_style(decls)
    decls = pass_reuse_score(decls)
    decls = pass_dependency_depth(decls)
    decls = pass_antipatterns(decls)

    print(f"GEPA: output {len(decls)} optimized declarations", file=sys.stderr)
    save(decls, output_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
