#!/usr/bin/env python3
"""
LEGACY — infotree declaration-level dual feature space.

This tool operates on the raw infotree declaration dependency graph
(artifacts/infotree/arango-lossless-dag-current/), NOT on the expression-level
wire/gate topology from wire_topology_transform.py.

For the canonical expression-level dual graph, use:
  - wire_topology_transform.py        (wire/gate incidence graph)
  - materialize_translation_candidates.py  (translation candidates + verified edges)
  - generate_translation_dedup_report.py   (read-only audit report)

This legacy tool is kept for infotree-level analysis only.
Its output schema (dual_features.jsonl, dual_edges.jsonl, subprogram_fingerprints.jsonl)
is NOT compatible with the ig_wires / ig_gates / ig_wire_edges stack.

Uses src/dst fields (declaration names) for dependency edges, not _from/_to (raw node keys).

Input:  ig_nodes.jsonl, ig_edges.jsonl (from raw infotree export)
Output:
  - dual_features.jsonl    (feature nodes)
  - dual_edges.jsonl       (subprogram --has_feature--> feature)
  - subprogram_fingerprints.jsonl (hash ladder per subprogram)
  - feature_index.json     (summary statistics)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


DEFAULT_INPUT_DIR = "artifacts/infotree/arango-lossless-dag-current"
DEFAULT_OUTPUT_DIR = "artifacts/infotree/legacy-dual"


def sha256_hex(payload: str) -> str:
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def build_dual_space(
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
) -> tuple[
    list[dict[str, Any]],  # features
    list[dict[str, Any]],  # dual edges
    list[dict[str, Any]],  # fingerprints
]:
    """
    Build the exact dual feature space.

    Uses src/dst fields for declaration dependency edges.
    """

    # Build node lookup by name (src field in edges)
    node_by_name: dict[str, dict[str, Any]] = {}
    for n in nodes:
        name = n.get("name", "")
        if name:
            node_by_name[name] = n

    # Build adjacency using src/dst (declaration names)
    # src = declaration, dst = dependency
    decl_deps: dict[str, list[tuple[str, str]]] = defaultdict(list)  # decl -> [(dep_name, kind)]
    decl_reverse_deps: dict[str, list[tuple[str, str]]] = defaultdict(list)

    for e in edges:
        kind = str(e.get("kind", "")).strip()
        src = str(e.get("src", "")).strip()
        dst = str(e.get("dst", "")).strip()
        if not src or not dst:
            continue
        decl_deps[src].append((dst, kind))
        decl_reverse_deps[dst].append((src, kind))

    # SCC analysis (from node data)
    scc_members: dict[int, list[str]] = defaultdict(list)
    for n in nodes:
        scc_id = n.get("scc_id")
        name = n.get("name", "")
        if scc_id is not None and name:
            scc_members[scc_id].append(name)

    scc_sizes = {sid: len(members) for sid, members in scc_members.items()}

    # Build features and dual edges
    features: dict[str, dict[str, Any]] = {}
    dual_edges: list[dict[str, Any]] = []
    fingerprints: list[dict[str, Any]] = []

    feature_edge_set: set[tuple[str, str]] = set()  # deduplicate edges

    def add_feature(fkey: str, fkind: str, fvalue: str, fdetail: str = ""):
        if fkey not in features:
            features[fkey] = {
                "_key": fkey,
                "kind": fkind,
                "value": fvalue,
                "detail": fdetail,
                "subprogram_count": 0,
            }
        features[fkey]["subprogram_count"] += 1

    def add_dual_edge(subprogram_name: str, feature_key: str, predicate: str):
        edge_key = (subprogram_name, feature_key)
        if edge_key not in feature_edge_set:
            feature_edge_set.add(edge_key)
            dual_edges.append({
                "_from": f"subprograms/{subprogram_name}",
                "_to": f"dual_features/{feature_key}",
                "predicate": predicate,
            })

    # Process each declaration node
    for n in nodes:
        name = n.get("name", "")
        if not name:
            continue

        kind = n.get("kind", "unknown")
        module = n.get("module", "")
        scc_id = n.get("scc_id")
        scc_size = scc_sizes.get(scc_id, 1) if scc_id is not None else 1

        # Skip external endpoint stubs
        if kind == "endpoint_stub":
            continue

        # 1. Kind feature
        kind_fkey = f"kind:{kind}"
        add_feature(kind_fkey, "kind", kind)
        add_dual_edge(name, kind_fkey, "has_kind")

        # 2. Module features
        if module:
            parts = module.split(".")
            for i in range(1, min(len(parts) + 1, 4)):  # up to 3 levels
                mod_path = ".".join(parts[:i])
                mod_fkey = f"module:{mod_path}"
                add_feature(mod_fkey, "module", mod_path, module)
                add_dual_edge(name, mod_fkey, "belongs_to_module")

        # 3. SCC features
        if scc_id is not None:
            if scc_size == 1:
                scc_fkey = "scc:singleton"
                add_feature(scc_fkey, "scc", "singleton")
                add_dual_edge(name, scc_fkey, "in_singleton_scc")
            else:
                # Categorize SCC size
                if scc_size <= 5:
                    scc_cat = "small"
                elif scc_size <= 20:
                    scc_cat = "medium"
                elif scc_size <= 100:
                    scc_cat = "large"
                else:
                    scc_cat = "xlarge"
                scc_fkey = f"scc:{scc_cat}_cycle"
                add_feature(scc_fkey, "scc", f"{scc_cat}_cycle", f"size={scc_size}")
                add_dual_edge(name, scc_fkey, "in_cycle_scc")

        # 4. Dependency features
        deps = decl_deps.get(name, [])
        dep_kinds = Counter(k for _, k in deps)
        dep_targets = [d for d, _ in deps]

        # Dependency count features
        total_deps = len(deps)
        if total_deps == 0:
            dep_count_fkey = "deps:none"
            add_feature(dep_count_fkey, "dep_count", "0")
            add_dual_edge(name, dep_count_fkey, "has_no_deps")
        elif total_deps <= 5:
            dep_count_fkey = "deps:few"
            add_feature(dep_count_fkey, "dep_count", "few")
            add_dual_edge(name, dep_count_fkey, "has_few_deps")
        elif total_deps <= 20:
            dep_count_fkey = "deps:moderate"
            add_feature(dep_count_fkey, "dep_count", "moderate")
            add_dual_edge(name, dep_count_fkey, "has_moderate_deps")
        elif total_deps <= 100:
            dep_count_fkey = "deps:many"
            add_feature(dep_count_fkey, "dep_count", "many")
            add_dual_edge(name, dep_count_fkey, "has_many_deps")
        else:
            dep_count_fkey = "deps:very_many"
            add_feature(dep_count_fkey, "dep_count", "very_many")
            add_dual_edge(name, dep_count_fkey, "has_very_many_deps")

        # Dependency kind pattern
        type_deps = dep_kinds.get("type", 0)
        value_deps = dep_kinds.get("value", 0)
        if type_deps > 0:
            add_feature("dep_kind:type", "dep_kind", "type")
            add_dual_edge(name, "dep_kind:type", "has_type_dep")
        if value_deps > 0:
            add_feature("dep_kind:value", "dep_kind", "value")
            add_dual_edge(name, "dep_kind:value", "has_value_dep")

        # Individual dependency features (top dependencies only)
        # Count how many times each dep appears across all decls
        for dep_name, dep_kind in deps:
            dep_node = node_by_name.get(dep_name, {})
            dep_kind_node = dep_node.get("kind", "unknown")
            if dep_kind_node != "endpoint_stub":
                dep_fkey = f"depends_on:{dep_name}"
                add_feature(dep_fkey, "dependency", dep_name, f"kind={dep_kind_node}")
                add_dual_edge(name, dep_fkey, f"depends_on_{dep_kind}")

        # 5. Reverse dependency features
        reverse_deps = decl_reverse_deps.get(name, [])
        if len(reverse_deps) > 0:
            add_feature("is_depended_on", "reverse_dep", "true")
            add_dual_edge(name, "is_depended_on", "is_depended_on")
            if len(reverse_deps) > 10:
                add_feature("is_heavily_depended_on", "reverse_dep", "heavy")
                add_dual_edge(name, "is_heavily_depended_on", "is_heavily_depended_on")

        # 6. Compute hash ladder
        fp = compute_fingerprint(n, deps, dep_kinds, scc_size, module, len(reverse_deps))
        fp["_key"] = name
        fp["name"] = name
        fp["kind"] = kind
        fp["module"] = module
        fp["scc_id"] = scc_id
        fp["scc_size"] = scc_size
        fp["dep_count"] = total_deps
        fp["reverse_dep_count"] = len(reverse_deps)
        fingerprints.append(fp)

    return list(features.values()), dual_edges, fingerprints


def compute_fingerprint(
    node: dict[str, Any],
    deps: list[tuple[str, str]],
    dep_kinds: Counter,
    scc_size: int,
    module: str,
    reverse_dep_count: int,
) -> dict[str, Any]:
    """Compute the hash ladder for a single subprogram."""

    name = node.get("name", "")
    kind = node.get("kind", "")

    # Level 0: raw identity
    raw_hash = sha256_hex(f"raw:{name}:{kind}")

    # Level 1: kind + module
    kind_module_hash = sha256_hex(f"kind_module:{kind}:{module}")

    # Level 2: dependency pattern (counts by kind)
    dep_pattern = (
        f"type:{dep_kinds.get('type',0)}|"
        f"value:{dep_kinds.get('value',0)}|"
        f"scc:{scc_size}|"
        f"rev:{reverse_dep_count}"
    )
    dep_pattern_hash = sha256_hex(dep_pattern)

    # Level 3: structural shape (deps sorted by name)
    dep_names_sorted = sorted([d for d, _ in deps])
    dep_names_hash = sha256_hex("|".join(dep_names_sorted))
    shape_hash = sha256_hex(f"shape:{kind}|{dep_pattern}|{dep_names_hash}")

    # Level 4: translation-invariant (module-agnostic, specific-dep-agnostic)
    # Use dep name prefixes (top-level module) instead of full names
    dep_prefixes = sorted(set(
        d.split(".")[0] if "." in d else d for d, _ in deps
    ))
    translation_hash = sha256_hex(
        f"translation:{kind}|"
        f"type:{dep_kinds.get('type',0)}|"
        f"value:{dep_kinds.get('value',0)}|"
        f"scc:{scc_size}|"
        f"prefixes:{'|'.join(dep_prefixes)}"
    )

    # Level 5: incidence hash (full feature vector)
    feature_str = (
        f"{kind}|{module}|{dep_pattern}|{len(deps)}|{reverse_dep_count}"
    )
    incidence_hash = sha256_hex(feature_str)

    return {
        "rawHash": raw_hash,
        "kindModuleHash": kind_module_hash,
        "depPatternHash": dep_pattern_hash,
        "shapeHash": shape_hash,
        "translationHash": translation_hash,
        "incidenceHash": incidence_hash,
    }


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Build exact dual feature space from raw infotree declaration graph"
    )
    ap.add_argument("--input-dir", default=DEFAULT_INPUT_DIR)
    ap.add_argument("--output-dir", default=DEFAULT_OUTPUT_DIR)
    args = ap.parse_args()

    input_dir = normalize_user_path(args.input_dir, (repo_root() / DEFAULT_INPUT_DIR))
    output_dir = normalize_user_path(args.output_dir, (repo_root() / DEFAULT_OUTPUT_DIR))

    nodes_path = input_dir / "ig_nodes.jsonl"
    edges_path = input_dir / "ig_edges.jsonl"

    if not nodes_path.exists():
        print(f"[dual-space] input not found: {nodes_path}", file=sys.stderr)
        return 1

    print(f"[dual-space] reading {nodes_path}")
    nodes = iter_jsonl(nodes_path)
    print(f"[dual-space] reading {edges_path}")
    edges = iter_jsonl(edges_path)

    print(f"[dual-space] building dual feature space from {len(nodes)} nodes, {len(edges)} edges")
    features, dual_edges, fingerprints = build_dual_space(nodes, edges)

    print(f"[dual-space] writing output to {output_dir}")
    write_jsonl(output_dir / "dual_features.jsonl", features)
    write_jsonl(output_dir / "dual_edges.jsonl", dual_edges)
    write_jsonl(output_dir / "subprogram_fingerprints.jsonl", fingerprints)

    # Summary
    feature_kinds = Counter(f.get("kind", "?") for f in features)

    unique_hashes = {}
    for h in ["rawHash", "kindModuleHash", "depPatternHash", "shapeHash", "translationHash", "incidenceHash"]:
        unique = len(set(fp.get(h, "") for fp in fingerprints))
        unique_hashes[h] = unique

    print(f"\n[dual-space] === Summary ===")
    print(f"  Subprograms: {len(fingerprints)}")
    print(f"  Features: {len(features)}")
    for k, v in sorted(feature_kinds.items(), key=lambda x: -x[1]):
        print(f"    {k}: {v}")
    print(f"  Dual edges: {len(dual_edges)}")
    print(f"\n  Hash ladder uniqueness:")
    for h, count in unique_hashes.items():
        pct = count / len(fingerprints) * 100 if fingerprints else 0
        print(f"    {h}: {count} unique ({pct:.1f}%)")

    # Write summary
    summary = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "input_dir": str(input_dir),
        "stats": {
            "subprogram_count": len(fingerprints),
            "feature_count": len(features),
            "dual_edge_count": len(dual_edges),
            "feature_kinds": dict(feature_kinds),
            "unique_hashes": unique_hashes,
        },
    }
    (output_dir / "feature_index.json").write_text(
        json.dumps(summary, indent=2), encoding="utf-8"
    )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
