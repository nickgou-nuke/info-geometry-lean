#!/usr/bin/env python3
from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools.pathing import default_docs_map_root, normalize_user_path
from scripts.utils import load_json, dump_json, sanitize_label_suffix, prefix_match, matches_prefix





def decls_payload_to_list(payload: Any) -> list[dict[str, str]]:
    if isinstance(payload, dict) and "declarations" in payload:
        return list(payload["declarations"])
    if isinstance(payload, list):
        return payload
    raise ValueError("Unsupported declarations JSON schema")


def index_decls(decls: list[dict[str, str]]) -> tuple[dict[str, dict[str, str]], dict[str, list[dict[str, str]]]]:
    by_name: dict[str, dict[str, str]] = {}
    by_module: dict[str, list[dict[str, str]]] = {}
    for d in decls:
        name = d["name"]
        by_name[name] = d
        by_module.setdefault(d.get("module", "<unknown>"), []).append(d)
    return by_name, by_module


# note: prefix_match imported from scripts.utils is used in some places


def resolve_node(node: dict[str, Any], by_name: dict[str, dict[str, str]]) -> tuple[list[dict[str, str]], list[str]]:
    resolved: list[dict[str, str]] = []
    missing: list[str] = []

    # 1) Exact list (many-to-one node support)
    for nm in node.get("lean", []):
        d = by_name.get(nm)
        if d:
            resolved.append(d)
        else:
            missing.append(nm)

    # 2) Fallback candidates (first existing wins)
    if not resolved and node.get("leanAnyOf"):
        found = None
        for nm in node["leanAnyOf"]:
            d = by_name.get(nm)
            if d:
                found = d
                break
        if found:
            resolved.append(found)
        else:
            missing.extend(node["leanAnyOf"])

    # Deduplicate by declaration name
    uniq = {}
    for d in resolved:
        uniq[d["name"]] = d
    resolved = [uniq[k] for k in sorted(uniq.keys())]

    return resolved, missing


def build_resolved(manifest: dict[str, Any], decls_payload: Any) -> tuple[dict[str, Any], dict[str, Any], int]:
    decls = decls_payload_to_list(decls_payload)
    by_name, _ = index_decls(decls)

    explicit_mapped_names: set[str] = set()
    used_labels: set[str] = set()
    unresolved_nodes: list[dict[str, Any]] = []
    resolved_chapters: list[dict[str, Any]] = []

    # Resolve explicit nodes first
    for ch in manifest["chapters"]:
        ch_out = {
            "id": ch["id"],
            "number": ch.get("number"),
            "title": ch["title"],
            "modulePrefixes": ch.get("modulePrefixes", []),
            "includeUnmappedDecls": ch.get("includeUnmappedDecls", False),
            "sections": [],
            "autoNodes": []
        }

        for sec in ch.get("sections", []):
            sec_out = {"id": sec["id"], "title": sec["title"], "nodes": []}
            for node in sec.get("nodes", []):
                label = node["label"]
                if label in used_labels:
                    raise ValueError(f"Duplicate node label: {label}")
                used_labels.add(label)

                resolved, missing = resolve_node(node, by_name)
                for d in resolved:
                    explicit_mapped_names.add(d["name"])

                node_out = dict(node)
                node_out["resolvedLean"] = [d["name"] for d in resolved]
                node_out["resolvedKinds"] = sorted({d.get("kind", "") for d in resolved if d.get("kind")})
                node_out["resolvedModules"] = sorted({d.get("module", "") for d in resolved if d.get("module")})
                node_out["missingLean"] = missing if not resolved else []
                sec_out["nodes"].append(node_out)

                if not resolved:
                    unresolved_nodes.append({
                        "chapter": ch["id"],
                        "section": sec["id"],
                        "label": label,
                        "title": node.get("title", ""),
                        "missingLean": missing
                    })

            ch_out["sections"].append(sec_out)

        resolved_chapters.append(ch_out)

    # Auto-assign unmapped declarations to chapters by module prefix, chapter order precedence
    auto_assigned: set[str] = set()
    all_decl_names = {d["name"] for d in decls}
    unmapped_global = all_decl_names - explicit_mapped_names

    for ch_out in resolved_chapters:
        prefixes = ch_out.get("modulePrefixes", [])
        if not ch_out.get("includeUnmappedDecls", False):
            continue

        for d in decls:
            nm = d["name"]
            if nm not in unmapped_global:
                continue
            if nm in auto_assigned:
                continue
            mod = d.get("module", "")
            if matches_prefix(mod, prefixes) or matches_prefix(nm, prefixes):
                auto_assigned.add(nm)
                ch_out["autoNodes"].append({
                    "label": f"auto:{sanitize_label_suffix(nm)}",
                    "kind": d.get("kind", "theorem"),
                    "title": nm,
                    "resolvedLean": [nm],
                    "resolvedKinds": [d.get("kind", "")],
                    "resolvedModules": [mod],
                    "render": "stub",
                    "autoGenerated": True
                })

        ch_out["autoNodes"].sort(key=lambda n: n["title"])

    mapped_names = explicit_mapped_names | auto_assigned
    still_unmapped = sorted(all_decl_names - mapped_names)

    coverage = {
        "project": manifest["project"]["name"],
        "totalDeclarations": len(decls),
        "explicitMappedDeclarations": len(explicit_mapped_names),
        "autoMappedDeclarations": len(auto_assigned),
        "mappedDeclarations": len(mapped_names),
        "unmappedDeclarations": len(still_unmapped),
        "unresolvedExplicitNodes": len(unresolved_nodes),
        "unresolvedNodes": unresolved_nodes,
        "stillUnmappedDeclarationNames": still_unmapped
    }

    resolved = {
        "project": manifest["project"],
        "paths": manifest.get("paths", {}),
        "renderDefaults": manifest.get("renderDefaults", {}),
        "chapters": resolved_chapters
    }

    return resolved, coverage, len(unresolved_nodes)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default=None, help="Path to manifest.json")
    ap.add_argument("--declarations", default=None, help="Defaults to manifest.paths.declarationsJson")
    ap.add_argument("--resolved", default=None, help="Defaults to manifest.paths.resolvedJson")
    ap.add_argument("--coverage", default=None, help="Defaults to manifest.paths.coverageJson")
    ap.add_argument("--strict", action="store_true", help="Exit nonzero if any explicit node fails to resolve")
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    manifest_path = normalize_user_path(args.manifest, docs_root / "manifest.json")
    manifest = load_json(manifest_path)

    decl_path = normalize_user_path(args.declarations or manifest["paths"]["declarationsJson"], docs_root / manifest["paths"]["declarationsJson"])
    resolved_path = normalize_user_path(args.resolved or manifest["paths"]["resolvedJson"], docs_root / manifest["paths"]["resolvedJson"])
    coverage_path = normalize_user_path(args.coverage or manifest["paths"]["coverageJson"], docs_root / manifest["paths"]["coverageJson"])

    decl_payload = load_json(decl_path)
    resolved, coverage, unresolved_count = build_resolved(manifest, decl_payload)

    dump_json(resolved_path, resolved)
    dump_json(coverage_path, coverage)

    print(f"[build_doc_map] wrote {resolved_path}")
    print(f"[build_doc_map] wrote {coverage_path}")
    print(f"[build_doc_map] total={coverage['totalDeclarations']} mapped={coverage['mappedDeclarations']} "
          f"unmapped={coverage['unmappedDeclarations']} unresolvedNodes={coverage['unresolvedExplicitNodes']}")

    if args.strict and unresolved_count > 0:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())