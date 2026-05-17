#!/usr/bin/env python3
"""
Static Lean graph overlay and wrapper-silhouette dedup.

This is intentionally *not* a Lean-kernel elaboration pass. It is a fast
observability layer for repository navigation when `lean`/`lake` is unavailable.

Outputs:
  - graph_overlay.json: files, declarations, import edges, contains edges,
    lexical reference edges, alpha-normalized hashes, WL hashes.
  - graph_overlay_report.md
  - graph_overlay_dashboard.html

For kernel-accurate expression/de-Bruijn hashes, add a later Lean exporter that
emits elaborated Expr JSON; this script can consume those hashes if present.
"""
from __future__ import annotations

import argparse
import dataclasses
import hashlib
import html
import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Dict, Tuple, Optional, Any

DECL_KINDS = [
    "theorem", "lemma", "def", "abbrev", "structure", "class", "inductive",
    "instance", "axiom", "opaque", "constant", "example"
]
DECL_RE = re.compile(r"^\s*(?:@[\w_\.\s\[\],:=\-]+\]\s*)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque|constant|example)\s+([^\s:({]+)?")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_\.]+)")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_\.]+)")
END_NS_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_\.]+))?")

RESERVED = set(DECL_KINDS + [
    "by", "where", "with", "let", "have", "show", "exact", "intro", "intros",
    "fun", "match", "if", "then", "else", "Type", "Type*", "Prop", "Sort",
    "namespace", "end", "import", "open", "section", "noncomputable", "variable",
    "variables", "universe", "universes", "in", "using", "from", "calc",
    "simpa", "simp", "rw", "rfl", "True", "False", "forall", "∀", "λ",
    "extends", "return", "do", "for", "in", "as", "macro", "syntax", "notation",
])
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|[0-9]+(?:\.[0-9]+)?|:=|=>|↦|→|←|∀|∃|[{}()\[\],;:.=+\-*/<>!%^&|?]+|\S")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")

@dataclasses.dataclass
class Decl:
    id: str
    file: str
    kind: str
    name: str
    fqname: str
    start_line: int
    end_line: int
    text: str
    type_text: str
    proof_text: str
    alpha_hash: str
    type_hash_alpha: str
    proof_hash_alpha: str
    alpha_tokens: List[str]
    contains_sorry: bool
    contains_axiom_like: bool
    refs: List[str] = dataclasses.field(default_factory=list)
    direct_dependencies: List[str] = dataclasses.field(default_factory=list)
    reverse_dependencies: List[str] = dataclasses.field(default_factory=list)
    wl_hash: str = ""
    is_owner: bool = False
    is_bridge: bool = False
    is_socket: bool = False
    rep_depth: str = ""
    template_role: str = ""
    socket_debt_class: str = ""


def sha256_short(s: str, n: int = 16) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()[:n]


def strip_comments(s: str) -> str:
    # Lightweight comment stripper; handles most line/block comments but not nested blocks.
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    s = re.sub(r"--.*", " ", s)
    return s


def tokenize(s: str) -> List[str]:
    return TOKEN_RE.findall(strip_comments(s))


def alpha_normalize_tokens(tokens: List[str]) -> List[str]:
    """Heuristic alpha normalization.

    We canonicalize identifiers by first occurrence inside the declaration block,
    preserving reserved words, declaration keywords, numerals, and symbols.
    This is not true de-Bruijn over elaborated binders, but it clusters Lean
    wrapper silhouettes well enough for static observability.
    """
    env: Dict[str, str] = {}
    out: List[str] = []
    counter = 0
    for tok in tokens:
        if IDENT_RE.match(tok) and tok not in RESERVED:
            # preserve qualified imported namespace heads somewhat coarsely
            if tok.startswith("Mathlib") or tok.startswith("InfoGeometry"):
                out.append("QNAME")
                continue
            if tok not in env:
                env[tok] = f"v{counter}"
                counter += 1
            out.append(env[tok])
        else:
            out.append(tok)
    return out


def split_decl_body(block: str) -> Tuple[str, str]:
    """Split a declaration block into a type-ish prefix and proof/body-ish suffix.

    This is heuristic and purely for observability. It tries to separate the
    statement surface from the proof/body surface when `:=` or `where` exists.
    """
    for sep in ("\n:=\n", "\n:= ", "\nwhere\n", "\nwhere "):
        if sep in block:
            head, tail = block.split(sep, 1)
            return head + sep.strip(), tail
    if ":=" in block:
        head, tail = block.split(":=", 1)
        return head + ":=", tail
    if " where" in block:
        head, tail = block.split(" where", 1)
        return head + " where", tail
    return block, ""


def decl_template_role(kind: str, name: str, attr_text: str) -> str:
    lowered = name.lower()
    if "socket_debt_tag" in attr_text:
        return "Socket"
    if "bridge_target_tag" in attr_text:
        return "Bridge"
    if "owner_target_tag" in attr_text:
        return "Witness"
    if "gate" in lowered:
        return "Gate"
    if "bridge" in lowered:
        return "Bridge"
    if "socket" in lowered:
        return "Socket"
    if kind in {"theorem", "lemma", "example"}:
        return "Witness"
    return "Source"


def decl_socket_debt_class(is_socket: bool, is_owner: bool, is_bridge: bool, contains_sorry: bool, contains_axiom_like: bool, name: str, kind: str) -> str:
    if is_socket:
        return "socket_debt"
    if is_bridge:
        return "bridge_preservation"
    if is_owner:
        return "closed_owner"
    if contains_sorry or contains_axiom_like:
        return "source_claim"
    if "alias" in name.lower() or "equiv" in name.lower() or "preserve" in name.lower():
        return "duplicate_alias"
    if kind in {"theorem", "lemma", "def"}:
        return "unclassified"
    return "source_claim"


def parse_file(path: Path, root: Path) -> Tuple[List[str], List[Decl]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    rel = str(path.relative_to(root))
    imports: List[str] = []
    ns_stack: List[str] = []
    decl_starts: List[Tuple[int, str, str, List[str]]] = []
    current_ns: List[str] = []

    # Track namespace line-by-line. Store namespace snapshot at decl start.
    ns_at_line: Dict[int, List[str]] = {}
    for i, line in enumerate(lines, start=1):
        m_imp = IMPORT_RE.match(line)
        if m_imp:
            imports.append(m_imp.group(1))
        m_ns = NAMESPACE_RE.match(line)
        if m_ns:
            current_ns.append(m_ns.group(1))
        m_end = END_NS_RE.match(line)
        if m_end and current_ns:
            current_ns.pop()
        ns_at_line[i] = list(current_ns)
        m_decl = DECL_RE.match(line)
        if m_decl:
            kind = m_decl.group(1)
            name = m_decl.group(2) or f"anonymous_{i}"
            decl_starts.append((i, kind, name, list(current_ns)))

    decls: List[Decl] = []
    for idx, (start, kind, name, ns) in enumerate(decl_starts):
        end = decl_starts[idx + 1][0] - 1 if idx + 1 < len(decl_starts) else len(lines)
        
        # Scan upwards to capture attribute lines immediately preceding the declaration
        attr_lines = []
        p = start - 2
        while p >= 0 and lines[p].strip().startswith("@["):
            attr_lines.insert(0, lines[p].strip())
            p -= 1
        
        # Also include any attributes on the same line
        decl_line = lines[start - 1]
        attr_text = " ".join(attr_lines) + " " + decl_line
        
        is_owner = "owner_target_tag" in attr_text
        is_bridge = "bridge_target_tag" in attr_text
        is_socket = "socket_debt_tag" in attr_text
        template_role = decl_template_role(kind, name, attr_text)

        rep_depth = ""
        m_depth = re.search(r"rep_depth\s+([a-zA-Z0-9_]+)", attr_text)
        if m_depth:
            rep_depth = m_depth.group(1)

        block = "\n".join(lines[p + 1:end])
        type_text, proof_text = split_decl_body(block)
        tokens = tokenize(block)
        alpha_tokens = alpha_normalize_tokens(tokens)
        alpha_hash = sha256_short(" ".join(alpha_tokens))
        type_hash_alpha = sha256_short(" ".join(alpha_normalize_tokens(tokenize(type_text))))
        proof_hash_alpha = sha256_short(" ".join(alpha_normalize_tokens(tokenize(proof_text or type_text))))
        fq = ".".join([*ns, name]) if ns else name
        decl_id = sha256_short(f"{rel}:{start}:{fq}", 20)
        decls.append(Decl(
            id=decl_id,
            file=rel,
            kind=kind,
            name=name,
            fqname=fq,
            start_line=start,
            end_line=end,
            text=block,
            type_text=type_text,
            proof_text=proof_text,
            alpha_hash=alpha_hash,
            type_hash_alpha=type_hash_alpha,
            proof_hash_alpha=proof_hash_alpha,
            alpha_tokens=alpha_tokens,
            contains_sorry=bool(re.search(r"\b(sorry|admit)\b", strip_comments(block))),
            contains_axiom_like=(kind in {"axiom", "constant", "opaque"}),
            is_owner=is_owner,
            is_bridge=is_bridge,
            is_socket=is_socket,
            rep_depth=rep_depth,
            template_role=template_role,
            socket_debt_class=decl_socket_debt_class(is_socket, is_owner, is_bridge, bool(re.search(r"\b(sorry|admit)\b", strip_comments(block))), kind in {"axiom", "constant", "opaque"}, name, kind),
        ))
    return imports, decls


def build_graph(root: Path, wl_rounds: int = 4) -> Dict[str, Any]:
    files = sorted(path for path in root.rglob("*.lean") if path.is_file())
    file_nodes = []
    decls: List[Decl] = []
    imports_by_file: Dict[str, List[str]] = {}
    for path in files:
        imports, ds = parse_file(path, root)
        rel = str(path.relative_to(root))
        imports_by_file[rel] = imports
        decls.extend(ds)
        file_nodes.append({
            "id": f"file:{rel}",
            "kind": "file",
            "path": rel,
            "imports": imports,
            "decl_count": len(ds),
        })

    # Declaration reference edges by lexical name occurrence.
    name_to_ids: Dict[str, List[str]] = defaultdict(list)
    fq_to_id: Dict[str, str] = {}
    for d in decls:
        name_to_ids[d.name].append(d.id)
        fq_to_id[d.fqname] = d.id
    id_to_fq = {v: k for k, v in fq_to_id.items()}

    edges = []
    for f in file_nodes:
        for imp in f["imports"]:
            edges.append({"source": f["id"], "target": f"import:{imp}", "type": "imports"})

    for d in decls:
        edges.append({"source": f"file:{d.file}", "target": f"decl:{d.id}", "type": "contains"})

    # Use tokenized original text for references to declarations in same scanned tree.
    decl_names = set(name_to_ids.keys())
    for d in decls:
        toks = set(tokenize(d.text))
        refs = sorted((decl_names & toks) - {d.name})
        d.refs = refs
        for refname in refs:
            targets = name_to_ids.get(refname, [])
            # If ambiguous, include all but mark ambiguous.
            for tid in targets:
                edges.append({"source": f"decl:{d.id}", "target": f"decl:{tid}", "type": "lexical_ref", "refname": refname})

    decl_out_deps: Dict[str, set[str]] = defaultdict(set)
    decl_in_deps: Dict[str, set[str]] = defaultdict(set)
    for e in edges:
        if e["type"] != "lexical_ref":
            continue
        if e["source"].startswith("decl:") and e["target"].startswith("decl:"):
            decl_out_deps[e["source"]].add(e["target"])
            decl_in_deps[e["target"]].add(e["source"])

    nodes: List[Dict[str, Any]] = []
    nodes.extend(file_nodes)
    # import placeholder nodes
    imports = sorted({imp for imps in imports_by_file.values() for imp in imps})
    for imp in imports:
        nodes.append({"id": f"import:{imp}", "kind": "import", "name": imp})
    for d in decls:
        nodes.append({
            "id": f"decl:{d.id}",
            "kind": "decl",
            "decl_kind": d.kind,
            "name": d.name,
            "fqname": d.fqname,
            "file": d.file,
            "imports": imports_by_file.get(d.file, []),
            "start_line": d.start_line,
            "end_line": d.end_line,
            "type_text": d.type_text,
            "proof_text": d.proof_text,
            "alpha_hash": d.alpha_hash,
            "type_hash_alpha": d.type_hash_alpha,
            "proof_hash_alpha": d.proof_hash_alpha,
            "contains_sorry": d.contains_sorry,
            "contains_axiom_like": d.contains_axiom_like,
            "is_owner": d.is_owner,
            "is_bridge": d.is_bridge,
            "is_socket": d.is_socket,
            "rep_depth": d.rep_depth,
            "template_role": d.template_role,
            "socket_debt_class": d.socket_debt_class,
            "refs": d.refs,
            "direct_dependencies": sorted(
                id_to_fq.get(dep.split("decl:", 1)[1], dep) for dep in decl_out_deps.get(f"decl:{d.id}", set())
            ),
            "reverse_dependencies": sorted(
                id_to_fq.get(dep.split("decl:", 1)[1], dep) for dep in decl_in_deps.get(f"decl:{d.id}", set())
            ),
            "token_count": len(d.alpha_tokens),
        })

    # Weisfeiler-Lehman refinement over directed graph.
    label: Dict[str, str] = {}
    for n in nodes:
        if n["kind"] == "decl":
            label[n["id"]] = f"decl:{n.get('decl_kind')}:{n.get('alpha_hash')}"
        elif n["kind"] == "file":
            label[n["id"]] = "file"
        else:
            label[n["id"]] = "import"
    out_edges = defaultdict(list)
    in_edges = defaultdict(list)
    for e in edges:
        out_edges[e["source"]].append((e["type"], e["target"]))
        in_edges[e["target"]].append((e["type"], e["source"]))
    for _ in range(wl_rounds):
        new_label = {}
        for n in nodes:
            nid = n["id"]
            neigh = []
            for et, tgt in sorted(out_edges.get(nid, [])):
                neigh.append(f"out:{et}:{label.get(tgt,'?')}")
            for et, src in sorted(in_edges.get(nid, [])):
                neigh.append(f"in:{et}:{label.get(src,'?')}")
            new_label[nid] = sha256_short(label[nid] + "|" + "|".join(neigh))
        label = new_label
    for n in nodes:
        n["wl_hash"] = label[n["id"]]

    # Duplicate classes.
    alpha_classes = defaultdict(list)
    wl_classes = defaultdict(list)
    for n in nodes:
        if n["kind"] == "decl":
            alpha_classes[n["alpha_hash"]].append(n["id"])
            wl_classes[n["wl_hash"]].append(n["id"])
    duplicate_alpha = {k:v for k,v in alpha_classes.items() if len(v) > 1}
    duplicate_wl = {k:v for k,v in wl_classes.items() if len(v) > 1}

    # SCCs for lexical decl graph only (Tarjan).
    decl_ids = [n["id"] for n in nodes if n["kind"] == "decl"]
    decl_adj = defaultdict(list)
    for e in edges:
        if e["type"] == "lexical_ref" and e["source"] in decl_ids and e["target"] in decl_ids:
            decl_adj[e["source"]].append(e["target"])

    index = 0
    stack = []
    onstack = set()
    indices = {}
    lowlink = {}
    sccs = []
    def strongconnect(v):
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v); onstack.add(v)
        for w in decl_adj.get(v, []):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in onstack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp = []
            while True:
                w = stack.pop(); onstack.remove(w)
                comp.append(w)
                if w == v: break
            if len(comp) > 1:
                sccs.append(comp)
    for v in decl_ids:
        if v not in indices:
            strongconnect(v)

    return {
        "root": str(root),
        "nodes": nodes,
        "edges": edges,
        "duplicate_alpha_classes": duplicate_alpha,
        "duplicate_wl_classes": duplicate_wl,
        "sccs": sccs,
        "stats": {
            "files": len(file_nodes),
            "decls": len(decls),
            "imports": len(imports),
            "edges": len(edges),
            "duplicate_alpha_classes": len(duplicate_alpha),
            "duplicate_wl_classes": len(duplicate_wl),
            "sccs": len(sccs),
            "sorry_decl_count": sum(1 for d in decls if d.contains_sorry),
            "axiom_like_decl_count": sum(1 for d in decls if d.contains_axiom_like),
            "owner_target_count": sum(1 for d in decls if d.is_owner),
            "bridge_target_count": sum(1 for d in decls if d.is_bridge),
            "socket_debt_count": sum(1 for d in decls if d.is_socket),
            "wl_rounds": wl_rounds,
        }
    }


def decl_nodes(graph: Dict[str, Any]) -> List[Dict[str, Any]]:
    return [n for n in graph["nodes"] if n["kind"] == "decl"]


def filter_graph_by_prefix(graph: Dict[str, Any], prefix: str) -> Dict[str, Any]:
    if not prefix:
        return graph
    keep_ids = {n["id"] for n in decl_nodes(graph) if n["fqname"].startswith(prefix)}
    keep_file_ids = {f"file:{n['file']}" for n in decl_nodes(graph) if n["id"] in keep_ids}
    keep_import_ids = {
        f"import:{imp}"
        for n in decl_nodes(graph)
        if n["id"] in keep_ids
        for imp in n.get("imports", [])
    }
    keep_ids_all = keep_ids | keep_file_ids | keep_import_ids
    nodes = [n for n in graph["nodes"] if n["id"] in keep_ids_all]
    edges = [e for e in graph["edges"] if e["source"] in keep_ids_all and e["target"] in keep_ids_all]
    sub = dict(graph)
    sub["nodes"] = nodes
    sub["edges"] = edges
    sub["root_prefix"] = prefix
    return sub


def cluster_classification(members: List[Dict[str, Any]]) -> str:
    if not members:
        return "unclassified"
    if any(m.get("is_socket") or m.get("socket_debt_class") == "socket_debt" for m in members):
        return "socket_debt"
    if any(m.get("is_bridge") for m in members):
        return "bridge_preservation"
    if any(m.get("is_owner") for m in members) and all(not m.get("contains_sorry") for m in members):
        return "closed_owner"
    if len(members) > 1:
        type_hashes = {m.get("type_hash_alpha") for m in members}
        proof_hashes = {m.get("proof_hash_alpha") for m in members}
        if len(type_hashes) == 1 and len(proof_hashes) == 1:
            return "duplicate_alias"
    if any(m.get("contains_sorry") or m.get("contains_axiom_like") for m in members):
        return "source_claim"
    return "unclassified"


def lane_duplicate_clusters(graph: Dict[str, Any]) -> List[Dict[str, Any]]:
    decls = decl_nodes(graph)
    by_hash: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for d in decls:
        by_hash[d.get("alpha_hash", "")].append(d)
    clusters = []
    for h, members in by_hash.items():
        if len(members) <= 1:
            continue
        clusters.append({
            "hash": h,
            "classification": cluster_classification(members),
            "count": len(members),
            "members": members,
        })
    clusters.sort(key=lambda c: (-c["count"], c["hash"]))
    return clusters


def write_lane_report(graph: Dict[str, Any], out_dir: Path, stem: str) -> None:
    decls = decl_nodes(graph)
    clusters = lane_duplicate_clusters(graph)
    report_json = {
        "root": graph["root"],
        "root_prefix": graph.get("root_prefix", ""),
        "include_tags": graph.get("include_tags", []),
        "wl_rounds": graph.get("wl_rounds", graph.get("stats", {}).get("wl_rounds", None)),
        "stats": graph["stats"],
        "declarations": decls,
        "duplicate_clusters": clusters,
    }
    (out_dir / f"{stem}.json").write_text(json.dumps(report_json, ensure_ascii=False, indent=2), encoding="utf-8")
    lines = []
    lines.append(f"# {stem}")
    lines.append("")
    lines.append(f"Root: `{graph['root']}`")
    if graph.get("root_prefix"):
        lines.append(f"Prefix: `{graph['root_prefix']}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    for k, v in graph["stats"].items():
        lines.append(f"- `{k}`: **{v}**")
    lines.append("")
    if graph.get("include_tags"):
        lines.append(f"- `include_tags`: `{', '.join(graph['include_tags'])}`")
        lines.append("")
    class_counts = Counter(c["classification"] for c in clusters)
    if class_counts:
        lines.append("## Cluster classification summary")
        lines.append("")
        for label in ["closed_owner", "bridge_preservation", "duplicate_alias", "socket_debt", "source_claim", "unclassified"]:
            lines.append(f"- `{label}`: **{class_counts.get(label, 0)}**")
        lines.append("")
    lines.append("## Duplicate clusters")
    lines.append("")
    if not clusters:
        lines.append("No duplicate alpha classes found in scope.")
    else:
        for c in clusters:
            lines.append(f"### `{c['hash']}` ({c['count']} declarations, `{c['classification']}`)")
            for m in c["members"]:
                lines.append(
                    f"- `{m['fqname']}` [{m['decl_kind']}] `{m['file']}:{m['start_line']}-{m['end_line']}` "
                    f"`rep_depth={m.get('rep_depth','')}` `role={m.get('template_role','')}` "
                    f"`owner={m.get('is_owner')}` `bridge={m.get('is_bridge')}` `socket={m.get('is_socket')}`"
                )
            lines.append("")
    lines.append("## AQL query templates")
    lines.append("")
    lines.append("```aql")
    lines.append("FOR d IN declarations")
    lines.append("  FILTER d.socket_debt_tag == true")
    lines.append("  LET owners = (")
    lines.append("    FOR e IN edges")
    lines.append("      FILTER e._to == d._id AND e.kind == \"owns_socket\"")
    lines.append("      RETURN e")
    lines.append("  )")
    lines.append("  FILTER LENGTH(owners) == 0")
    lines.append("  RETURN {")
    lines.append("    name: d.name,")
    lines.append("    module: d.module,")
    lines.append("    rep_depth: d.rep_depth,")
    lines.append("    socket_debt_class: d.socket_debt_class")
    lines.append("  }")
    lines.append("```")
    lines.append("")
    lines.append("```aql")
    lines.append("FOR d IN declarations")
    lines.append("  FILTER d.owner_target_tag == true")
    lines.append("  COLLECT h = d.type_hash_alpha INTO group")
    lines.append("  FILTER LENGTH(group) > 1")
    lines.append("  RETURN {")
    lines.append("    type_hash_alpha: h,")
    lines.append("    declarations: group[*].d.name,")
    lines.append("    modules: group[*].d.module")
    lines.append("  }")
    lines.append("```")
    lines.append("")
    lines.append("```aql")
    lines.append("FOR d IN declarations")
    lines.append("  FILTER d.template_role IN [\"Gate\", \"Bridge\", \"Socket\", \"Witness\"]")
    lines.append("  FILTER d.socket_debt_tag != true AND d.owner_target_tag != true AND d.bridge_target_tag != true")
    lines.append("  RETURN {")
    lines.append("    name: d.name,")
    lines.append("    module: d.module,")
    lines.append("    template_role: d.template_role,")
    lines.append("    status: \"untagged_template_object\"")
    lines.append("  }")
    lines.append("```")
    lines.append("")
    lines.append("## Declaration inventory")
    lines.append("")
    for d in sorted(decls, key=lambda n: n["fqname"]):
        lines.append(
            f"- `{d['fqname']}` [{d['decl_kind']}] "
            f"`type_hash={d.get('type_hash_alpha','')}` `proof_hash={d.get('proof_hash_alpha','')}` "
            f"`rep_depth={d.get('rep_depth','')}` `role={d.get('template_role','')}` "
            f"`socket_debt_class={d.get('socket_debt_class','')}`"
        )
    lines.append("")
    lines.append("## Interpretation")
    lines.append("")
    lines.append("This is a static observability overlay. It is not a kernel proof. Exact duplicates and WL neighborhoods are heuristics for navigation and refactoring priority.")
    (out_dir / f"{stem}.md").write_text("\n".join(lines), encoding="utf-8")


def write_report(graph: Dict[str, Any], out: Path) -> None:
    nodes = graph["nodes"]
    decl_by_id = {n["id"]: n for n in nodes if n["kind"] == "decl"}
    file_nodes = [n for n in nodes if n["kind"] == "file"]
    stats = graph["stats"]
    lines = []
    lines.append("# Lean Graph Overlay / Dedup Report")
    lines.append("")
    lines.append("## Scope")
    lines.append("")
    lines.append(f"Root: `{graph['root']}`")
    lines.append("")
    lines.append("## Static scan summary")
    lines.append("")
    for k,v in stats.items():
        lines.append(f"- `{k}`: **{v}**")
    lines.append("")
    lines.append("## Files")
    lines.append("")
    for f in sorted(file_nodes, key=lambda x: x["path"]):
        lines.append(f"- `{f['path']}` — {f['decl_count']} declarations")
    lines.append("")
    lines.append("## Alpha-normalized duplicate declaration silhouettes")
    lines.append("")
    dups = graph["duplicate_alpha_classes"]
    if not dups:
        lines.append("No duplicate alpha-hash classes found.")
    else:
        for h, ids in sorted(dups.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:50]:
            lines.append(f"### `{h}` ({len(ids)} declarations)")
            for did in ids:
                n = decl_by_id.get(did)
                if n:
                    lines.append(f"- `{n['fqname']}` ({n['decl_kind']}) in `{n['file']}:{n['start_line']}-{n['end_line']}`")
            lines.append("")
    lines.append("## WL duplicate graph neighborhoods")
    lines.append("")
    dups_wl = graph["duplicate_wl_classes"]
    if not dups_wl:
        lines.append("No duplicate WL-hash classes found.")
    else:
        for h, ids in sorted(dups_wl.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:50]:
            lines.append(f"### `{h}` ({len(ids)} declarations)")
            for did in ids:
                n = decl_by_id.get(did)
                if n:
                    lines.append(f"- `{n['fqname']}` ({n['decl_kind']}) in `{n['file']}:{n['start_line']}-{n['end_line']}`")
            lines.append("")
    lines.append("## Strongly connected components in lexical declaration graph")
    lines.append("")
    if not graph["sccs"]:
        lines.append("No nontrivial SCCs found by lexical reference scan.")
    else:
        for comp in graph["sccs"]:
            lines.append("- " + ", ".join(decl_by_id.get(d, {}).get("fqname", d) for d in comp))
    lines.append("")
    lines.append("## Interpretation")
    lines.append("")
    lines.append("This report is a static observability overlay. It is not a Lean proof check and not a kernel-accurate expression hash. The next precision step is a Lean-native exporter over elaborated `Expr`, using de-Bruijn indices and universe normalization, feeding this same JSON schema.")
    out.write_text("\n".join(lines), encoding="utf-8")


def write_html(graph: Dict[str, Any], out: Path) -> None:
    data_json = json.dumps(graph, ensure_ascii=False)
    html_text = f"""<!doctype html>
<html lang=\"en\">
<head>
<meta charset=\"utf-8\"/>
<title>Lean Graph Overlay</title>
<style>
body {{ font-family: system-ui, sans-serif; margin: 2rem; line-height: 1.4; }}
code {{ background: #f4f4f4; padding: 0.1rem 0.25rem; border-radius: 3px; }}
table {{ border-collapse: collapse; width: 100%; margin: 1rem 0; }}
th, td {{ border: 1px solid #ddd; padding: 0.35rem; text-align: left; vertical-align: top; }}
th {{ background: #fafafa; }}
.badge {{ display:inline-block; padding:0.1rem 0.4rem; border-radius:999px; background:#eee; margin-right:0.25rem; }}
.warn {{ background:#ffe9a8; }}
.ok {{ background:#ddf4dd; }}
.small {{ color:#666; font-size:0.9em; }}
</style>
</head>
<body>
<h1>Lean Graph Overlay</h1>
<p class=\"small\">Static dependency/dedup dashboard. No external JavaScript. Not a Lean compile-check.</p>
<div id=\"summary\"></div>
<h2>Duplicate alpha silhouettes</h2>
<div id=\"alpha\"></div>
<h2>Duplicate WL neighborhoods</h2>
<div id=\"wl\"></div>
<h2>Files</h2>
<div id=\"files\"></div>
<script>
const graph = {data_json};
const nodes = Object.fromEntries(graph.nodes.map(n => [n.id, n]));
function esc(s) {{ return String(s).replace(/[&<>]/g, c => {{return {{'&':'&amp;','<':'&lt;','>':'&gt;'}}[c];}}); }}
function table(rows, headers) {{
  let h = '<table><thead><tr>' + headers.map(x=>'<th>'+esc(x)+'</th>').join('') + '</tr></thead><tbody>';
  h += rows.map(r => '<tr>' + r.map(c=>'<td>'+c+'</td>').join('') + '</tr>').join('');
  h += '</tbody></table>'; return h;
}}
document.getElementById('summary').innerHTML = table(Object.entries(graph.stats).map(([k,v])=>[esc(k), '<b>'+esc(v)+'</b>']), ['metric','value']);
const fileRows = graph.nodes.filter(n=>n.kind==='file').sort((a,b)=>a.path.localeCompare(b.path)).map(f=>[esc(f.path), esc(f.decl_count), f.imports.map(esc).join('<br/>')]);
document.getElementById('files').innerHTML = table(fileRows, ['file','decls','imports']);
function dupTable(classes) {{
  const rows = Object.entries(classes).sort((a,b)=>b[1].length-a[1].length).slice(0,100).map(([h, ids]) => {{
    const list = ids.map(id => {{ const n = nodes[id]; return n ? `<code>${{esc(n.fqname)}}</code> <span class=small>${{esc(n.decl_kind)}} ${{esc(n.file)}}:${{n.start_line}}</span>` : esc(id); }}).join('<br/>');
    return ['<code>'+esc(h)+'</code>', esc(ids.length), list];
  }});
  return rows.length ? table(rows, ['hash','count','declarations']) : '<p>No duplicate classes.</p>';
}}
document.getElementById('alpha').innerHTML = dupTable(graph.duplicate_alpha_classes);
document.getElementById('wl').innerHTML = dupTable(graph.duplicate_wl_classes);
</script>
</body>
</html>
"""
    out.write_text(html_text, encoding="utf-8")


def choose_report_stem(root: Path, filter_prefix: str, explicit: str | None = None) -> str:
    if explicit:
        return explicit
    if filter_prefix == "InfoGeometry.Arithmetic" or root.name == "Arithmetic":
        return "prime_boolean_cube_dedupe"
    if filter_prefix:
        tail = filter_prefix.rsplit(".", 1)[-1]
        return f"{tail.lower()}_dedupe"
    return "graph_overlay"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root", type=Path, help="Root directory containing Lean files")
    ap.add_argument("--out-dir", type=Path, default=Path("graph_overlay_out"))
    ap.add_argument("--filter-prefix", default="", help="Restrict the lane-scoped report to this declaration prefix")
    ap.add_argument("--include-tags", default="", help="Comma-separated tag names to preserve in the lane report")
    ap.add_argument("--wl-rounds", type=int, default=4, help="Number of Weisfeiler-Lehman refinement rounds")
    ap.add_argument("--report-stem", default="", help="Override the lane-scoped report filename stem")
    args = ap.parse_args()
    root = args.root.resolve()
    out = args.out_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    graph = build_graph(root, wl_rounds=args.wl_rounds)
    (out / "graph_overlay.json").write_text(json.dumps(graph, ensure_ascii=False, indent=2), encoding="utf-8")
    write_report(graph, out / "graph_overlay_report.md")
    write_html(graph, out / "graph_overlay_dashboard.html")

    if args.filter_prefix:
        lane = filter_graph_by_prefix(graph, args.filter_prefix)
        lane["include_tags"] = [t for t in args.include_tags.split(",") if t]
        lane["wl_rounds"] = args.wl_rounds
        stem = choose_report_stem(root, args.filter_prefix, args.report_stem or None)
        write_lane_report(lane, out, stem)

    print(json.dumps(graph["stats"], indent=2))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
