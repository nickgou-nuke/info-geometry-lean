#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import default_decl_index_dir, default_decl_metadata_file, repo_root
else:
    from tools.pathing import default_decl_index_dir, default_decl_metadata_file, repo_root


ROOT = repo_root()
DEFAULT_JSON = "reports/dag/module-theory-program.json"
DEFAULT_MD = "reports/dag/module-theory-program.md"
ROOT_PREFIXES = (
    "lean/InfoGeometry/Core/",
    "lean/InfoGeometry/MaxEnt/",
    "lean/InfoGeometry/Convex/",
    "lean/InfoGeometry/Geometry/",
)

KEYWORD_EXPANSIONS: dict[str, list[str]] = {
    "aqft": [
        "aqft",
        "algebraic quantum field theory",
        "haag",
        "kastler",
        "cstar",
        "operator algebra",
    ],
    "calabi": ["calabi", "yau", "kahler", "monge ampere", "ricci", "einstein equation"],
    "yau": ["calabi conjecture", "complex monge ampere", "kahler einstein"],
    "conformal": ["conformal", "weyl anomaly", "trace anomaly", "projector commutator"],
    "grand": ["unification", "canopy", "closure", "branch", "trunk", "root"],
    "synthesis": ["coherence", "intertwiner", "closure theorem", "isomorphism"],
    "modular": ["tomita", "takesaki", "kms", "modular hamiltonian"],
    "dirac": ["spectral triple", "dirac operator", "index formula"],
    "bott": ["bott", "kk-theory", "kasparov", "clifford"],
    "projective": ["projective", "ray", "simplex", "normalization"],
    "thermo": ["gibbs", "entropy", "free energy", "sinkhorn"],
}

STOPWORDS = {
    "info",
    "geometry",
    "canonical",
    "module",
    "all",
    "bridge",
    "core",
    "interface",
    "theory",
}

SCAN_SUFFIXES = {".lean", ".md", ".py", ".txt"}
SCAN_DIRS = ("lean", "docs", "tools", "scripts")

LITERATURE_BY_TOPIC: dict[str, list[dict[str, str]]] = {
    "aqft": [
        {
            "title": "Haag–Kastler (1964): An Algebraic Approach to Quantum Field Theory",
            "url": "https://doi.org/10.1063/1.1704187",
            "why": "Foundational net-of-algebras AQFT source.",
        },
        {
            "title": "Haag (book): Local Quantum Physics",
            "url": "https://link.springer.com/book/10.1007/978-3-642-61458-3",
            "why": "Canonical AQFT reference text.",
        },
    ],
    "modular": [
        {
            "title": "Takesaki (1970): Tomita's Theory of Modular Hilbert Algebras",
            "url": "https://link.springer.com/book/10.1007/BFb0065832",
            "why": "Classical modular-theory owner lane.",
        },
        {
            "title": "Araki (1976): Relative Entropy of States of von Neumann Algebras",
            "url": "https://projecteuclid.org/euclid.cmp/1103899848",
            "why": "Relative modular entropy source.",
        },
    ],
    "calabi": [
        {
            "title": "Yau (1978): On the Ricci Curvature of a Compact Kähler Manifold and the Complex Monge–Ampère Equation I",
            "url": "https://doi.org/10.1002/cpa.3160310304",
            "why": "Calabi conjecture closure backbone.",
        },
        {
            "title": "Aubin (1978): Équations du type Monge–Ampère sur les variétés kählériennes compactes",
            "url": "https://doi.org/10.24033/bsmf.1876",
            "why": "Continuity-method companion line.",
        },
    ],
    "conformal": [
        {
            "title": "Deser–Schwimmer (1993): Geometric classification of conformal anomalies",
            "url": "https://doi.org/10.1016/0370-2693(93)90934-A",
            "why": "Type-A/Type-B anomaly classification owner.",
        },
        {
            "title": "Duff (1994): Twenty years of the Weyl anomaly",
            "url": "https://arxiv.org/abs/hep-th/9308075",
            "why": "Comprehensive Weyl anomaly review.",
        },
        {
            "title": "Henningson–Skenderis (1998): The holographic Weyl anomaly",
            "url": "https://arxiv.org/abs/hep-th/9806087",
            "why": "Holographic anomaly bridge.",
        },
    ],
    "bott": [
        {
            "title": "Kasparov (1981): The operator K-functor and extensions of C*-algebras",
            "url": "https://doi.org/10.1070/IM1981v016n03ABEH001320",
            "why": "KK-theory owner source.",
        },
        {
            "title": "Higson–Kasparov (2001): E-theory and KK-theory for groups acting on Hilbert space",
            "url": "https://doi.org/10.1007/s002220000118",
            "why": "Modern KK closure lane.",
        },
        {
            "title": "Wood (1966): Banach algebras and Bott periodicity",
            "url": "https://doi.org/10.1016/0040-9383(66)90035-8",
            "why": "C*-algebra Bott periodicity bridge.",
        },
    ],
}

TOPIC_BY_KEYWORD: dict[str, str] = {
    "aqft": "aqft",
    "haag": "aqft",
    "kastler": "aqft",
    "cstar": "aqft",
    "operator algebra": "aqft",
    "modular": "modular",
    "kms": "modular",
    "tomita": "modular",
    "takesaki": "modular",
    "calabi": "calabi",
    "yau": "calabi",
    "kahler": "calabi",
    "monge ampere": "calabi",
    "ricci": "calabi",
    "einstein equation": "calabi",
    "conformal": "conformal",
    "weyl anomaly": "conformal",
    "trace anomaly": "conformal",
    "bott": "bott",
    "kk-theory": "bott",
    "kasparov": "bott",
    "clifford": "bott",
}


@dataclass(frozen=True)
class PathHit:
    start: str
    root: str
    depth: int
    path: list[str]


def rel(path: str | Path) -> str:
    p = Path(path)
    if p.is_absolute():
        try:
            return p.resolve().relative_to(ROOT.resolve()).as_posix()
        except Exception:
            return p.as_posix()
    return p.as_posix()


def split_camel(token: str) -> list[str]:
    return re.findall(r"[A-Z]+(?=[A-Z][a-z]|\b)|[A-Z]?[a-z]+|\d+", token)


def decl_belongs_to_module(module: str, row: dict[str, Any]) -> bool:
    """
    In this repository, canonical umbrella modules frequently re-export or split declarations
    across source files where `row["module"]` is not equal to the umbrella module, while the
    declaration `name` still lives under the expected namespace prefix.
    """
    m = str(row.get("module", ""))
    if m == module:
        return True
    name = str(row.get("name", ""))
    return bool(name) and (name == module or name.startswith(f"{module}."))


def extract_keywords(module: str) -> list[str]:
    out: list[str] = []
    for part in module.split("."):
        for t in split_camel(part):
            k = t.lower().strip()
            if len(k) <= 2 or k in STOPWORDS:
                continue
            out.append(k)
            out.extend(KEYWORD_EXPANSIONS.get(k, []))
    seen: set[str] = set()
    dedup: list[str] = []
    for k in out:
        k2 = re.sub(r"\s+", " ", k.strip().lower())
        if not k2 or k2 in seen:
            continue
        seen.add(k2)
        dedup.append(k2)
    return dedup


def iter_scan_files() -> list[Path]:
    files: list[Path] = []
    for d in SCAN_DIRS:
        base = ROOT / d
        if not base.exists():
            continue
        for p in base.rglob("*"):
            if p.is_file() and p.suffix in SCAN_SUFFIXES:
                files.append(p)
    return files


def count_keyword_in_text(text: str, keyword: str) -> int:
    key = keyword.lower()
    if " " in key:
        return text.count(key)
    pattern = re.compile(rf"\b{re.escape(key)}\b", re.IGNORECASE)
    return len(pattern.findall(text))


def repo_keyword_scan(keywords: list[str], *, top_files: int) -> dict[str, Any]:
    files = iter_scan_files()
    file_text_cache: dict[Path, str] = {}
    for f in files:
        try:
            file_text_cache[f] = f.read_text(encoding="utf-8", errors="ignore").lower()
        except Exception:
            file_text_cache[f] = ""

    keyword_totals: dict[str, int] = {}
    keyword_top_files: dict[str, list[dict[str, Any]]] = {}
    global_file_counter: Counter[str] = Counter()

    for kw in keywords:
        per_file: Counter[str] = Counter()
        total = 0
        for f, txt in file_text_cache.items():
            c = count_keyword_in_text(txt, kw)
            if c <= 0:
                continue
            rp = rel(f)
            per_file[rp] += c
            total += c
            global_file_counter[rp] += c
        keyword_totals[kw] = total
        keyword_top_files[kw] = [
            {"file": fp, "count": int(cnt)} for fp, cnt in per_file.most_common(top_files)
        ]

    return {
        "scanned_file_total": len(files),
        "keyword_totals": keyword_totals,
        "keyword_top_files": keyword_top_files,
        "global_top_files": [
            {"file": fp, "count": int(cnt)} for fp, cnt in global_file_counter.most_common(top_files)
        ],
    }


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            raw = json.loads(line)
        except Exception:
            continue
        if isinstance(raw, dict):
            rows.append(raw)
    return rows


def shortest_root_path(
    start: str,
    adj: dict[str, list[str]],
    root_decls: set[str],
    max_depth: int,
) -> PathHit | None:
    q: deque[tuple[str, int]] = deque([(start, 0)])
    parent: dict[str, str | None] = {start: None}
    while q:
        node, depth = q.popleft()
        if node in root_decls and node != start:
            path: list[str] = []
            cur: str | None = node
            while cur is not None:
                path.append(cur)
                cur = parent[cur]
            path.reverse()
            return PathHit(start=start, root=node, depth=max(0, len(path) - 1), path=path)
        if depth >= max_depth:
            continue
        for nxt in adj.get(node, []):
            if nxt in parent:
                continue
            parent[nxt] = node
            q.append((nxt, depth + 1))
    return None


def dependency_trace(
    module: str,
    *,
    decls_path: Path,
    edges_path: Path,
    max_depth: int,
    sample: int,
) -> dict[str, Any]:
    decls = load_jsonl(decls_path)
    edges = load_jsonl(edges_path)

    decl_module: dict[str, str] = {}
    decl_file: dict[str, str] = {}
    module_decls: list[str] = []
    root_decls: set[str] = set()

    for row in decls:
        name = str(row.get("name", ""))
        if not name:
            continue
        m = str(row.get("module", ""))
        f = rel(str(row.get("file", "")))
        decl_module[name] = m
        decl_file[name] = f
        if decl_belongs_to_module(module, row):
            module_decls.append(name)
        if any(f.startswith(p) for p in ROOT_PREFIXES):
            root_decls.add(name)

    adj: dict[str, list[str]] = defaultdict(list)
    for row in edges:
        if str(row.get("kind", "")) not in {"value", "type"}:
            continue
        src = str(row.get("src", ""))
        dst = str(row.get("dst", ""))
        if not src or not dst:
            continue
        if src not in decl_module or dst not in decl_module:
            continue
        adj[src].append(dst)

    hits: list[PathHit] = []
    for start in module_decls:
        h = shortest_root_path(start, adj, root_decls, max_depth=max_depth)
        if h is not None:
            hits.append(h)

    hits.sort(key=lambda h: (h.depth, h.start, h.root))
    roots_reached = len({h.root for h in hits})
    start_reaching = len({h.start for h in hits})

    return {
        "module_decl_total": len(module_decls),
        "root_decl_total": len(root_decls),
        "module_decl_reaching_roots": start_reaching,
        "distinct_roots_reached": roots_reached,
        "path_hits": [
            {
                "start": h.start,
                "start_file": decl_file.get(h.start, ""),
                "root": h.root,
                "root_file": decl_file.get(h.root, ""),
                "depth": h.depth,
                "path": h.path,
            }
            for h in hits[:sample]
        ],
    }


def candidate_decls_for_module(
    module: str,
    *,
    decls_path: Path,
    top: int,
) -> list[str]:
    decls = load_jsonl(decls_path)
    wanted: list[tuple[int, str]] = []
    score_tokens = (
        "closure",
        "bridge",
        "equiv",
        "iso",
        "projective",
        "modular",
        "ricci",
        "entropy",
        "canopy",
        "root",
        "trunk",
    )
    banned_fragments = (
        ".casesOn",
        ".ctorIdx",
        ".noConfusion",
        ".noConfusionType",
        ".rec",
        ".recOn",
        ".brecOn",
        ".below",
        ".mk.inj",
        ".mk.noConfusion",
        ".mk.sizeOf_spec",
    )
    allowed_kinds = {"theorem", "def", "structure", "class", "instance", "abbrev"}
    for row in decls:
        if not decl_belongs_to_module(module, row):
            continue
        name = str(row.get("name", ""))
        if not name:
            continue
        if any(b in name for b in banned_fragments):
            continue
        kind = str(row.get("kind", "")).lower()
        if kind and kind not in allowed_kinds:
            continue
        lname = name.lower()
        score = sum(1 for t in score_tokens if t in lname)
        if kind == "theorem":
            score += 2
        if lname.startswith(f"{module.lower()}."):
            score += 1
        wanted.append((score, name))
    wanted.sort(key=lambda x: (-x[0], x[1]))
    out: list[str] = []
    seen: set[str] = set()
    for _, name in wanted:
        if name in seen:
            continue
        seen.add(name)
        out.append(name)
        if len(out) >= top:
            break
    return out


def formulate_theorem_packet(module: str, key_decls: list[str]) -> list[str]:
    short = module.split(".")[-1]
    base = re.sub(r"[^A-Za-z0-9]", "", short)
    if not key_decls:
        key_decls = [f"{module}.<owner_decl_1>", f"{module}.<owner_decl_2>"]
    conj = " ∧\n      ".join(key_decls[:4])
    return [
        (
            f"theorem {base[0].lower() + base[1:]}_trunk_to_canopy_closure\n"
            f"    (S : {base}CanopyPackage) :\n"
            f"    {conj}"
        ),
        (
            f"theorem {base[0].lower() + base[1:]}_root_factorization\n"
            f"    (S : {base}CanopyPackage) :\n"
            f"    ∃ Φ, ReadoutPreservation Φ ∧ GeneratorPreservation Φ ∧ CoherentClosure Φ"
        ),
        (
            f"theorem {base[0].lower() + base[1:]}_isomorphism_corridor\n"
            f"    (h : {base}BranchHypotheses) :\n"
            f"    Isomorphic {base}TrunkObject {base}CanopyObject"
        ),
    ]


def collect_literature_context(module: str, keywords: list[str]) -> list[dict[str, str]]:
    topics: set[str] = set()
    for kw in keywords:
        t = TOPIC_BY_KEYWORD.get(kw.lower())
        if t:
            topics.add(t)

    # Module-name fallback topic routing.
    low_module = module.lower()
    if "aqft" in low_module:
        topics.add("aqft")
    if "calabi" in low_module or "yau" in low_module:
        topics.add("calabi")
    if "conformal" in low_module or "weyl" in low_module:
        topics.add("conformal")
    if "grand" in low_module or "bott" in low_module:
        topics.add("bott")
        topics.add("modular")

    out: list[dict[str, str]] = []
    seen_urls: set[str] = set()
    for topic in sorted(topics):
        for ref in LITERATURE_BY_TOPIC.get(topic, []):
            url = ref["url"]
            if url in seen_urls:
                continue
            seen_urls.add(url)
            out.append({"topic": topic, **ref})
    return out


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Module-keyword context program: extract keyword lattice, run deep repo scan, "
            "trace trunk->root dependencies, and formulate theorem packets."
        )
    )
    ap.add_argument("--module", action="append", required=True, help="Module name (repeatable)")
    ap.add_argument(
        "--decls",
        default=str(default_decl_metadata_file().relative_to(ROOT)),
        help="Path to DAG decl metadata jsonl",
    )
    ap.add_argument(
        "--edges",
        default=str((default_decl_index_dir() / "edges.jsonl").relative_to(ROOT)),
        help="Path to DAG edges jsonl",
    )
    ap.add_argument("--max-depth", type=int, default=8)
    ap.add_argument("--top-files", type=int, default=12)
    ap.add_argument("--top-decls", type=int, default=8)
    ap.add_argument("--sample-paths", type=int, default=12)
    ap.add_argument("--json-out", default=DEFAULT_JSON)
    ap.add_argument("--md-out", default=DEFAULT_MD)
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    decls_path = ROOT / args.decls
    edges_path = ROOT / args.edges
    out_json = ROOT / args.json_out
    out_md = ROOT / args.md_out

    modules_payload: list[dict[str, Any]] = []
    for module in args.module:
        keywords = extract_keywords(module)
        scan = repo_keyword_scan(keywords, top_files=args.top_files)
        trace = dependency_trace(
            module,
            decls_path=decls_path,
            edges_path=edges_path,
            max_depth=args.max_depth,
            sample=args.sample_paths,
        )
        key_decls = candidate_decls_for_module(module, decls_path=decls_path, top=args.top_decls)
        theorem_packet = formulate_theorem_packet(module, key_decls)
        literature_context = collect_literature_context(module, keywords)
        modules_payload.append(
            {
                "module": module,
                "keywords": keywords,
                "repo_scan": scan,
                "dependency_trace": trace,
                "candidate_declarations": key_decls,
                "theorem_packet": theorem_packet,
                "literature_context": literature_context,
            }
        )

    payload = {
        "schema": "ig.module-keyword-theory-program.v1",
        "modules": modules_payload,
        "inputs": {
            "decls": rel(decls_path),
            "edges": rel(edges_path),
            "max_depth": args.max_depth,
        },
    }

    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    md: list[str] = []
    md.append("# Module Keyword Theory Program")
    md.append("")
    md.append("Generated by `tools/infra/module_keyword_theory_program.py`.")
    md.append("")
    for row in modules_payload:
        md.append(f"## {row['module']}")
        md.append("")
        md.append("### Keywords")
        md.append("")
        md.append(", ".join(f"`{k}`" for k in row["keywords"]) if row["keywords"] else "_none_")
        md.append("")
        md.append("### Literature Context")
        md.append("")
        if row["literature_context"]:
            for ref in row["literature_context"]:
                md.append(
                    f"- [{ref['title']}]({ref['url']}) "
                    f"(`topic: {ref['topic']}`) — {ref['why']}"
                )
        else:
            md.append("_none_")
        md.append("")
        scan = row["repo_scan"]
        trace = row["dependency_trace"]
        md.append("### Repo Scan")
        md.append("")
        md.append(f"- Scanned files: `{scan['scanned_file_total']}`")
        md.append(f"- Module declarations: `{trace['module_decl_total']}`")
        md.append(f"- Declarations reaching roots: `{trace['module_decl_reaching_roots']}`")
        md.append(f"- Distinct roots reached: `{trace['distinct_roots_reached']}`")
        md.append("")
        md.append("Top keyword counts:")
        md.append("")
        md.append("| Keyword | Count |")
        md.append("|---|---:|")
        for k, cnt in sorted(scan["keyword_totals"].items(), key=lambda kv: kv[1], reverse=True)[: args.top_files]:
            md.append(f"| `{k}` | {cnt} |")
        md.append("")
        md.append("Top files (global across module keywords):")
        md.append("")
        md.append("| File | Count |")
        md.append("|---|---:|")
        for tf in scan["global_top_files"][: args.top_files]:
            md.append(f"| `{tf['file']}` | {tf['count']} |")
        md.append("")
        md.append("### Trunk→Root Path Samples")
        md.append("")
        md.append("| Start Decl | Root Decl | Depth |")
        md.append("|---|---|---:|")
        for h in trace["path_hits"]:
            md.append(f"| `{h['start']}` | `{h['root']}` | {h['depth']} |")
        md.append("")
        md.append("### Candidate Declarations")
        md.append("")
        for d in row["candidate_declarations"]:
            md.append(f"- `{d}`")
        md.append("")
        md.append("### Theorem Packet (Draft Surfaces)")
        md.append("")
        for t in row["theorem_packet"]:
            md.append("```lean")
            md.append(t)
            md.append("```")
        md.append("")

    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_md.write_text("\n".join(md) + "\n", encoding="utf-8")

    print(f"[module-theory-program] modules={len(modules_payload)}")
    print(f"[module-theory-program] json={rel(out_json)}")
    print(f"[module-theory-program] md={rel(out_md)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
