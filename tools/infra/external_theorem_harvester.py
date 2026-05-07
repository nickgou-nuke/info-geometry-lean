#!/usr/bin/env python3
"""Harvest external theorem-intelligence packets from local formal-library mirrors or arXiv.

This tool deliberately emits proposal-authority `ExternalTheoremCandidatePacket`s.  Foreign
proof status is retrieval guidance only; promotion still requires Lean/build/audit gates.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import html
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Iterable

try:
    from tools.infra.hive_packet_build import build_external_theorem_candidate, stable_json
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
except ImportError:  # pragma: no cover - direct script execution
    ROOT_FOR_IMPORT = Path(__file__).resolve().parents[2]
    if str(ROOT_FOR_IMPORT) not in sys.path:
        sys.path.insert(0, str(ROOT_FOR_IMPORT))
    from tools.infra.hive_packet_build import build_external_theorem_candidate, stable_json
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

ROOT = Path(__file__).resolve().parents[2]

DECL_PATTERNS: dict[str, re.Pattern[str]] = {
    "Isabelle/HOL": re.compile(r"^\s*(?:theorem|lemma|corollary|proposition)\s+([A-Za-z0-9_'.]+)\b(.*)$"),
    "Lean/mathlib": re.compile(r"^\s*(?:theorem|lemma|def|abbrev|instance)\s+([A-Za-z0-9_'.]+)\b(.*)$"),
    "Coq": re.compile(r"^\s*(?:Theorem|Lemma|Corollary|Proposition|Definition)\s+([A-Za-z0-9_'.]+)\b(.*)$"),
    "HOL-Light": re.compile(r"^\s*(?:let|Theorem|Lemma)\s+([A-Za-z0-9_'.]+)\b(.*)$"),
    "Agda": re.compile(r"^\s*([A-Za-z0-9_'.-]+)\s*:(.*)$"),
    "Dedukti": re.compile(r"^\s*([A-Za-z0-9_'.-]+)\s*:(.*)$"),
    "Logipedia": re.compile(r"^\s*([A-Za-z0-9_'.-]+)\s*:(.*)$"),
}

EXTENSIONS_BY_SYSTEM: dict[str, set[str]] = {
    "Isabelle/HOL": {".thy"},
    "Lean/mathlib": {".lean"},
    "Coq": {".v"},
    "HOL-Light": {".ml"},
    "Agda": {".agda", ".lagda"},
    "Dedukti": {".dk"},
    "Logipedia": {".dk", ".lp", ".json", ".txt"},
}

DEFAULT_SYMBOL_MAP = {
    "cblinfun": "ContinuousLinearMap",
    "'a ⇒CL 'b": "E →L[ℂ] F",
    "adj": "ContinuousLinearMap.adjoint",
    "cinner": "inner ℂ",
    "ccsubspace": "Submodule ℂ E",
    "Proj": "orthogonalProjection / IsStarProjection",
    "ell2": "MeasureTheory.Lp ℂ (2 : ℝ≥0∞) Measure.count",
    "L2": "MeasureTheory.Lp ℂ (2 : ℝ≥0∞) μ",
    "L∞": "MeasureTheory.Lp ℂ (∞ : ℝ≥0∞) μ",
}

DEFAULT_IMPORTS_BY_TERM = {
    "adj": "Mathlib.Analysis.InnerProductSpace.Adjoint",
    "adjoint": "Mathlib.Analysis.InnerProductSpace.Adjoint",
    "projection": "Mathlib.Analysis.InnerProductSpace.Projection",
    "projector": "Mathlib.Analysis.InnerProductSpace.Projection",
    "loewner": "Mathlib.Analysis.InnerProductSpace.PiL2",
    "blt": "Mathlib.Analysis.NormedSpace.BoundedLinearMaps",
    "bounded": "Mathlib.Analysis.Normed.Operator.Basic",
    "operator": "Mathlib.Analysis.Normed.Operator.Basic",
    "l2": "Mathlib.MeasureTheory.Function.L2Space",
    "lp": "Mathlib.MeasureTheory.Function.Holder",
    "holder": "Mathlib.MeasureTheory.Function.Holder",
    "count": "Mathlib.MeasureTheory.Measure.Count",
    "matrix": "Mathlib.LinearAlgebra.Matrix.Adjugate",
}

SOURCE_SYSTEM_BY_ALIAS = {
    "isabelle": "Isabelle/HOL",
    "isabelle-afp": "Isabelle/HOL",
    "afp": "Isabelle/HOL",
    "mathlib": "Lean/mathlib",
    "lean": "Lean/mathlib",
    "coq": "Coq",
    "hol-light": "HOL-Light",
    "agda": "Agda",
    "dedukti": "Dedukti",
    "logipedia": "Logipedia",
    "logipedia-web": "Logipedia",
    "logipedia-site": "Logipedia",
    "afp-entry": "Isabelle/HOL",
    "isabelle-afp-entry": "Isabelle/HOL",
    "arxiv": "arXiv",
    "local-failure-memory": "local_lean_failure_memory",
    "local-hive-memory": "local_hive_packet_memory",
}


def normalize_source_system(value: str) -> str:
    return SOURCE_SYSTEM_BY_ALIAS.get(value.strip().lower(), value.strip())


def iter_files(inputs: list[str], source_system: str) -> Iterable[Path]:
    wanted = EXTENSIONS_BY_SYSTEM.get(source_system)
    for raw in inputs:
        path = Path(raw)
        if not path.is_absolute():
            path = (ROOT / path).resolve()
        if path.is_file():
            if not wanted or path.suffix in wanted:
                yield path
            continue
        if path.is_dir():
            for child in sorted(path.rglob("*")):
                if child.is_file() and (not wanted or child.suffix in wanted):
                    yield child


def query_terms(args: argparse.Namespace) -> list[str]:
    terms: list[str] = []
    for q in args.query or []:
        terms.extend([t.strip() for t in re.split(r"[,\s]+", q) if t.strip()])
    return list(dict.fromkeys(terms))


def matches_query(text: str, terms: list[str]) -> bool:
    if not terms:
        return True
    lowered = text.lower()
    return any(term.lower() in lowered for term in terms)


def default_imports(terms: list[str], statement: str) -> list[str]:
    out = []
    haystack = " ".join(terms + [statement]).lower()
    for key, imp in DEFAULT_IMPORTS_BY_TERM.items():
        if key in haystack:
            out.append(imp)
    if not out:
        out.append("Mathlib")
    return list(dict.fromkeys(out))


def default_symbol_map(statement: str) -> dict[str, str]:
    lowered = statement.lower()
    out = {}
    for foreign, lean in DEFAULT_SYMBOL_MAP.items():
        if foreign.lower() in lowered:
            out[foreign] = lean
    if not out:
        out = {"foreign theorem statement": "Lean/mathlib native theorem or adapter surface"}
    return out


def classify(statement: str) -> tuple[str, str, str]:
    lowered = statement.lower()
    if any(x in lowered for x in ["adj", "projection", "projector", "bounded", "loewner", "l2", "lp", "matrix"]):
        return "requires_adapter", "requires_adapter", "adapter"
    return "discovered", "unclassified", "proof_sketch"


def module_name_for(path: Path, source_system: str) -> str:
    stem = path.with_suffix("").name
    if source_system == "Isabelle/HOL":
        return stem
    try:
        rel = path.relative_to(ROOT)
    except ValueError:
        rel = path
    return ".".join(rel.with_suffix("").parts[-4:])


def parse_local_declarations(args: argparse.Namespace, terms: list[str]) -> list[dict[str, Any]]:
    source_system = normalize_source_system(args.source)
    pattern = DECL_PATTERNS.get(source_system)
    if pattern is None:
        raise SystemExit(f"ERROR: no local declaration parser for source system: {source_system}")
    rows = []
    for path in iter_files(args.input, source_system):
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError as exc:
            print(f"WARN: could not read {path}: {exc}", file=sys.stderr)
            continue
        for idx, line in enumerate(lines, start=1):
            match = pattern.match(line)
            if not match:
                continue
            decl = match.group(1)
            raw = line.strip()
            if not matches_query(f"{decl} {raw} {path}", terms):
                continue
            status, translation_status, mode = classify(raw)
            rows.append(
                {
                    "source_system": source_system,
                    "source_library": args.source_library or source_system,
                    "source_module": args.source_module or module_name_for(path, source_system),
                    "source_decl": decl,
                    "source_path": str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path),
                    "source_line_start": idx,
                    "source_line_end": idx,
                    "source_statement_raw": raw,
                    "normalized_statement": raw,
                    "status": status,
                    "translation_status": translation_status,
                    "proof_transport_mode": mode,
                    "lean_import_candidates": default_imports(terms, raw),
                    "symbol_map": default_symbol_map(raw),
                }
            )
            if args.limit and len(rows) >= args.limit:
                return rows
    return rows


def text_from_html(raw: str) -> str:
    text = re.sub(r"<script\b.*?</script>", " ", raw, flags=re.I | re.S)
    text = re.sub(r"<style\b.*?</style>", " ", text, flags=re.I | re.S)
    text = re.sub(r"<[^>]+>", " ", text)
    return re.sub(r"\s+", " ", html.unescape(text)).strip()


def fetch_text(url: str, timeout: int) -> str:
    req = urllib.request.Request(url, headers={"User-Agent": "InfoGeometry external theorem harvester"})
    with urllib.request.urlopen(req, timeout=timeout) as response:
        return response.read().decode("utf-8", errors="replace")


def absolutize_url(base: str, link: str) -> str:
    return urllib.parse.urljoin(base, html.unescape(link))


def parse_logipedia_search_or_detail(args: argparse.Namespace, terms: list[str]) -> list[dict[str, Any]]:
    """Harvest theorem metadata from live Logipedia HTML pages.

    This intentionally records Logipedia/Dedukti as theorem intelligence only.  The site
    exposes exported Lean/Coq/PVS downloads, but those artifacts are still foreign proof
    guidance until reconstructed and checked by this repository's Lean build.
    """
    urls = args.web_url or []
    rows: list[dict[str, Any]] = []
    detail_links: list[str] = []
    for url in urls:
        raw = fetch_text(url, args.timeout)
        for link in re.findall(r'href=["\']([^"\']*theorems\.php\?[^"\']+)["\']', raw):
            detail_links.append(absolutize_url(url, link))
        if "theorems.php?" in url or re.search(r"<legend[^>]*>\s*(?:Theorem|Axiom|Definition|Constant|Type Operator)\s*</legend>", raw, re.I):
            detail_links.append(url)
    # Keep deterministic order and respect --limit before fetching too much.
    seen: set[str] = set()
    detail_links = [u for u in detail_links if not (u in seen or seen.add(u))]
    if args.limit:
        detail_links = detail_links[: args.limit]
    for url in detail_links:
        raw = fetch_text(url, args.timeout)
        page_text = text_from_html(raw)
        theorem_match = re.search(r"(?:Theorem|Axiom|Definition|Constant|Type Operator)\s+([A-Za-z0-9_.'-]+)", page_text)
        statement_match = re.search(
            r"Statement\s+(.+?)(?:Main Dependencies|Dependencies|Download|Coq|Lean|PVS|OpenTheory|$)",
            page_text,
            flags=re.S,
        )
        parsed = urllib.parse.parse_qs(urllib.parse.urlparse(url).query)
        module = (parsed.get("md") or [""])[0]
        decl = (parsed.get("id") or [""])[0]
        kind = (parsed.get("kind") or ["theorem"])[0]
        source_decl = theorem_match.group(1) if theorem_match else f"{module}.{decl}".strip(".")
        statement = statement_match.group(1).strip() if statement_match else page_text[:500]
        if not matches_query(f"{source_decl} {statement} {module} {kind}", terms):
            continue
        status, translation_status, mode = classify(statement)
        rows.append(
            {
                "source_system": "Logipedia",
                "source_library": args.source_library or "Logipedia/Dedukti",
                "source_module": args.source_module or module or "logipedia",
                "source_decl": source_decl,
                "source_url": url,
                "source_statement_raw": statement,
                "normalized_statement": statement,
                "status": status,
                "translation_status": translation_status,
                "proof_transport_mode": "dedukti" if mode == "proof_sketch" else mode,
                "lean_import_candidates": default_imports(terms, statement),
                "symbol_map": default_symbol_map(statement)
                | {"Dedukti proof object": "Lean theorem reconstruction guidance"},
            }
        )
    return rows


def parse_afp_entry_pages(args: argparse.Namespace, terms: list[str]) -> list[dict[str, Any]]:
    """Harvest Isabelle AFP entry metadata without downloading the AFP tarball."""
    rows: list[dict[str, Any]] = []
    for url in args.web_url or []:
        raw = fetch_text(url, args.timeout)
        page_text = text_from_html(raw)
        title_match = re.search(r"<title>(.*?)</title>", raw, flags=re.I | re.S)
        title = text_from_html(title_match.group(1)) if title_match else "AFP entry"
        abstract_match = re.search(r"Abstract\s+(.+?)(?:License|Topics|Session|Depends on|Used by|Cite|Download|$)", page_text, flags=re.S)
        abstract = abstract_match.group(1).strip() if abstract_match else page_text[:1200]
        session_match = re.search(r"Session\s+([A-Za-z0-9_'.-]+)", page_text)
        session = session_match.group(1) if session_match else Path(urllib.parse.urlparse(url).path).stem
        theory_links = [
            absolutize_url(url, link)
            for link in re.findall(r'href=["\']([^"\']*thys/[^"\']+\.html)["\']', raw)
        ]
        theory_names = [Path(urllib.parse.urlparse(link).path).stem for link in theory_links]
        haystack = f"{title} {abstract} {session} {' '.join(theory_names)}"
        if not matches_query(haystack, terms):
            continue
        status, translation_status, mode = classify(haystack)
        if theory_names:
            modules = theory_names[: args.limit or len(theory_names)]
        else:
            modules = [session]
        for module in modules:
            rows.append(
                {
                    "source_system": "Isabelle/HOL",
                    "source_library": args.source_library or f"AFP/{session}",
                    "source_module": args.source_module or module,
                    "source_decl": f"{session}.{module}.entry_surface",
                    "source_url": url,
                    "source_statement_raw": f"{title}: {abstract}",
                    "normalized_statement": f"AFP entry {session}/{module}: {abstract}",
                    "status": status,
                    "translation_status": translation_status,
                    "proof_transport_mode": mode,
                    "lean_import_candidates": default_imports(terms, abstract),
                    "symbol_map": default_symbol_map(abstract)
                    | {"Isabelle/HOL theorem": "Lean/mathlib theorem or adapter surface"},
                }
            )
            if args.limit and len(rows) >= args.limit:
                return rows
    return rows

def fetch_arxiv(args: argparse.Namespace, terms: list[str]) -> list[dict[str, Any]]:
    query = " ".join(args.query or [])
    if not query:
        raise SystemExit("ERROR: arXiv source requires --query")
    encoded = urllib.parse.quote_plus(f"all:{query}")
    url = (
        "https://export.arxiv.org/api/query?"
        f"search_query={encoded}&max_results={args.limit or 10}&sortBy=relevance&sortOrder=descending"
    )
    with urllib.request.urlopen(url, timeout=args.timeout) as response:
        data = response.read()
    ns = {"a": "http://www.w3.org/2005/Atom"}
    root = ET.fromstring(data)
    rows = []
    for entry in root.findall("a:entry", ns):
        title = (entry.findtext("a:title", default="", namespaces=ns) or "").strip().replace("\n", " ")
        summary = (entry.findtext("a:summary", default="", namespaces=ns) or "").strip().replace("\n", " ")
        entry_url = (entry.findtext("a:id", default="", namespaces=ns) or "").strip()
        arxiv_id = entry_url.rsplit("/abs/", 1)[-1]
        raw = f"{title}: {summary}"
        status, translation_status, mode = "discovered", "unclassified", "research_guidance"
        rows.append(
            {
                "source_system": "arXiv",
                "source_library": "arXiv",
                "source_module": arxiv_id,
                "source_decl": title[:96] or arxiv_id,
                "source_url": entry_url,
                "source_statement_raw": raw,
                "normalized_statement": raw,
                "status": status,
                "translation_status": translation_status,
                "proof_transport_mode": mode,
                "lean_import_candidates": default_imports(terms, raw),
                "symbol_map": {"paper result": "Lean theorem target or research-only guidance"},
            }
        )
    return rows


def namespace_from_module(module: str) -> str:
    cleaned = module.strip()
    if not cleaned:
        return "InfoGeometry.ExternalTheoremHive"
    if cleaned.endswith(".lean") or "/" in cleaned:
        cleaned = Path(cleaned).with_suffix("").name
    return cleaned.replace("/", ".")


def build_packet(args: argparse.Namespace, row: dict[str, Any], terms: list[str]) -> dict[str, Any]:
    symbol_map_args = [f"{k}={v}" for k, v in row.get("symbol_map", {}).items()]
    ns = argparse.Namespace(
        out="",
        id="",
        lineage_id=args.lineage_id,
        revision=1,
        origin_run_id=args.origin_run_id,
        created_at="",
        updated_at="",
        created_by_agent="external-theorem-harvester",
        agent_role="retrieval_bee",
        backend="local",
        task_id=args.task_id,
        session_key="",
        tag=["external-theorem-hive", normalize_source_system(args.source)],
        notes=args.notes,
        parent_ref=[],
        evidence_ref=[],
        source_hash=[],
        representation_class=args.representation_class,
        representation_depth=args.representation_depth,
        validate=False,
        status=row["status"],
        packet_version="1.0.0",
        packet_hash="",
        source_system=row["source_system"],
        source_library=row["source_library"],
        source_module=row["source_module"],
        source_decl=row["source_decl"],
        source_url=row.get("source_url", args.source_url or ""),
        source_path=row.get("source_path", ""),
        source_line_start=int(row.get("source_line_start", 0) or 0),
        source_line_end=int(row.get("source_line_end", 0) or 0),
        source_statement_raw=row["source_statement_raw"],
        normalized_statement=row["normalized_statement"],
        lean_target_namespace=args.target_namespace or namespace_from_module(args.target_module),
        lean_candidate_statement=args.lean_candidate_statement,
        lean_import_candidate=args.lean_import_candidate or row.get("lean_import_candidates", []),
        lean_target_module_candidate=[args.target_module] if args.target_module else [],
        symbol_map=args.symbol_map or symbol_map_args,
        proof_transport_mode=row["proof_transport_mode"],
        translation_status=row["translation_status"],
        external_proof_object_ref=args.external_proof_object_ref,
        correspondence_notes=args.correspondence_notes,
        operator_gap_id=args.operator_gap_id,
        query_term=terms,
        source_ref=[f"{row.get('source_url') or row.get('source_path') or row['source_library']}|external_source|source_guidance|0.8"],
        required_gate=["lean_checked", "build_checked", "audit_checked"],
    )
    packet = build_external_theorem_candidate(ns)
    errors = validate_packet(packet, SCHEMA_BY_KIND["ExternalTheoremCandidatePacket"], build_store())
    if errors:
        raise SystemExit("ERROR: generated invalid packet:\n" + "\n".join(f"- {e}" for e in errors))
    return packet


def write_outputs(args: argparse.Namespace, packets: list[dict[str, Any]]) -> None:
    out = Path(args.out)
    if not out.is_absolute():
        out = (ROOT / out).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8") as handle:
        for packet in packets:
            handle.write(json.dumps(packet, ensure_ascii=False, sort_keys=True) + "\n")
    if args.split_dir:
        split_dir = Path(args.split_dir)
        if not split_dir.is_absolute():
            split_dir = (ROOT / split_dir).resolve()
        split_dir.mkdir(parents=True, exist_ok=True)
        for packet in packets:
            (split_dir / f"{packet['id']}.json").write_text(stable_json(packet), encoding="utf-8")
    print(f"external theorem packets written: {out} ({len(packets)} packets)")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", required=True, help="isabelle-afp|mathlib|coq|dedukti|logipedia|arxiv|...")
    p.add_argument("--input", action="append", default=[], help="Local source file or directory. Repeatable.")
    p.add_argument("--query", action="append", default=[], help="Search query/terms. Repeatable.")
    p.add_argument("--source-library", default="", help="Override source library label.")
    p.add_argument("--source-module", default="", help="Override source module label.")
    p.add_argument("--source-url", default="", help="Optional source URL for local harvest rows.")
    p.add_argument(
        "--web-url",
        action="append",
        default=[],
        help="Live source page to harvest without downloading bulk archives. Supports Logipedia theorem/search pages and AFP entry pages.",
    )
    p.add_argument("--target-module", default="InfoGeometry.OperatorAlgebra.ExternalTheoremHive")
    p.add_argument("--target-namespace", default="InfoGeometry.OperatorAlgebra.ExternalTheoremHive")
    p.add_argument("--lean-candidate-statement", default="")
    p.add_argument("--lean-import-candidate", action="append", default=[])
    p.add_argument("--symbol-map", action="append", default=[], help="Override symbol map FOREIGN=LEAN; repeatable.")
    p.add_argument("--external-proof-object-ref", default="")
    p.add_argument("--correspondence-notes", default="")
    p.add_argument("--operator-gap-id", default="")
    p.add_argument("--lineage-id", default="external-theorem-hive")
    p.add_argument("--origin-run-id", default="")
    p.add_argument("--task-id", default="")
    p.add_argument("--notes", default="foreign theorem intelligence; not proof authority")
    p.add_argument("--representation-class", default="translator", choices=["owner", "translator", "coherence", "capstone", "shadow"])
    p.add_argument("--representation-depth", action="append", default=["operatorial"], choices=["scalar", "finite_matrix", "projective", "hilbert", "operatorial", "krein", "von_neumann", "type_iii", "categorical"])
    p.add_argument("--limit", type=int, default=100)
    p.add_argument("--timeout", type=int, default=30)
    p.add_argument("--out", required=True)
    p.add_argument("--split-dir", default="", help="Optional directory for one JSON packet per file.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    terms = query_terms(args)
    source_system = normalize_source_system(args.source)
    if source_system == "arXiv":
        rows = fetch_arxiv(args, terms)
    elif args.web_url and source_system == "Logipedia":
        rows = parse_logipedia_search_or_detail(args, terms)
    elif args.web_url and source_system == "Isabelle/HOL":
        rows = parse_afp_entry_pages(args, terms)
    else:
        if not args.input:
            raise SystemExit("ERROR: local sources require at least one --input path, or use --web-url for Logipedia/AFP entry pages")
        rows = parse_local_declarations(args, terms)
    packets = [build_packet(args, row, terms) for row in rows]
    write_outputs(args, packets)


if __name__ == "__main__":
    main()
