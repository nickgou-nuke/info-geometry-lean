"""Tier 4: Read-only real-world corpus & Lean formalization scenarios (7 tests: T4-01..T4-07)."""
from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Any
from urllib.error import URLError

import pytest

from tests.e2e_alexandria_pdf.conftest import (
    ALEXANDRIA_ENDPOINT,
    ALEXANDRIA_PROD_DB,
    ASK_REPO_SCRIPT,
    DEFAULT_CORPUS_REPORT,
    GRAPH_CONTEXT_RANK_SCRIPT,
    GRAPH_RAG_QUERY_SCRIPT,
    INFOGEOMETRY_ENDPOINT,
    REAL_CORPUS_DIR,
    REPO_ROOT,
    RETRIEVE_CONTEXT_SCRIPT,
    _parse_env_file,
    arango_aql,
    arango_collection_count,
    arango_http_json,
    arango_list_collections,
    arango_list_databases,
    arango_list_views,
    assert_retrieval_authority,
    hit_field,
    report_metric,
    require_alexandria_8532,
    run_cli,
)

pytestmark = pytest.mark.tier4

VALID_DAG_EDGE_TYPES = {
    "section_precedes_section",
    "proof_proves_theorem",
    "chunk_uses_definition",
    "chunk_references_result",
    "chunk_cites_entry",
    "document_cites_document",
}


def _live_alexandria_env(user: str, pw: str) -> dict[str, str]:
    return {
        "ALEXANDRIA_ARANGO_ENDPOINT": ALEXANDRIA_ENDPOINT,
        "ALEXANDRIA_ARANGO_DB": ALEXANDRIA_PROD_DB,
        "ALEXANDRIA_ARANGO_USERNAME": user,
        "ALEXANDRIA_ARANGO_PASSWORD": pw,
    }


def _load_corpus_report() -> dict[str, Any]:
    report_path = Path(os.environ.get("ALEXANDRIA_CORPUS_REPORT", str(DEFAULT_CORPUS_REPORT)))
    assert report_path.exists(), (
        f"Corpus inventory report missing at {report_path}. M2 full corpus ingestion must generate it."
    )
    return json.loads(report_path.read_text(encoding="utf-8"))


def _find_unique_doc(unique_docs: list[dict[str, Any]], filename: str) -> dict[str, Any]:
    for entry in unique_docs:
        if Path(str(entry.get("canonicalPath", ""))).name == filename:
            return entry
        if any(Path(str(p)).name == filename for p in (entry.get("duplicatePaths") or [])):
            return entry
    raise AssertionError(f"Expected unique_documents entry matching filename {filename!r}")


def _repo_8530_credentials() -> tuple[str, str]:
    env_override = os.environ.get("HIVE_ARANGO_ENV_FILE")
    env_path = Path(env_override) if env_override else (REPO_ROOT / "configs" / "local" / "hive_arango.env")
    env_data = _parse_env_file(env_path)
    user = (
        os.environ.get("ARANGO_USER")
        or os.environ.get("ARANGO_USERNAME")
        or env_data.get("ARANGO_USER")
        or env_data.get("ARANGO_USERNAME")
        or "root"
    )
    pw = (
        os.environ.get("ARANGO_PASS")
        or os.environ.get("ARANGO_PASSWORD")
        or env_data.get("ARANGO_PASS")
        or env_data.get("ARANGO_PASSWORD")
        or ""
    )
    return user, pw


def _hit_text_blob(h: dict[str, Any]) -> str:
    parts: list[str] = []
    for key in ("title", "path", "text", "snippet"):
        val = h.get(key)
        if val:
            parts.append(str(val))
    chunk = h.get("chunk")
    if isinstance(chunk, dict):
        if chunk.get("text"):
            parts.append(str(chunk["text"]))
        prov = chunk.get("provenance")
        if isinstance(prov, dict) and prov.get("section"):
            parts.append(str(prov["section"]))
    meta = h.get("metadata")
    if isinstance(meta, dict):
        if meta.get("section"):
            parts.append(str(meta["section"]))
    doc = h.get("document")
    if isinstance(doc, dict) and doc.get("title"):
        parts.append(str(doc["title"]))
    for ent_list in (h.get("entities"), meta.get("entities") if isinstance(meta, dict) else None):
        if isinstance(ent_list, list):
            for ent in ent_list:
                if isinstance(ent, dict):
                    for ek in ("surface", "normalized"):
                        if ent.get(ek):
                            parts.append(str(ent[ek]))
    return " ".join(parts).lower()


def _assert_topic_relevance(
    hits: list[dict[str, Any]],
    terms: tuple[str, ...],
    *,
    min_terms: int = 2,
    label: str = "",
) -> None:
    sample = hits[:5] if len(hits) > 5 else hits
    combined = " ".join(_hit_text_blob(h) for h in sample)
    matched = [t for t in terms if t.lower() in combined]
    assert len(matched) >= min_terms, (
        f"[{label}] Expected >= {min_terms} topic terms from {terms!r} in top hits, matched {matched!r}"
    )


def _assert_valid_dag_neighbors(hits: list[dict[str, Any]], *, label: str = "") -> None:
    dags = [
        d
        for h in hits
        for d in (h.get("dagNeighbors") or [])
        if isinstance(d, dict)
    ]
    assert dags, f"[{label}] Expected non-empty dagNeighbors across retrieved hits"
    assert any(
        d.get("edgeType") in VALID_DAG_EDGE_TYPES
        and d.get("direction") in {"inbound", "outbound"}
        and bool(d.get("_id"))
        and bool(d.get("_key"))
        for d in dags
    ), f"[{label}] No valid DAG neighbor entry found in {dags[:3]!r}"


def _assert_graph_rag_alexandria(
    rag_data: dict[str, Any],
    terms: tuple[str, ...],
    *,
    min_terms: int = 2,
    label: str = "",
) -> list[dict[str, Any]]:
    assert rag_data.get("scope") == "alexandria", f"[{label}] scope={rag_data.get('scope')!r}"
    assert rag_data.get("gravity") is None, f"[{label}] gravity should be None"
    assert rag_data.get("authority") == "retrieval_context_only", (
        f"[{label}] authority={rag_data.get('authority')!r}"
    )
    assert rag_data.get("authorities", {}).get("alexandria") == "retrieval_context_only", (
        f"[{label}] authorities={rag_data.get('authorities')!r}"
    )
    assert "not verified lean proof" in str(rag_data.get("disclaimer", "")).lower(), (
        f"[{label}] missing non-proof disclaimer: {rag_data.get('disclaimer')!r}"
    )
    alex_hits = rag_data.get("alexandria", [])
    assert isinstance(alex_hits, list) and len(alex_hits) >= 1, (
        f"[{label}] Expected >= 1 alexandria hit in graph_rag_query"
    )
    for idx, h in enumerate(alex_hits):
        assert h.get("source") == "alexandria", f"[{label}] hit[{idx}] source={h.get('source')!r}"
        assert bool(h.get("path")), f"[{label}] hit[{idx}] missing path"
        meta = h.get("metadata")
        assert isinstance(meta, dict), f"[{label}] hit[{idx}] missing metadata dict"
        assert meta.get("authority") == "retrieval_context_only", (
            f"[{label}] hit[{idx}] metadata.authority={meta.get('authority')!r}"
        )
        assert meta.get("sourceAuthority") == "retrieval_context_only", (
            f"[{label}] hit[{idx}] metadata.sourceAuthority={meta.get('sourceAuthority')!r}"
        )
        assert bool(meta.get("documentKey")), f"[{label}] hit[{idx}] missing metadata.documentKey"
        assert bool(meta.get("contentHash")), f"[{label}] hit[{idx}] missing metadata.contentHash"
        assert meta.get("pageStart") is not None, f"[{label}] hit[{idx}] missing metadata.pageStart"
    _assert_topic_relevance(alex_hits, terms, min_terms=min_terms, label=label)
    return alex_hits


def _require_live_alexandria_corpus() -> tuple[str, str]:
    user, pw = require_alexandria_8532()
    dbs = set(arango_list_databases(ALEXANDRIA_ENDPOINT, user, pw))
    assert ALEXANDRIA_PROD_DB in dbs, (
        f"Live database '{ALEXANDRIA_PROD_DB}' does not exist on {ALEXANDRIA_ENDPOINT}. "
        "M2 full corpus ingestion must run first."
    )
    cols = arango_list_collections(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw)
    assert "alexandria_documents" in cols, "alexandria_documents collection missing in live alexandria DB"
    doc_cnt = arango_collection_count(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw, "alexandria_documents")
    assert doc_cnt >= 1000, (
        f"Live alexandria_documents count is {doc_cnt} (< 1000). M2 full corpus ingestion has not completed."
    )
    return user, pw


def _run_retrieve_live(query: str, user: str, pw: str, top_k: int = 8) -> dict[str, Any]:
    proc = run_cli(
        [
            str(RETRIEVE_CONTEXT_SCRIPT),
            "--arango",
            "--endpoint", ALEXANDRIA_ENDPOINT,
            "--database", ALEXANDRIA_PROD_DB,
            "--query", query,
            "--top-k", str(top_k),
        ],
        env_overrides=_live_alexandria_env(user, pw),
    )
    assert proc.returncode == 0, f"retrieve_context.py --arango failed: {proc.stderr}"
    packet = json.loads(proc.stdout)
    assert_retrieval_authority(packet)
    assert packet.get("target") == {"endpoint": ALEXANDRIA_ENDPOINT, "database": ALEXANDRIA_PROD_DB}, (
        f"Unexpected retrieval target: {packet.get('target')!r}"
    )
    return packet


def test_t4_full_corpus_inventory_accounting_matches_collection_for_formalization() -> None:
    """T4-01: Corpus inventory report accounts for 100% of collection_for_formalization without modifying it."""
    assert REAL_CORPUS_DIR.exists(), f"Source corpus directory missing: {REAL_CORPUS_DIR}"

    report = _load_corpus_report()
    assert report.get("input_dir") == str(REAL_CORPUS_DIR), (
        f"Unexpected input_dir in report: {report.get('input_dir')!r}"
    )
    assert report.get("source_authority") == "retrieval_context_only", (
        f"Unexpected source_authority in report: {report.get('source_authority')!r}"
    )

    total_scanned = report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles")
    unique_cnt = report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs")
    dup_skip = report_metric(report, "duplicateSkipped", "duplicate_skipped", "duplicate_skipped_count", "duplicatesSkipped")
    non_pdf = report_metric(report, "nonPdfSkipped", "non_pdf_skipped", "nonPdfsSkipped")
    total_pdf = report_metric(report, "total_pdf_files", "totalPdfFiles")
    symlinks_skipped = report_metric(report, "symlinks_skipped", "symlinksSkipped")
    pdf_ext_cnt = report_metric(report, "pdf_extension_count", "pdfExtensionCount")
    magic_non_pdf = report_metric(report, "magic_header_non_pdf_ext_count", "magicHeaderNonPdfExtCount")

    assert unique_cnt >= 3500, f"Expected >= 3500 unique PDFs, got {unique_cnt}"
    assert dup_skip >= 1400, f"Expected >= 1400 duplicate skips, got {dup_skip}"
    assert non_pdf >= 45000, f"Expected >= 45000 non-PDF skipped files, got {non_pdf}"
    assert total_pdf == unique_cnt + dup_skip, (
        f"PDF accounting mismatch: {total_pdf} != {unique_cnt} + {dup_skip}"
    )
    assert total_scanned == non_pdf + total_pdf, (
        f"100% accounting invariant failed: {total_scanned} != {non_pdf} + {total_pdf}"
    )
    assert total_pdf == pdf_ext_cnt + magic_non_pdf, (
        f"PDF detection mismatch: {total_pdf} != {pdf_ext_cnt} + {magic_non_pdf}"
    )

    disk_reg = 0
    disk_symlinks = 0
    for root_str, dirnames, filenames in os.walk(REAL_CORPUS_DIR, followlinks=False):
        root_path = Path(root_str)
        for dname in dirnames:
            if (root_path / dname).is_symlink():
                disk_symlinks += 1
        for fname in filenames:
            fpath = root_path / fname
            if fpath.is_symlink():
                disk_symlinks += 1
            elif fpath.is_file():
                disk_reg += 1

    assert disk_reg >= 53000, f"Expected >= 53000 regular files in {REAL_CORPUS_DIR}, got {disk_reg}"
    assert total_scanned >= int(0.95 * disk_reg), (
        f"Report total_scanned_files ({total_scanned}) covers < 95% of on-disk regular files ({disk_reg})"
    )
    assert abs(disk_reg - total_scanned) <= max(250, int(0.02 * disk_reg)), (
        f"Report total_scanned_files ({total_scanned}) diverges too far from disk count ({disk_reg})"
    )
    assert abs(disk_symlinks - symlinks_skipped) <= max(20, int(0.05 * max(1, disk_symlinks))), (
        f"Report symlinks_skipped ({symlinks_skipped}) diverges from disk symlinks ({disk_symlinks})"
    )

    outcome_counts = report.get("outcome_counts", {})
    assert isinstance(outcome_counts, dict)
    assert sum(outcome_counts.values()) == total_pdf, (
        f"sum(outcome_counts)={sum(outcome_counts.values())} != total_pdf_files={total_pdf}"
    )
    assert outcome_counts.get("duplicate_skipped") == dup_skip
    assert sum(v for k, v in outcome_counts.items() if k != "duplicate_skipped") == unique_cnt
    assert outcome_counts.get("ingested", 0) >= 3400
    assert outcome_counts.get("empty_0_bytes", 0) >= 1
    assert outcome_counts.get("scanned_no_text", 0) >= 50

    unique_docs = report.get("unique_documents", [])
    assert isinstance(unique_docs, list) and len(unique_docs) == unique_cnt, (
        f"len(unique_documents)={len(unique_docs)} != unique_cnt={unique_cnt}"
    )
    assert sum(1 for d in unique_docs if d.get("outcome") == "ingested") == outcome_counts["ingested"]

    user, pw = _require_live_alexandria_corpus()
    live_docs_cnt = arango_collection_count(
        ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw, "alexandria_documents"
    )
    assert outcome_counts["ingested"] == live_docs_cnt, (
        f"Report ingested count ({outcome_counts['ingested']}) != live alexandria_documents ({live_docs_cnt})"
    )

    prelim = _find_unique_doc(unique_docs, "preliminaries.ftl.en.pdf")
    assert prelim.get("outcome") == "empty_0_bytes"
    assert prelim.get("sizeBytes") == 0
    assert Path(str(prelim["canonicalPath"])).exists()

    bost = _find_unique_doc(unique_docs, "bostconnesscan.pdf")
    assert bost.get("outcome") == "scanned_no_text"
    assert bost.get("charCount") == 0
    assert Path(str(bost["canonicalPath"])).exists()

    kandkk = _find_unique_doc(unique_docs, "KandKK.pdf")
    assert kandkk.get("outcome") == "scanned_no_text"
    assert kandkk.get("charCount") == 0
    assert Path(str(kandkk["canonicalPath"])).exists()

    ingested_sample = [d for d in unique_docs if d.get("outcome") == "ingested"][:5]
    assert len(ingested_sample) == 5
    for d in ingested_sample:
        assert Path(str(d["canonicalPath"])).exists()
        assert str(d.get("documentKey", "")).startswith("doc_")


def test_t4_live_8532_alexandria_graph_dag_integrity_and_zero_dangling_edges() -> None:
    """T4-02: Live :8532 alexandria has non-empty graph/DAG, 0 dangling edges, and :8530 untouched."""
    user, pw = _require_live_alexandria_corpus()
    views = arango_list_views(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw)
    assert "alexandria_chunks_search" in views

    docs_cnt = arango_collection_count(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw, "alexandria_documents")
    sections_cnt = arango_collection_count(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw, "alexandria_sections")
    chunks_cnt = arango_collection_count(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw, "alexandria_chunks")
    entities_cnt = arango_collection_count(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw, "alexandria_entities")
    dag_cnt = arango_collection_count(ALEXANDRIA_ENDPOINT, ALEXANDRIA_PROD_DB, user, pw, "alexandria_dag_edges")
    assert docs_cnt >= 1000
    assert sections_cnt > 0
    assert chunks_cnt >= 10000
    assert entities_cnt > 0
    assert dag_cnt > 0

    for edge_col in (
        "alexandria_document_section_edges",
        "alexandria_section_chunk_edges",
        "alexandria_chunk_adjacent_edges",
        "alexandria_chunk_entity_edges",
        "alexandria_entity_relation_edges",
        "alexandria_dag_edges",
    ):
        dangling = arango_aql(
            ALEXANDRIA_ENDPOINT,
            ALEXANDRIA_PROD_DB,
            user,
            pw,
            f"FOR e IN {edge_col} FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null LIMIT 5 RETURN e._key",
            timeout=60.0,
        )
        assert dangling == [], f"Dangling edges in live {edge_col}: {dangling}"

    # Sample >= 5 distinct PDFs deterministically showing structured extraction and DAG edges
    sampled = arango_aql(
        ALEXANDRIA_ENDPOINT,
        ALEXANDRIA_PROD_DB,
        user,
        pw,
        (
            "FOR e IN alexandria_dag_edges "
            "COLLECT dk = e.documentKey WITH COUNT INTO dagCount "
            "FILTER dagCount > 0 "
            "SORT dk ASC "
            "LIMIT 10 "
            "LET kinds = UNIQUE(FOR c IN alexandria_chunks FILTER c.documentKey == dk RETURN c.chunkKind) "
            "LET docAuth = DOCUMENT(CONCAT('alexandria_documents/', dk)).sourceAuthority "
            "RETURN {documentKey: dk, dagCount: dagCount, kinds: kinds, sourceAuthority: docAuth}"
        ),
        timeout=60.0,
    )
    assert len(sampled) >= 5, f"Expected >= 5 distinct PDFs with DAG edges, got {len(sampled)}"
    assert all(row.get("sourceAuthority") == "retrieval_context_only" for row in sampled), (
        f"Unexpected sourceAuthority in sampled documents: {sampled!r}"
    )
    all_kinds = {k for row in sampled for k in (row.get("kinds") or []) if k}
    required_kinds = {"theorem", "definition", "proof", "equation"}
    assert required_kinds.issubset(all_kinds), (
        f"Expected structured math kinds {sorted(required_kinds)} in sampled docs, got {sorted(all_kinds)}"
    )

    edge_type_rows = arango_aql(
        ALEXANDRIA_ENDPOINT,
        ALEXANDRIA_PROD_DB,
        user,
        pw,
        "FOR e IN alexandria_dag_edges COLLECT et = e.edgeType WITH COUNT INTO cnt RETURN {edgeType: et, count: cnt}",
        timeout=60.0,
    )
    et_counts = {row["edgeType"]: int(row["count"]) for row in edge_type_rows if row.get("edgeType")}
    for required_et in ("proof_proves_theorem", "chunk_uses_definition", "chunk_references_result", "chunk_cites_entry"):
        assert et_counts.get(required_et, 0) > 0, (
            f"Missing or empty DAG edgeType {required_et!r}; got {et_counts!r}"
        )

    auth_audit = arango_aql(
        ALEXANDRIA_ENDPOINT,
        ALEXANDRIA_PROD_DB,
        user,
        pw,
        (
            "RETURN {"
            "badDocs: LENGTH(FOR d IN alexandria_documents FILTER d.sourceAuthority != 'retrieval_context_only' LIMIT 1 RETURN 1), "
            "badChunks: LENGTH(FOR c IN alexandria_chunks FILTER c.sourceAuthority != 'retrieval_context_only' LIMIT 1 RETURN 1)"
            "}"
        ),
        timeout=60.0,
    )
    assert auth_audit == [{"badDocs": 0, "badChunks": 0}], f"Authority audit failed: {auth_audit!r}"

    # Read-only verify :8530 infogeometry and darwin_commits have zero alexandria_* PDF pollution
    user_8530, pw_8530 = _repo_8530_credentials()
    for db_8530 in ("infogeometry", "darwin_commits"):
        try:
            st, cols_8530 = arango_http_json(
                "GET",
                f"{INFOGEOMETRY_ENDPOINT}/_db/{db_8530}/_api/collection?excludeSystem=true",
                user_8530,
                pw_8530,
                timeout=2.0,
            )
        except (URLError, OSError):
            break
        assert st == 200, f"Unexpected HTTP status {st} querying :8530 DB {db_8530}"
        names_8530 = {c.get("name") for c in cols_8530.get("result", []) if isinstance(c, dict)}
        assert not any(n and n.startswith("alexandria_") for n in names_8530), (
            f"Found unexpected alexandria_* collections on :8530 {db_8530}: {sorted(n for n in names_8530 if n and n.startswith('alexandria_'))}"
        )


def test_t4_scenario_clifford_dirac_hestenes_spinors() -> None:
    """T4-03: Retrieve Clifford / Dirac-Hestenes spinor formalization context from live :8532 corpus."""
    user, pw = _require_live_alexandria_corpus()
    q = "Dirac Hestenes spinor Clifford algebra multivector"
    pkt = _run_retrieve_live(q, user, pw, top_k=8)
    hits = pkt.get("hits", [])
    assert len(hits) >= 3
    doc_keys = {hit_field(h, "documentKey") for h in hits if hit_field(h, "documentKey")}
    assert len(doc_keys) >= 2
    assert all(hit_field(h, "contentHash") and hit_field(h, "pageStart") is not None for h in hits[:3])
    assert any(h.get("entities") for h in hits), "T4-03 retrieve_context hits missing entities"
    _assert_topic_relevance(hits, ("clifford", "dirac", "hestenes", "spinor"), min_terms=2, label="T4-03 retrieve")

    p_rag = run_cli(
        [str(GRAPH_RAG_QUERY_SCRIPT), q, "--scope", "alexandria", "--format", "json", "--no-gravity"],
        env_overrides=_live_alexandria_env(user, pw),
    )
    assert p_rag.returncode == 0, f"stderr={p_rag.stderr}"
    rag_data = json.loads(p_rag.stdout)
    _assert_graph_rag_alexandria(rag_data, ("clifford", "dirac", "hestenes", "spinor"), min_terms=2, label="T4-03 graph_rag")


def test_t4_scenario_split_octonions_g2_albert_jordan_algebra() -> None:
    """T4-04: Retrieve Split Octonions, G2, and Albert Jordan algebra context from live :8532 corpus."""
    user, pw = _require_live_alexandria_corpus()
    q = "split octonions exceptional Lie algebra G2 Jordan algebra"
    pkt = _run_retrieve_live(q, user, pw, top_k=8)
    hits = pkt.get("hits", [])
    assert len(hits) >= 3
    doc_keys = {hit_field(h, "documentKey") for h in hits if hit_field(h, "documentKey")}
    assert len(doc_keys) >= 2
    assert all(hit_field(h, "contentHash") and hit_field(h, "pageStart") is not None for h in hits[:3])
    assert any(h.get("entities") for h in hits), "T4-04 retrieve_context hits missing entities"
    _assert_topic_relevance(hits, ("octonion", "jordan", "lie", "g2"), min_terms=2, label="T4-04 retrieve")

    p_rank = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--arango",
            "--endpoint", ALEXANDRIA_ENDPOINT,
            "--database", ALEXANDRIA_PROD_DB,
            "--query", q,
            "--top-k", "6",
        ],
        env_overrides=_live_alexandria_env(user, pw),
    )
    assert p_rank.returncode == 0, f"stderr={p_rank.stderr}"
    ranked = json.loads(p_rank.stdout)
    assert_retrieval_authority(ranked)
    assert ranked.get("target") == {"endpoint": ALEXANDRIA_ENDPOINT, "database": ALEXANDRIA_PROD_DB}
    assert ranked.get("graph", {}).get("nodeCount", 0) > 0
    assert ranked.get("graph", {}).get("edgeCount", 0) > 0
    assert len(ranked.get("seeds", [])) >= 1
    rhits = ranked.get("hits", [])
    assert len(rhits) >= 3
    assert all(
        hit_field(h, "documentKey")
        and hit_field(h, "contentHash")
        and hit_field(h, "pageStart") is not None
        and "graphScore" in h
        and "lexicalScore" in h
        for h in rhits
    )
    assert any(h.get("neighbors") or h.get("dagNeighbors") for h in rhits)
    assert any(h.get("entities") for h in rhits)
    _assert_topic_relevance(rhits, ("octonion", "jordan", "lie", "g2"), min_terms=2, label="T4-04 rank")


def test_t4_scenario_bost_connes_kms_modular_operator() -> None:
    """T4-05: Retrieve Bost-Connes & KMS modular operator context from live :8532 corpus."""
    user, pw = _require_live_alexandria_corpus()
    q = "KMS state modular operator split quaternions Cuntz"
    pkt = _run_retrieve_live(q, user, pw, top_k=8)
    hits = pkt.get("hits", [])
    assert len(hits) >= 1
    assert hit_field(hits[0], "documentKey")
    assert hit_field(hits[0], "contentHash")
    assert hit_field(hits[0], "pageStart") is not None
    _assert_valid_dag_neighbors(hits, label="T4-05")
    assert any(h.get("entities") for h in hits), "T4-05 retrieve_context hits missing entities"
    _assert_topic_relevance(hits, ("kms", "cuntz", "modular", "state"), min_terms=2, label="T4-05 retrieve")

    p_ask = run_cli(
        [str(ASK_REPO_SCRIPT), q, "--scope", "alexandria", "--brief", "--no-gravity"],
        env_overrides=_live_alexandria_env(user, pw),
    )
    assert p_ask.returncode == 0, f"stderr={p_ask.stderr}"
    m = re.search(r"^- Alexandria PDFs:\s*`?(\d+)`?\s*$", p_ask.stdout, re.MULTILINE)
    assert m and int(m.group(1)) >= 1, f"Expected non-zero Alexandria PDFs in ask_repo output:\n{p_ask.stdout}"
    sec_match = re.search(
        r"## Alexandria PDFs \(retrieval_context_only\)(.*?)(?:\nAuthority labels:|\Z)",
        p_ask.stdout,
        re.DOTALL,
    )
    assert sec_match, f"Missing Alexandria PDFs section in ask_repo output:\n{p_ask.stdout}"
    alex_section = sec_match.group(1)
    assert "- no hits" not in alex_section.lower()
    assert re.search(r"doc=`?doc_[0-9a-f]+`?", alex_section), f"Missing doc key in:\n{alex_section}"
    assert re.search(r"authority=`?retrieval_context_only`?", alex_section), f"Missing authority label in:\n{alex_section}"
    assert "path:" in alex_section
    assert any(t in alex_section.lower() for t in ("kms", "cuntz", "modular"))

    report = _load_corpus_report()
    bost = _find_unique_doc(report.get("unique_documents", []), "bostconnesscan.pdf")
    assert bost.get("outcome") == "scanned_no_text"
    bost_rows = arango_aql(
        ALEXANDRIA_ENDPOINT,
        ALEXANDRIA_PROD_DB,
        user,
        pw,
        "FOR d IN alexandria_documents FILTER CONTAINS(LOWER(d.path), 'bostconnesscan') RETURN d._key",
        timeout=30.0,
    )
    assert bost_rows == [], f"Scanned PDF bostconnesscan.pdf should not be in alexandria_documents: {bost_rows!r}"


def test_t4_scenario_peirce_drazin_souriau_metriplectic_fisher() -> None:
    """T4-06: Retrieve Peirce/Drazin and Souriau/Metriplectic/Fisher context from live :8532 corpus."""
    user, pw = _require_live_alexandria_corpus()
    q1 = "Drazin inverse orthogonal projections von Neumann algebra"
    q2 = "Souriau Lie group thermodynamics metriplectic contact manifold"
    pkt1 = _run_retrieve_live(q1, user, pw, top_k=6)
    pkt2 = _run_retrieve_live(q2, user, pw, top_k=6)
    assert len(pkt1.get("hits", [])) >= 1
    assert len(pkt2.get("hits", [])) >= 1
    for label, pkt in (("T4-06a", pkt1), ("T4-06b", pkt2)):
        hits = pkt["hits"]
        h0 = hits[0]
        assert hit_field(h0, "chunkKind")
        assert hit_field(h0, "pageStart") is not None
        assert hit_field(h0, "documentKey")
        assert hit_field(h0, "contentHash")
        _assert_valid_dag_neighbors(hits, label=label)
        assert any(h.get("entities") for h in hits), f"[{label}] hits missing entities"

    _assert_topic_relevance(pkt1["hits"], ("von neumann", "projection", "projector", "drazin"), min_terms=2, label="T4-06a")
    _assert_topic_relevance(pkt2["hits"], ("souriau", "thermodynamics", "lie group", "metriplectic", "entropy"), min_terms=2, label="T4-06b")


def test_t4_scenario_krein_space_kasparov_kk_spectral_triple() -> None:
    """T4-07: Retrieve Krein space quantization & Kasparov KK-theory context without touching :8530."""
    user, pw = _require_live_alexandria_corpus()
    q = "Krein space quantization spectral interpretation"
    pkt = _run_retrieve_live(q, user, pw, top_k=6)
    hits = pkt.get("hits", [])
    assert len(hits) >= 1
    assert hit_field(hits[0], "documentKey")
    assert hit_field(hits[0], "contentHash")
    assert hit_field(hits[0], "pageStart") is not None
    _assert_valid_dag_neighbors(hits, label="T4-07")
    assert any(h.get("entities") for h in hits), "T4-07 retrieve_context hits missing entities"
    assert any("krein" in _hit_text_blob(h) for h in hits), "Expected 'krein' in T4-07 retrieval hits"
    _assert_topic_relevance(hits, ("krein", "quantization", "spectral", "green"), min_terms=1, label="T4-07 retrieve")

    p_rag = run_cli(
        [str(GRAPH_RAG_QUERY_SCRIPT), q, "--scope", "alexandria", "--format", "json", "--no-gravity"],
        env_overrides=_live_alexandria_env(user, pw),
    )
    assert p_rag.returncode == 0, f"stderr={p_rag.stderr}"
    rag_data = json.loads(p_rag.stdout)
    alex_hits = _assert_graph_rag_alexandria(
        rag_data, ("krein", "quantization", "spectral", "green"), min_terms=1, label="T4-07 graph_rag"
    )
    assert any("krein" in _hit_text_blob(h) for h in alex_hits), "Expected 'krein' in T4-07 graph_rag hits"
