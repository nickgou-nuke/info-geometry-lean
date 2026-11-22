"""Tier 3: Pairwise combinatorial cross-feature E2E tests (8 tests: T3-01..T3-08)."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any
from urllib.error import URLError

import pytest

from tests.e2e_alexandria_pdf.conftest import (
    ARANGO_INGEST_SCRIPT,
    ASK_REPO_SCRIPT,
    GRAPH_CONTEXT_RANK_SCRIPT,
    GRAPH_RAG_QUERY_SCRIPT,
    INFOGEOMETRY_ENDPOINT,
    PDF_CORPUS_INGEST_SCRIPT,
    RETRIEVE_CONTEXT_SCRIPT,
    arango_aql,
    arango_collection_count,
    arango_http_json,
    assert_retrieval_authority,
    build_corrupt_pdf,
    build_scanned_zero_text_pdf,
    build_structured_math_pdf,
    build_zero_byte_pdf,
    hit_field,
    read_inventory_report,
    read_jsonl,
    report_metric,
    require_script,
    run_cli,
)

pytestmark = pytest.mark.tier3


def _run_pdf_ingest(in_dir: Path, out_dir: Path, extra_args: list[str] | None = None, **kwargs: Any) -> Any:
    script = require_script(PDF_CORPUS_INGEST_SCRIPT)
    cmd = [str(script), "--input-dir", str(in_dir), "--output-dir", str(out_dir)]
    if extra_args:
        cmd.extend(extra_args)
    return run_cli(cmd, **kwargs)


def test_t3_mixed_corpus_dedup_extract_dag_pipeline(tmp_path: Path) -> None:
    """T3-01 (F2 x F3 x F4): Mixed corpus deduplicates, normalizes ligatures, extracts DAG, accounts 100%."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    orig = build_structured_math_pdf(
        in_dir / "clifford.pdf",
        title="Clifford Spinor Ligatures",
        topic="clifford",
        pages=2,
        include_ligatures=True,
    )
    (in_dir / "clifford_copy.pdf").write_bytes(orig.read_bytes())
    (in_dir / "notes.txt").write_text("plain text non-pdf", encoding="utf-8")
    build_zero_byte_pdf(in_dir / "empty.pdf")
    build_scanned_zero_text_pdf(in_dir / "scanned.pdf", pages=1)
    build_corrupt_pdf(in_dir / "corrupt.pdf")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 6
    assert report_metric(report, "duplicateSkipped", "duplicate_skipped", "duplicate_skipped_count", "duplicatesSkipped") == 1
    assert report_metric(report, "nonPdfSkipped", "non_pdf_skipped", "nonPdfsSkipped") == 1

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1
    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    combined = "\n".join(c["text"] for c in chunks)
    assert "artificial" in combined.lower() and "\ufb01" not in combined
    dag_edges = read_jsonl(out_dir / "alexandria_dag_edges.jsonl")
    assert len(dag_edges) >= 1


def test_t3_ingest_replace_documents_updates_dag_and_bm25(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T3-02 (F1 x F4 x F5): --replace-documents purges stale Theorem Alpha/DAG and indexes Theorem Beta."""
    in_dir = tmp_path / "in"
    out_v1 = tmp_path / "v1"
    build_structured_math_pdf(in_dir / "paper.pdf", title="Theorem Alpha Paper", topic="clifford", pages=2)
    assert _run_pdf_ingest(in_dir, out_v1).returncode == 0

    ingest_base = [
        str(ARANGO_INGEST_SCRIPT),
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
        "--username", isolated_alexandria_db["username"],
        "--password", isolated_alexandria_db["password"],
    ]
    assert run_cli([*ingest_base, "--input-dir", str(out_v1)]).returncode == 0

    # Mutate JSONL for v2 with same documentKey -> Theorem Beta
    doc_v1 = read_jsonl(out_v1 / "alexandria_documents.jsonl")[0]
    doc_key = doc_v1["_key"]
    sec_v1 = read_jsonl(out_v1 / "alexandria_sections.jsonl")[0]
    sec_key = sec_v1["_key"]

    out_v2 = tmp_path / "v2"
    out_v2.mkdir()
    doc_v2 = dict(doc_v1)
    doc_v2["contentHash"] = "c" * 64
    c_thm = {
        "_key": f"{doc_key}_beta_thm",
        "documentKey": doc_key,
        "sectionKey": sec_key,
        "ordinal": 1,
        "chunkKind": "theorem",
        "title": "Theorem Beta",
        "text": "Theorem Beta: UniquezxBeta spectral decomposition holds.",
        "tokens": ["theorem", "beta", "uniquezxbeta", "spectral", "decomposition", "holds"],
        "sourceAuthority": "retrieval_context_only",
        "provenance": {"path": doc_v2["path"], "contentHash": doc_v2["contentHash"], "sourceFormat": "pdf", "pageStart": 1, "pageEnd": 1},
    }
    c_prf = {
        "_key": f"{doc_key}_beta_prf",
        "documentKey": doc_key,
        "sectionKey": sec_key,
        "ordinal": 2,
        "chunkKind": "proof",
        "title": "Proof Beta",
        "text": "Proof of Theorem Beta via modular operator.",
        "tokens": ["proof", "theorem", "beta", "via", "modular", "operator"],
        "sourceAuthority": "retrieval_context_only",
        "provenance": {"path": doc_v2["path"], "contentHash": doc_v2["contentHash"], "sourceFormat": "pdf", "pageStart": 1, "pageEnd": 1},
    }
    dag_v2 = {
        "_key": f"{doc_key}_dag_beta",
        "_from": f"alexandria_chunks/{c_prf['_key']}",
        "_to": f"alexandria_chunks/{c_thm['_key']}",
        "documentKey": doc_key,
        "edgeType": "proof_proves_theorem",
        "evidence": "Proof of Theorem Beta",
        "confidence": 0.95,
    }
    (out_v2 / "alexandria_documents.jsonl").write_text(json.dumps(doc_v2) + "\n", encoding="utf-8")
    (out_v2 / "alexandria_sections.jsonl").write_text(json.dumps(sec_v1) + "\n", encoding="utf-8")
    (out_v2 / "alexandria_chunks.jsonl").write_text(
        json.dumps(c_thm) + "\n" + json.dumps(c_prf) + "\n", encoding="utf-8"
    )
    (out_v2 / "alexandria_dag_edges.jsonl").write_text(json.dumps(dag_v2) + "\n", encoding="utf-8")
    (out_v2 / "alexandria_document_section_edges.jsonl").write_text(
        json.dumps({"_key": f"{doc_key}_ds", "_from": f"alexandria_documents/{doc_key}", "_to": f"alexandria_sections/{sec_key}"}) + "\n",
        encoding="utf-8",
    )
    (out_v2 / "alexandria_section_chunk_edges.jsonl").write_text(
        "".join(
            json.dumps({"_key": f"{doc_key}_sc_{i}", "_from": f"alexandria_sections/{sec_key}", "_to": f"alexandria_chunks/{c['_key']}"}) + "\n"
            for i, c in enumerate((c_thm, c_prf))
        ),
        encoding="utf-8",
    )
    for empty_col in ("alexandria_entities", "alexandria_chunk_adjacent_edges", "alexandria_chunk_entity_edges", "alexandria_entity_relation_edges"):
        (out_v2 / f"{empty_col}.jsonl").write_text("", encoding="utf-8")

    assert run_cli([*ingest_base, "--input-dir", str(out_v2), "--replace-documents"]).returncode == 0

    hits_beta = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        'FOR c IN alexandria_chunks_search SEARCH ANALYZER(c.text IN TOKENS(@q, "text_en"), "text_en") OPTIONS {waitForSync: true} RETURN c._key',
        {"q": "uniquezxbeta"},
    )
    hits_alpha = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        'FOR c IN alexandria_chunks_search SEARCH ANALYZER(c.text IN TOKENS(@q, "text_en"), "text_en") OPTIONS {waitForSync: true} RETURN c._key',
        {"q": "Hestenes"},
    )
    assert c_thm["_key"] in hits_beta
    assert hits_alpha == []
    dangling = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR e IN alexandria_dag_edges FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null RETURN e._key",
    )
    assert dangling == []
    dag_keys = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR e IN alexandria_dag_edges SORT e._key RETURN e._key",
    )
    assert dag_keys == [dag_v2["_key"]], f"Stale DAG edges survived --replace-documents: {dag_keys}"
    chunk_keys = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR c IN alexandria_chunks SORT c._key RETURN c._key",
    )
    assert chunk_keys == sorted([c_thm["_key"], c_prf["_key"]])
    sec_keys = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR s IN alexandria_sections SORT s._key RETURN s._key",
    )
    assert sec_keys == [sec_key]


def test_t3_idempotent_reingestion_skip_unchanged_and_replace_combo(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T3-03 (F2 x F5 x F6): --skip-unchanged skips unchanged docs and --replace-documents updates idempotently."""
    in_dir = tmp_path / "in"
    out_1 = tmp_path / "out1"
    out_2 = tmp_path / "out2"
    out_3 = tmp_path / "out3"
    p1 = build_structured_math_pdf(in_dir / "p1.pdf", topic="clifford")
    build_structured_math_pdf(in_dir / "p2.pdf", topic="octonions")

    env = {
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    base_arango_args = [
        "--ingest-arango",
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
    ]
    proc_1 = _run_pdf_ingest(in_dir, out_1, extra_args=[*base_arango_args, "--skip-unchanged"], env_overrides=env)
    assert proc_1.returncode == 0, f"stderr={proc_1.stderr}"
    stdout_1 = json.loads(proc_1.stdout)
    report_1 = read_inventory_report(out_1)
    assert stdout_1["arango_ingest"] == report_1["arango_ingest"]
    arango_1 = report_1["arango_ingest"]
    assert arango_1["documents"] == 2
    assert arango_1["skippedUnchanged"] == 0
    assert arango_1["imported"].get("alexandria_documents") == 2

    p3 = build_structured_math_pdf(in_dir / "p3.pdf", topic="peirce")
    p1_dup = in_dir / "p1_dup.pdf"
    p1_dup.write_bytes(p1.read_bytes())
    proc_2 = _run_pdf_ingest(in_dir, out_2, extra_args=[*base_arango_args, "--skip-unchanged"], env_overrides=env)
    assert proc_2.returncode == 0, f"stderr={proc_2.stderr}"
    stdout_2 = json.loads(proc_2.stdout)
    report_2 = read_inventory_report(out_2)
    assert report_2["duplicate_skipped_count"] == 1
    assert stdout_2["arango_ingest"] == report_2["arango_ingest"]

    docs_out2 = read_jsonl(out_2 / "alexandria_documents.jsonl")
    p1_doc_key = next(d["_key"] for d in docs_out2 if d["path"] == p1.as_posix())
    p3_doc_key = next(d["_key"] for d in docs_out2 if d["path"] == p3.as_posix())
    p3_chunks = [c for c in read_jsonl(out_2 / "alexandria_chunks.jsonl") if c.get("documentKey") == p3_doc_key]
    p3_dag_edges = [e for e in read_jsonl(out_2 / "alexandria_dag_edges.jsonl") if e.get("documentKey") == p3_doc_key]

    arango_2 = report_2["arango_ingest"]
    assert arango_2["documents"] == 3
    assert arango_2["skippedUnchanged"] == 2
    assert arango_2["imported"].get("alexandria_documents") == 1
    assert arango_2["imported"].get("alexandria_chunks") == len(p3_chunks)
    assert arango_2["imported"].get("alexandria_dag_edges", 0) == len(p3_dag_edges)

    p1_dups_after_skip = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR d IN alexandria_documents FILTER d._key == @k RETURN d.duplicatePaths",
        {"k": p1_doc_key},
    )
    assert p1_dups_after_skip == [[]], f"Expected p1 skipped without overwrite, got {p1_dups_after_skip}"

    chunks_after_skip = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_chunks",
    )
    dag_after_skip = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_dag_edges",
    )

    proc_3 = _run_pdf_ingest(in_dir, out_3, extra_args=[*base_arango_args, "--replace-documents"], env_overrides=env)
    assert proc_3.returncode == 0, f"stderr={proc_3.stderr}"
    stdout_3 = json.loads(proc_3.stdout)
    report_3 = read_inventory_report(out_3)
    assert stdout_3["arango_ingest"] == report_3["arango_ingest"]
    arango_3 = report_3["arango_ingest"]
    assert arango_3["documents"] == 3
    assert arango_3["skippedUnchanged"] == 0
    assert arango_3["imported"].get("alexandria_documents") == 3

    p1_dups_after_replace = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR d IN alexandria_documents FILTER d._key == @k RETURN d.duplicatePaths",
        {"k": p1_doc_key},
    )
    assert p1_dups_after_replace == [[p1_dup.as_posix()]]

    doc_count = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_documents",
    )
    assert doc_count == 3
    assert arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_chunks",
    ) == chunks_after_skip
    assert arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_dag_edges",
    ) == dag_after_skip
    dangling = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR e IN alexandria_dag_edges FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null RETURN e._key",
    )
    assert dangling == []


def test_t3_bm25_search_plus_dag_neighbor_expansion_end_to_end(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T3-04 (F4 x F5 x F7): BM25 match on Definition/Theorem retrieves linked DAG neighbors."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "peirce_dag.pdf", title="Peirce Projections", topic="peirce", pages=2)
    env = {
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    assert _run_pdf_ingest(
        in_dir,
        out_dir,
        extra_args=[
            "--ingest-arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
        ],
        env_overrides=env,
    ).returncode == 0

    proc = run_cli(
        [
            str(RETRIEVE_CONTEXT_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "Peirce Projector",
            "--top-k", "5",
        ],
        env_overrides=env,
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    packet = json.loads(proc.stdout)
    assert_retrieval_authority(packet)
    assert packet.get("target", {}).get("database") == isolated_alexandria_db["database"]
    hits = packet.get("hits", [])
    assert len(hits) >= 1
    dag_neighbors = [d for h in hits for d in (h.get("dagNeighbors") or []) if isinstance(d, dict)]
    assert dag_neighbors, f"Expected non-empty dagNeighbors in retrieval packet: hits={hits!r}"
    valid_dag_edge_types = {
        "section_precedes_section",
        "proof_proves_theorem",
        "chunk_uses_definition",
        "chunk_references_result",
        "chunk_cites_entry",
        "document_cites_document",
    }
    assert any(
        d.get("edgeType") in valid_dag_edge_types
        and d.get("direction") in {"inbound", "outbound"}
        and bool(d.get("_id"))
        and bool(d.get("_key"))
        for d in dag_neighbors
    ), f"Expected typed DAG neighbor with edgeType/direction/_id/_key, got {dag_neighbors!r}"


def test_t3_jsonl_vs_arango_retrieval_and_graph_rank_parity(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T3-05 (F4 x F5 x F7): JSONL and --arango modes agree on top relevant documents and provenance."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "clifford.pdf", title="Clifford Spinors", topic="clifford")
    build_structured_math_pdf(in_dir / "octonions.pdf", title="Split Octonions", topic="octonions")
    build_structured_math_pdf(in_dir / "peirce.pdf", title="Peirce Drazin", topic="peirce")

    env = {
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    assert _run_pdf_ingest(
        in_dir,
        out_dir,
        extra_args=[
            "--ingest-arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
        ],
        env_overrides=env,
    ).returncode == 0

    q = "Albert Vector split octonions G2"
    p_jsonl = run_cli([str(RETRIEVE_CONTEXT_SCRIPT), "--input-dir", str(out_dir), "--query", q, "--top-k", "5"])
    p_arango = run_cli(
        [
            str(RETRIEVE_CONTEXT_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", q,
            "--top-k", "5",
        ],
        env_overrides=env,
    )
    assert p_jsonl.returncode == 0 and p_arango.returncode == 0
    pkt_j = json.loads(p_jsonl.stdout)
    pkt_a = json.loads(p_arango.stdout)
    assert_retrieval_authority(pkt_j)
    assert_retrieval_authority(pkt_a)

    docs_j = {hit_field(h, "documentKey") for h in pkt_j.get("hits", []) if hit_field(h, "documentKey")}
    docs_a = {hit_field(h, "documentKey") for h in pkt_a.get("hits", []) if hit_field(h, "documentKey")}
    assert docs_j & docs_a, f"No overlapping documentKey between JSONL ({docs_j}) and Arango ({docs_a})"

    r_jsonl = run_cli([str(GRAPH_CONTEXT_RANK_SCRIPT), "--input-dir", str(out_dir), "--query", q, "--top-k", "5"])
    r_arango = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", q,
            "--top-k", "5",
        ],
        env_overrides=env,
    )
    assert r_jsonl.returncode == 0, f"stderr={r_jsonl.stderr}"
    assert r_arango.returncode == 0, f"stderr={r_arango.stderr}"
    rank_j = json.loads(r_jsonl.stdout)
    rank_a = json.loads(r_arango.stdout)
    assert_retrieval_authority(rank_j)
    assert_retrieval_authority(rank_a)
    assert rank_a.get("target", {}).get("database") == isolated_alexandria_db["database"]

    for label, pkt in (("jsonl", rank_j), ("arango", rank_a)):
        assert pkt.get("authority") == "retrieval_context_only", f"{label} missing top-level authority: {pkt!r}"
        assert pkt.get("sourceAuthority") == "retrieval_context_only", f"{label} missing sourceAuthority: {pkt!r}"
        disc = str(pkt.get("disclaimer", "")).lower()
        assert "retrieval" in disc and "not" in disc and "proof" in disc, f"{label} missing disclaimer: {pkt!r}"
        rhits = pkt.get("hits", [])
        assert rhits, f"{label} graph_context_rank returned no hits"
        assert all(
            isinstance(h, dict)
            and h.get("authority") == "retrieval_context_only"
            and h.get("sourceAuthority") == "retrieval_context_only"
            for h in rhits
        ), f"{label} hit missing authority/sourceAuthority: {rhits!r}"

    rank_docs_j = {hit_field(h, "documentKey") for h in rank_j["hits"] if hit_field(h, "documentKey")}
    rank_docs_a = {hit_field(h, "documentKey") for h in rank_a["hits"] if hit_field(h, "documentKey")}
    assert rank_docs_j & rank_docs_a, (
        f"No overlapping documentKey between graph_context_rank JSONL ({rank_docs_j}) and Arango ({rank_docs_a})"
    )
    assert docs_a & rank_docs_a, (
        f"retrieve_context ({docs_a}) and graph_context_rank ({rank_docs_a}) disagree on top documentKey"
    )
    rank_hashes_j = {hit_field(h, "contentHash") for h in rank_j["hits"] if hit_field(h, "contentHash")}
    rank_hashes_a = {hit_field(h, "contentHash") for h in rank_a["hits"] if hit_field(h, "contentHash")}
    assert rank_hashes_j & rank_hashes_a, (
        f"No overlapping contentHash provenance between JSONL ({rank_hashes_j}) and Arango ({rank_hashes_a})"
    )


def test_t3_repo_graph_rag_and_ask_repo_route_to_8532_without_8530(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T3-06 (F1 x F7): graph_rag_query.py and ask_repo.py --scope alexandria query :8532 even with poisoned :8530 env."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    pdf_path = build_structured_math_pdf(in_dir / "clifford.pdf", title="Clifford Spinors", topic="clifford")
    assert _run_pdf_ingest(
        in_dir,
        out_dir,
        extra_args=[
            "--ingest-arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
        ],
        env_overrides={
            "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
            "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
        },
    ).returncode == 0
    expected_doc_key = read_jsonl(out_dir / "alexandria_documents.jsonl")[0]["_key"]

    poisoned_env = {
        "ARANGO_ENDPOINT": INFOGEOMETRY_ENDPOINT,
        "ARANGO_DATABASE": "infogeometry",
        "ALEXANDRIA_ARANGO_ENDPOINT": isolated_alexandria_db["endpoint"],
        "ALEXANDRIA_ARANGO_DB": isolated_alexandria_db["database"],
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    p_rag = run_cli(
        [str(GRAPH_RAG_QUERY_SCRIPT), "Hestenes spinor", "--scope", "alexandria", "--format", "json", "--no-gravity"],
        env_overrides=poisoned_env,
    )
    assert p_rag.returncode == 0, f"stderr={p_rag.stderr}"
    rag_data = json.loads(p_rag.stdout)
    assert rag_data.get("scope") == "alexandria"
    assert rag_data.get("gravity") is None
    assert rag_data.get("authority") == "retrieval_context_only"
    assert "not verified lean proof" in str(rag_data.get("disclaimer", "")).lower()
    assert rag_data.get("authorities", {}).get("alexandria") == "retrieval_context_only"

    alex_hits = rag_data.get("alexandria", [])
    assert len(alex_hits) >= 1
    assert all(
        isinstance(h, dict)
        and h.get("source") == "alexandria"
        and isinstance(h.get("metadata"), dict)
        and h["metadata"].get("authority") == "retrieval_context_only"
        and h["metadata"].get("sourceAuthority") == "retrieval_context_only"
        for h in alex_hits
    ), f"Expected retrieval_context_only metadata on all alexandria hits: {alex_hits!r}"
    assert any(
        h.get("path") == str(pdf_path)
        and h.get("metadata", {}).get("documentKey") == expected_doc_key
        for h in alex_hits
    ), (
        f"Expected hit from isolated DB ({pdf_path}, {expected_doc_key}); "
        f"got {[(h.get('path'), (h.get('metadata') or {}).get('documentKey')) for h in alex_hits]!r}"
    )

    p_ask = run_cli(
        [str(ASK_REPO_SCRIPT), "Hestenes spinor", "--scope", "alexandria", "--answer", "--no-gravity"],
        env_overrides=poisoned_env,
    )
    assert p_ask.returncode == 0, f"stderr={p_ask.stderr}"
    assert "No ranked hits were found" not in p_ask.stdout
    assert "[alexandria]" in p_ask.stdout
    assert "The strongest pointers come from the Alexandria PDF corpus (retrieval_context_only)" in p_ask.stdout
    assert "hestenes" in p_ask.stdout.lower() or "clifford" in p_ask.stdout.lower()

    p_ask_brief = run_cli(
        [str(ASK_REPO_SCRIPT), "Hestenes spinor", "--scope", "alexandria", "--brief", "--no-gravity"],
        env_overrides=poisoned_env,
    )
    assert p_ask_brief.returncode == 0, f"stderr={p_ask_brief.stderr}"
    assert str(pdf_path) in p_ask_brief.stdout
    assert expected_doc_key in p_ask_brief.stdout


def test_t3_ligature_normalization_enables_bm25_citation_retrieval(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T3-07 (F3 x F4 x F5 x F7): Ligature normalization flows into BM25 search for ASCII queries."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(
        in_dir / "lig.pdf",
        title="Souriau Gauge Fields",
        topic="peirce",
        include_ligatures=True,
    )
    env = {
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    assert _run_pdf_ingest(
        in_dir,
        out_dir,
        extra_args=[
            "--ingest-arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
        ],
        env_overrides=env,
    ).returncode == 0

    proc = run_cli(
        [
            str(RETRIEVE_CONTEXT_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "artificial gauge fields",
            "--top-k", "5",
        ],
        env_overrides=env,
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    packet = json.loads(proc.stdout)
    assert_retrieval_authority(packet)
    hits = packet.get("hits", [])
    assert len(hits) >= 1
    assert any("artificial" in str(hit_field(h, "text") or "").lower() for h in hits)


def test_t3_poisoned_generic_arango_env_cannot_corrupt_pipeline_lane(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T3-08 (F1 x F2 x F5 x F6): Poisoned ARANGO_*/HIVE_ARANGO_* env cannot divert pdf_corpus_ingest off :8532."""
    import igf.config.env_aliases as env_aliases

    assert callable(getattr(env_aliases, "guard_alexandria_target", None)), (
        "guard_alexandria_target missing; refusing poisoned-env test against live :8530"
    )
    pdf_script = require_script(PDF_CORPUS_INGEST_SCRIPT)
    script_src = pdf_script.read_text(encoding="utf-8")
    assert "alexandria_arango_endpoint" in script_src and "guard_alexandria_target" in script_src, (
        "pdf_corpus_ingest.py must resolve via alexandria_arango_endpoint() + guard_alexandria_target()"
    )

    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "lane.pdf", topic="clifford")

    proc = _run_pdf_ingest(
        in_dir,
        out_dir,
        extra_args=["--ingest-arango"],
        clear_arango_env=True,
        env_overrides={
            "ARANGO_ENDPOINT": INFOGEOMETRY_ENDPOINT,
            "ARANGO_DATABASE": "infogeometry",
            "HIVE_ARANGO_ENDPOINT": "http://127.0.0.1:8540",
            "HIVE_ARANGO_DATABASE": "hive_live",
            "ALEXANDRIA_ARANGO_DB": isolated_alexandria_db["database"],
            "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
            "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
        },
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    assert arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_documents",
    ) == 1

    # Behavioral negative probes: explicit CLI flags and poisoned ALEXANDRIA_* env must be rejected
    # by guard_alexandria_target BEFORE any DB connection (dummy creds prevent touching :8530/:8540).
    guard_cases = [
        (
            [
                "--ingest-arango",
                "--endpoint", INFOGEOMETRY_ENDPOINT,
                "--database", "infogeometry",
                "--username", "e2e_guard_probe",
                "--password", "e2e_guard_probe",
            ],
            {"ALEXANDRIA_ARANGO_ENDPOINT": None, "ALEXANDRIA_ARANGO_DB": None},
            ("infogeometry", "8530"),
        ),
        (
            [
                "--ingest-arango",
                "--endpoint", "http://127.0.0.1:8540",
                "--database", "hive_live",
                "--username", "e2e_guard_probe",
                "--password", "e2e_guard_probe",
            ],
            {"ALEXANDRIA_ARANGO_ENDPOINT": None, "ALEXANDRIA_ARANGO_DB": None},
            ("hive_live", "8540"),
        ),
        (
            ["--ingest-arango"],
            {
                "ALEXANDRIA_ARANGO_ENDPOINT": INFOGEOMETRY_ENDPOINT,
                "ALEXANDRIA_ARANGO_DB": "infogeometry",
                "ALEXANDRIA_ARANGO_USERNAME": "e2e_guard_probe",
                "ALEXANDRIA_ARANGO_PASSWORD": "e2e_guard_probe",
            },
            ("infogeometry", "8530"),
        ),
    ]
    for idx, (extra_args, env_ovr, expected_tokens) in enumerate(guard_cases):
        p_rej = _run_pdf_ingest(
            in_dir,
            tmp_path / f"out_guard_{idx}",
            extra_args=extra_args,
            clear_arango_env=True,
            env_overrides=env_ovr,
        )
        combined = (p_rej.stderr + p_rej.stdout).lower()
        assert p_rej.returncode != 0, (
            f"Expected guard_alexandria_target rejection for case {idx}: stdout={p_rej.stdout!r}"
        )
        assert "refusing alexandria" in combined, (
            f"Expected guard_alexandria_target ValueError ('Refusing Alexandria...') for case {idx}, got: {combined!r}"
        )
        assert any(tok in combined for tok in expected_tokens), (
            f"Expected one of {expected_tokens!r} in guard rejection output: {combined!r}"
        )

    # Read-only verify :8530 infogeometry has zero alexandria_documents collection if reachable
    col_names_8530: set[str] | None = None
    try:
        st, cols = arango_http_json(
            "GET",
            f"{INFOGEOMETRY_ENDPOINT}/_db/infogeometry/_api/collection?excludeSystem=true",
            isolated_alexandria_db["username"],
            isolated_alexandria_db["password"],
            timeout=2.0,
        )
        if st == 200:
            col_names_8530 = {c.get("name") for c in cols.get("result", []) if isinstance(c, dict)}
    except (URLError, OSError):
        col_names_8530 = None
    if col_names_8530 is not None:
        assert "alexandria_documents" not in col_names_8530
