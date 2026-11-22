"""Tier 1: Isolated feature happy-path E2E tests (35 tests across F1-F7)."""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any
from urllib.error import URLError

import pytest

from tests.e2e_alexandria_pdf.conftest import (
    ALEXANDRIA_ENDPOINT,
    ARANGO_INGEST_SCRIPT,
    ASK_REPO_SCRIPT,
    GRAPH_CONTEXT_RANK_SCRIPT,
    GRAPH_RAG_QUERY_SCRIPT,
    INFOGEOMETRY_ENDPOINT,
    PDF_CORPUS_INGEST_SCRIPT,
    REPO_ROOT,
    RETRIEVE_CONTEXT_SCRIPT,
    arango_aql,
    arango_collection_count,
    arango_http_json,
    arango_list_collections,
    arango_list_databases,
    arango_list_views,
    assert_retrieval_authority,
    build_permission_encrypted_pdf,
    build_png_file,
    build_structured_math_pdf,
    hit_field,
    read_inventory_report,
    read_jsonl,
    report_entries,
    report_metric,
    require_alexandria_8532,
    require_script,
    run_cli,
    sha256_file,
    snapshot_tree,
)

pytestmark = pytest.mark.tier1


def _run_pdf_ingest(in_dir: Path, out_dir: Path, extra_args: list[str] | None = None, **kwargs: Any) -> Any:
    script = require_script(PDF_CORPUS_INGEST_SCRIPT)
    cmd = [str(script), "--input-dir", str(in_dir), "--output-dir", str(out_dir)]
    if extra_args:
        cmd.extend(extra_args)
    return run_cli(cmd, **kwargs)


# ===========================================================================
# F1 — Strict ArangoDB Lane Isolation & :8532 Service (5 tests)
# ===========================================================================


def test_f1_alexandria_env_defaults_resolve_to_8532() -> None:
    """T1-F1-01: Alexandria env defaults resolve to :8532 and 'alexandria' with non-empty creds."""
    code = (
        "import json; from pathlib import Path; "
        "import igf.config.env_aliases as ea; "
        "(getattr(ea, 'load_alexandria_arango_env', None) or ea.load_repo_arango_env)(Path.cwd()); "
        "print(json.dumps({"
        "'endpoint': ea.alexandria_arango_endpoint(), "
        "'database': ea.alexandria_arango_database(), "
        "'username': ea.alexandria_arango_username(), "
        "'password': ea.alexandria_arango_password()"
        "}))"
    )
    proc = run_cli(["-c", code], clear_arango_env=True)
    assert proc.returncode == 0, f"Subprocess failed: {proc.stderr}"
    data = json.loads(proc.stdout)
    assert data["endpoint"] == "http://127.0.0.1:8532"
    assert data["database"] == "alexandria"
    assert data["username"], "alexandria_arango_username() must resolve non-empty default from configs/alexandria/.env"
    assert data["password"], "alexandria_arango_password() must resolve non-empty default from configs/alexandria/.env"


def test_f1_guard_accepts_valid_alexandria_target() -> None:
    """T1-F1-02: guard_alexandria_target accepts :8532 + alexandria and test DB names."""
    import igf.config.env_aliases as env_aliases

    guard = getattr(env_aliases, "guard_alexandria_target", None)
    assert callable(guard), "guard_alexandria_target(endpoint, database) is missing from igf.config.env_aliases"
    guard("http://127.0.0.1:8532", "alexandria")
    guard("http://127.0.0.1:8532", "alexandria_e2e_test")


def test_f1_generic_arango_env_does_not_hijack_alexandria() -> None:
    """T1-F1-03: Generic ARANGO_ENDPOINT=:8530 / ARANGO_DATABASE=infogeometry never hijack Alexandria."""
    code = (
        "import json; from pathlib import Path; "
        "import igf.config.env_aliases as ea; "
        "ea.load_repo_arango_env(Path.cwd()); "
        "print(json.dumps({"
        "'endpoint': ea.alexandria_arango_endpoint(), "
        "'database': ea.alexandria_arango_database()"
        "}))"
    )
    proc = run_cli(
        ["-c", code],
        clear_arango_env=True,
        env_overrides={
            "ARANGO_ENDPOINT": "http://127.0.0.1:8530",
            "ARANGO_DATABASE": "infogeometry",
        },
    )
    assert proc.returncode == 0, f"Subprocess failed: {proc.stderr}"
    data = json.loads(proc.stdout)
    assert data["endpoint"] == "http://127.0.0.1:8532"
    assert data["database"] == "alexandria"


def test_f1_compose_and_env_config_declare_8532_and_noncolliding_container() -> None:
    """T1-F1-04: Dedicated Alexandria PDF compose & env files map 8532->8529 with non-colliding container."""
    compose_pdf = REPO_ROOT / "configs" / "alexandria" / "docker-compose.pdf.yml"
    compose_default = REPO_ROOT / "configs" / "alexandria" / "docker-compose.yml"
    compose_path = compose_pdf if compose_pdf.exists() else compose_default
    assert compose_path.exists(), "Missing Alexandria docker-compose config under configs/alexandria/"

    compose_text = compose_path.read_text(encoding="utf-8")
    assert "8532" in compose_text and "8529" in compose_text, (
        f"{compose_path.name} must map host 8532 to container 8529"
    )
    match = re.search(r"container_name:\s*([^\s#]+)", compose_text)
    assert match, f"{compose_path.name} must declare an explicit non-colliding container_name"
    container_name = match.group(1)
    assert container_name not in {"arango_alexandria", "arango_hive"}, (
        f"Container name {container_name!r} collides with live :8530/:8540 containers"
    )

    env_example = REPO_ROOT / "configs" / "alexandria" / ".env.example"
    assert env_example.exists(), "configs/alexandria/.env.example missing"
    env_text = env_example.read_text(encoding="utf-8")
    assert "ALEXANDRIA_ARANGO_PORT=8532" in env_text
    assert "ALEXANDRIA_ARANGO_DB=alexandria" in env_text


def test_f1_live_8532_service_reachable_and_separate_from_8530() -> None:
    """T1-F1-05: Live :8532 ArangoDB responds HTTP 200 and stays isolated from :8530 DBs."""
    user, pw = require_alexandria_8532()
    status, ver = arango_http_json("GET", f"{ALEXANDRIA_ENDPOINT}/_api/version", user, pw, timeout=3.0)
    assert status == 200 and ver.get("server") == "arango", f"Unexpected :8532 version response: {ver}"

    dbs_8532 = set(arango_list_databases(ALEXANDRIA_ENDPOINT, user, pw))
    assert "infogeometry" not in dbs_8532
    assert "darwin_commits" not in dbs_8532
    assert "hive_live" not in dbs_8532

    # Read-only check against :8530 infogeometry if reachable: verify zero PDF-lane collections
    col_names_8530: set[str] | None = None
    try:
        st_8530, cols_8530 = arango_http_json(
            "GET",
            f"{INFOGEOMETRY_ENDPOINT}/_db/infogeometry/_api/collection?excludeSystem=true",
            user,
            pw,
            timeout=2.0,
        )
        if st_8530 == 200:
            col_names_8530 = {
                c["name"] for c in cols_8530.get("result", []) if isinstance(c, dict) and c.get("name")
            }
    except (URLError, OSError):
        col_names_8530 = None
    if col_names_8530 is not None:
        assert "alexandria_documents" not in col_names_8530
        assert "alexandria_dag_edges" not in col_names_8530


# ===========================================================================
# F2 — Corpus Inventory & SHA-256 Deduplication (5 tests)
# ===========================================================================


def test_f2_inventory_single_valid_pdf_reports_complete_accounting(tmp_path: Path) -> None:
    """T1-F2-01: Single valid PDF produces 100%-accounted inventory report and JSONL."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    pdf_path = build_structured_math_pdf(in_dir / "sample.pdf", topic="clifford", pages=2)
    expected_hash = sha256_file(pdf_path)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    assert (out_dir / "corpus_inventory_report.json").exists()
    assert (out_dir / "corpus_inventory_report.md").exists()

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 1
    assert report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs") == 1
    assert report_metric(report, "duplicateSkipped", "duplicate_skipped", "duplicate_skipped_count", "duplicatesSkipped") == 0
    assert report_metric(report, "nonPdfSkipped", "non_pdf_skipped", "nonPdfsSkipped") == 0

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1
    assert docs[0]["contentHash"] == expected_hash


def test_f2_sha256_deduplication_across_renamed_and_nested_copies(tmp_path: Path) -> None:
    """T1-F2-02: Identical bytes in renamed and nested copies collapse to 1 unique document."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    orig = build_structured_math_pdf(in_dir / "paper.pdf", topic="clifford")
    raw = orig.read_bytes()
    (in_dir / "paper (1).pdf").write_bytes(raw)
    (in_dir / "subdir").mkdir()
    (in_dir / "subdir" / "copy_of_paper.pdf").write_bytes(raw)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 3
    assert report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs") == 1
    assert report_metric(report, "duplicateSkipped", "duplicate_skipped", "duplicate_skipped_count", "duplicatesSkipped") == 2

    dup_groups = report.get("duplicateGroups") or report.get("duplicate_groups") or []
    assert len(dup_groups) == 1
    assert dup_groups[0].get("canonicalPath")
    assert len(dup_groups[0].get("duplicatePaths", [])) == 2

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1
    assert len(docs[0].get("duplicatePaths", [])) >= 2


def test_f2_distinct_content_pdfs_yield_distinct_document_keys(tmp_path: Path) -> None:
    """T1-F2-03: Distinct valid PDFs emit distinct _key and contentHash values."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "clifford.pdf", title="Clifford Paper", topic="clifford")
    build_structured_math_pdf(in_dir / "octonions.pdf", title="Octonions Paper", topic="octonions")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs") == 2
    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 2
    keys = {d["_key"] for d in docs}
    hashes = {d["contentHash"] for d in docs}
    assert len(keys) == 2 and len(hashes) == 2
    for d in docs:
        assert d["_key"] == f"doc_{d['contentHash'][:20]}"


def test_f2_non_pdf_artifacts_cleanly_classified_and_skipped(tmp_path: Path) -> None:
    """T1-F2-04: Non-PDF extensions (.txt, .png, .svg, .thy, .lean) are skipped and accounted."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "valid.pdf", topic="peirce")
    (in_dir / "notes.txt").write_text("plain notes", encoding="utf-8")
    build_png_file(in_dir / "diagram.png")
    (in_dir / "fig.svg").write_text("<svg/>", encoding="utf-8")
    (in_dir / "theory.thy").write_text("theory Foo imports Main begin end", encoding="utf-8")
    (in_dir / "lemma.lean").write_text("theorem t : True := trivial", encoding="utf-8")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 6
    assert report_metric(report, "nonPdfSkipped", "non_pdf_skipped", "nonPdfsSkipped") == 5
    assert report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs") == 1
    assert len(read_jsonl(out_dir / "alexandria_documents.jsonl")) == 1


def test_f2_source_directory_strictly_unmodified(tmp_path: Path) -> None:
    """T1-F2-05: Input directory timestamps, bytes, and structure remain identical after run."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    p = build_structured_math_pdf(in_dir / "a.pdf", topic="clifford")
    (in_dir / "a_dup.pdf").write_bytes(p.read_bytes())
    (in_dir / "readme.txt").write_text("untouched", encoding="utf-8")

    before = snapshot_tree(in_dir)
    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    after = snapshot_tree(in_dir)
    assert before == after, "Source directory was modified during ingestion!"


# ===========================================================================
# F3 — Resilient PDF Extraction & Normalization (5 tests)
# ===========================================================================


def test_f3_extracts_multipage_text_and_page_count(tmp_path: Path) -> None:
    """T1-F3-01: Multi-page PDF records exact pageCount, parser, and 1..3 page bounds."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "multi.pdf", topic="clifford", pages=3)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1
    assert docs[0]["pageCount"] == 3
    assert docs[0].get("parser")

    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    assert chunks
    for ch in chunks:
        prov = ch.get("provenance", {})
        assert 1 <= prov["pageStart"] <= prov["pageEnd"] <= 3


def test_f3_normalizes_ligatures_and_form_feeds(tmp_path: Path) -> None:
    """T1-F3-02: Unicode ligatures (fi/fl/ff) and form-feed chars are normalized in chunks."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "ligatures.pdf", topic="peirce", include_ligatures=True)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    combined = "\n".join(c["text"] for c in chunks)
    assert "artificial" in combined.lower()
    assert "fields" in combined.lower()
    assert "flow" in combined.lower()
    assert "\ufb01" not in combined and "\ufb02" not in combined and "\ufb00" not in combined
    assert "\x0c" not in combined


def test_f3_strips_repeated_running_headers_and_footers(tmp_path: Path) -> None:
    """T1-F3-03: Repeated running headers across pages are deduplicated/stripped from body chunks."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    header = "Journal of Mathematical Physics Vol 12"
    build_structured_math_pdf(
        in_dir / "running.pdf",
        topic="clifford",
        pages=4,
        include_running_header=True,
        running_header=header,
    )

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    combined = "\n".join(c["text"] for c in chunks)
    assert "Hestenes" in combined
    assert combined.count(header) < 4, "Repeated running header polluted all 4 pages without stripping"


def test_f3_permission_encrypted_extractable_pdf_succeeds(tmp_path: Path) -> None:
    """T1-F3-04: Owner-password permission-encrypted PDF with empty user password extracts cleanly."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_permission_encrypted_pdf(in_dir / "perm_encrypted.pdf")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1
    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    assert len(chunks) >= 1
    assert any("Souriau" in c["text"] or "coadjoint" in c["text"].lower() for c in chunks)


def test_f3_pypdf_fallback_when_pdftotext_unavailable(tmp_path: Path) -> None:
    """T1-F3-05: When pdftotext is unavailable on PATH, extraction falls back to pypdf cleanly."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "fallback.pdf", topic="octonions", pages=2)

    proc = _run_pdf_ingest(in_dir, out_dir, env_overrides={"PATH": ""})
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1
    assert "pypdf" in str(docs[0].get("parser", "")).lower()
    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    assert any("Albert" in c["text"] or "Octonions" in c["text"] for c in chunks)


# ===========================================================================
# F4 — Mathematical Archetypal & DAG Extraction + Enrichment (5 tests)
# ===========================================================================


def test_f4_extracts_sections_definitions_theorems_proofs_equations(tmp_path: Path) -> None:
    """T1-F4-01: Structured math PDF emits sections, definition/theorem/proof chunks, and entities."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "arch.pdf", topic="clifford", pages=2)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    sections = read_jsonl(out_dir / "alexandria_sections.jsonl")
    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    entities = read_jsonl(out_dir / "alexandria_entities.jsonl")
    assert len(sections) >= 1
    kinds = {c.get("chunkKind") for c in chunks}
    assert {"definition", "theorem", "proof"}.issubset(kinds), f"Missing expected chunkKinds in {kinds}"
    assert len(entities) >= 1


def test_f4_emits_directed_dag_edges_with_valid_endpoints(tmp_path: Path) -> None:
    """T1-F4-02: Directed DAG edges connect emitted nodes with required metadata and valid endpoints."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "dag.pdf", topic="clifford", pages=2)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    node_ids: set[str] = set()
    for col in ("alexandria_documents", "alexandria_sections", "alexandria_chunks", "alexandria_entities"):
        for row in read_jsonl(out_dir / f"{col}.jsonl"):
            node_ids.add(f"{col}/{row['_key']}")

    dag_edges = read_jsonl(out_dir / "alexandria_dag_edges.jsonl")
    assert len(dag_edges) >= 1
    edge_types = {e.get("edgeType") for e in dag_edges}
    assert edge_types & {
        "proof_proves_theorem",
        "chunk_uses_definition",
        "chunk_references_result",
        "chunk_cites_entry",
        "section_precedes_section",
    }
    for edge in dag_edges:
        for req in ("_key", "_from", "_to", "documentKey", "edgeType", "confidence"):
            assert req in edge, f"DAG edge missing {req}: {edge}"
        assert edge["_from"] in node_ids, f"Dangling _from in DAG JSONL: {edge['_from']}"
        assert edge["_to"] in node_ids, f"Dangling _to in DAG JSONL: {edge['_to']}"


def test_f4_deterministic_keys_and_source_authority_provenance(tmp_path: Path) -> None:
    """T1-F4-03: Two independent runs emit identical _keys and full retrieval_context_only provenance."""
    in_dir = tmp_path / "in"
    out_1 = tmp_path / "out1"
    out_2 = tmp_path / "out2"
    build_structured_math_pdf(in_dir / "det.pdf", topic="peirce", pages=2)

    assert _run_pdf_ingest(in_dir, out_1).returncode == 0
    assert _run_pdf_ingest(in_dir, out_2).returncode == 0

    for fname in (
        "alexandria_documents.jsonl",
        "alexandria_sections.jsonl",
        "alexandria_chunks.jsonl",
        "alexandria_entities.jsonl",
        "alexandria_dag_edges.jsonl",
    ):
        k1 = [r["_key"] for r in read_jsonl(out_1 / fname)]
        k2 = [r["_key"] for r in read_jsonl(out_2 / fname)]
        assert k1 == k2, f"Non-deterministic _key sequence in {fname}"

    doc = read_jsonl(out_1 / "alexandria_documents.jsonl")[0]
    assert doc["sourceType"] == "pdf"
    assert doc["sourceAuthority"] == "retrieval_context_only"

    for ch in read_jsonl(out_1 / "alexandria_chunks.jsonl"):
        assert ch["sourceAuthority"] == "retrieval_context_only"
        prov = ch["provenance"]
        for k in ("path", "contentHash", "sourceFormat", "pageStart", "pageEnd"):
            assert k in prov, f"Chunk provenance missing {k}"
        assert prov["sourceFormat"] == "pdf"


def test_f4_deterministic_semantic_payload_fields_present(tmp_path: Path) -> None:
    """T1-F4-04: Each chunk includes deterministic semantic payload fields without Ollama."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "sem.pdf", topic="clifford", pages=2)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    assert chunks
    for ch in chunks:
        sem = ch.get("semantic")
        assert isinstance(sem, dict), f"Missing semantic payload on chunk {ch.get('_key')}"
        for field in (
            "summary",
            "assumed_definitions",
            "mathematical_entities",
            "graph_triplets",
            "symbolic_terms",
            "semantic_mode",
        ):
            assert field in sem, f"semantic.{field} missing on chunk {ch.get('_key')}"
        assert sem["summary"]
    thm_chunks = [c for c in chunks if c.get("chunkKind") in {"theorem", "definition"}]
    assert any(c["semantic"]["mathematical_entities"] or c["semantic"]["symbolic_terms"] for c in thm_chunks)


def test_f4_all_schema_jsonl_artifacts_emitted_and_valid_json(tmp_path: Path) -> None:
    """T1-F4-05: All 10 Alexandria PDF JSONL artifact files exist and parse cleanly with _key."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "schema.pdf", topic="octonions", pages=2)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    expected_files = (
        "alexandria_documents.jsonl",
        "alexandria_sections.jsonl",
        "alexandria_chunks.jsonl",
        "alexandria_entities.jsonl",
        "alexandria_document_section_edges.jsonl",
        "alexandria_section_chunk_edges.jsonl",
        "alexandria_chunk_adjacent_edges.jsonl",
        "alexandria_chunk_entity_edges.jsonl",
        "alexandria_entity_relation_edges.jsonl",
        "alexandria_dag_edges.jsonl",
    )
    for fname in expected_files:
        rows = read_jsonl(out_dir / fname)
        for row in rows:
            assert isinstance(row.get("_key"), str) and row["_key"], f"Missing _key in {fname}: {row}"


# ===========================================================================
# F5 — Idempotent ArangoDB Storage & alexandria_chunks_search (5 tests)
# ===========================================================================


def test_f5_arango_ingest_creates_collections_indexes_and_search_view(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F5-01: arango_ingest.py creates all node/edge collections, indexes, and search view."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "ingest.pdf", topic="clifford", pages=2)
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    proc = run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--input-dir", str(out_dir),
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--username", isolated_alexandria_db["username"],
            "--password", isolated_alexandria_db["password"],
        ]
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    summary = json.loads(proc.stdout)
    assert summary.get("searchView", {}).get("alexandria_chunks_search") in {"created", "updated"}

    cols = arango_list_collections(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
    )
    for expected in (
        "alexandria_documents",
        "alexandria_sections",
        "alexandria_chunks",
        "alexandria_entities",
        "alexandria_document_section_edges",
        "alexandria_section_chunk_edges",
        "alexandria_chunk_adjacent_edges",
        "alexandria_chunk_entity_edges",
        "alexandria_entity_relation_edges",
        "alexandria_dag_edges",
    ):
        assert expected in cols, f"Missing collection {expected} in {cols}"

    views = arango_list_views(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
    )
    assert "alexandria_chunks_search" in views


def test_f5_ingested_document_and_dag_counts_match_jsonl(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F5-02: ArangoDB collection counts match emitted JSONL row counts 1-to-1."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "counts.pdf", topic="peirce", pages=2)
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    proc = run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--input-dir", str(out_dir),
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--username", isolated_alexandria_db["username"],
            "--password", isolated_alexandria_db["password"],
        ]
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    for col in (
        "alexandria_documents",
        "alexandria_sections",
        "alexandria_chunks",
        "alexandria_entities",
        "alexandria_document_section_edges",
        "alexandria_section_chunk_edges",
        "alexandria_chunk_adjacent_edges",
        "alexandria_chunk_entity_edges",
        "alexandria_entity_relation_edges",
        "alexandria_dag_edges",
    ):
        expected = len(read_jsonl(out_dir / f"{col}.jsonl"))
        actual = arango_collection_count(
            isolated_alexandria_db["endpoint"],
            isolated_alexandria_db["database"],
            isolated_alexandria_db["username"],
            isolated_alexandria_db["password"],
            col,
        )
        assert actual == expected, f"Count mismatch for {col}: DB={actual} vs JSONL={expected}"


def test_f5_bm25_arangosearch_view_returns_ingested_chunk(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F5-03: alexandria_chunks_search BM25 AQL query returns ingested chunk with positive score."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "bm25.pdf", topic="clifford", pages=2)
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    assert run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--input-dir", str(out_dir),
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--username", isolated_alexandria_db["username"],
            "--password", isolated_alexandria_db["password"],
        ]
    ).returncode == 0

    rows = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        (
            'FOR c IN alexandria_chunks_search '
            'SEARCH ANALYZER(c.text IN TOKENS(@q, "text_en"), "text_en") '
            'OPTIONS {waitForSync: true} '
            'SORT BM25(c) DESC LIMIT 5 RETURN {key: c._key, score: BM25(c), text: c.text}'
        ),
        {"q": "Hestenes spinor Clifford"},
    )
    assert len(rows) >= 1
    assert rows[0]["score"] > 0


def test_f5_skip_unchanged_skips_matching_content_hash(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F5-04: Re-running arango_ingest.py --skip-unchanged skips unchanged contentHash docs."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "skip.pdf", topic="octonions", pages=2)
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    base_args = [
        str(ARANGO_INGEST_SCRIPT),
        "--input-dir", str(out_dir),
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
        "--username", isolated_alexandria_db["username"],
        "--password", isolated_alexandria_db["password"],
    ]
    assert run_cli(base_args).returncode == 0
    proc2 = run_cli([*base_args, "--skip-unchanged"])
    assert proc2.returncode == 0, f"stderr={proc2.stderr}"
    summary = json.loads(proc2.stdout)
    assert summary["skippedUnchanged"] == 1
    assert summary["imported"] == {}


def test_f5_replace_documents_replaces_without_duplicating(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F5-05: Re-running arango_ingest.py --replace-documents preserves counts with 0 dangling edges."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "rep.pdf", topic="peirce", pages=2)
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    base_args = [
        str(ARANGO_INGEST_SCRIPT),
        "--input-dir", str(out_dir),
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
        "--username", isolated_alexandria_db["username"],
        "--password", isolated_alexandria_db["password"],
    ]
    assert run_cli(base_args).returncode == 0
    before_chunks = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_chunks",
    )
    proc2 = run_cli([*base_args, "--replace-documents"])
    assert proc2.returncode == 0, f"stderr={proc2.stderr}"
    after_chunks = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_chunks",
    )
    assert after_chunks == before_chunks


# ===========================================================================
# F6 — Full Corpus Ingestion & Integrity Verification (5 tests)
# ===========================================================================


def test_f6_end_to_end_pipeline_with_ingest_arango_flag(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F6-01: Single-command pdf_corpus_ingest.py --ingest-arango writes JSONL, manifest, and DB."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "one.pdf", topic="clifford", pages=2)
    build_structured_math_pdf(in_dir / "two.pdf", topic="octonions", pages=2)

    proc = _run_pdf_ingest(
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
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    assert (out_dir / "corpus_inventory_report.json").exists()
    doc_count = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_documents",
    )
    assert doc_count == 2


def test_f6_zero_dangling_edges_across_all_edge_collections(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F6-02: Zero dangling _from/_to endpoints exist across all edge collections in ArangoDB."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "d1.pdf", topic="clifford", pages=2)
    build_structured_math_pdf(in_dir / "d2.pdf", topic="peirce", pages=2)

    proc = _run_pdf_ingest(
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
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    edge_cols = (
        "alexandria_document_section_edges",
        "alexandria_section_chunk_edges",
        "alexandria_chunk_adjacent_edges",
        "alexandria_chunk_entity_edges",
        "alexandria_entity_relation_edges",
        "alexandria_dag_edges",
    )
    for col in edge_cols:
        dangling = arango_aql(
            isolated_alexandria_db["endpoint"],
            isolated_alexandria_db["database"],
            isolated_alexandria_db["username"],
            isolated_alexandria_db["password"],
            f"FOR e IN {col} FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null RETURN e._key",
        )
        assert dangling == [], f"Dangling edges found in {col}: {dangling}"


def test_f6_inventory_report_100_percent_accounting_invariant(tmp_path: Path) -> None:
    """T1-F6-03: 4-file mixed corpus satisfies totalFilesScanned == nonPdf + dupSkipped + uniqueProcessed."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    p1 = build_structured_math_pdf(in_dir / "p1.pdf", topic="clifford")
    build_structured_math_pdf(in_dir / "p2.pdf", topic="octonions")
    (in_dir / "p1_dup.pdf").write_bytes(p1.read_bytes())
    (in_dir / "note.txt").write_text("not a pdf", encoding="utf-8")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    total = report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles")
    non_pdf = report_metric(report, "nonPdfSkipped", "non_pdf_skipped", "nonPdfsSkipped")
    dup_skip = report_metric(report, "duplicateSkipped", "duplicate_skipped", "duplicate_skipped_count", "duplicatesSkipped")
    unique_cnt = report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs")
    assert total == 4
    assert non_pdf == 1
    assert dup_skip == 1
    assert unique_cnt == 2
    assert total == non_pdf + dup_skip + unique_cnt

    entries = report_entries(report)
    if entries:
        paths_text = json.dumps(report)
        for name in ("p1.pdf", "p2.pdf", "p1_dup.pdf"):
            assert name in paths_text, f"Missing path {name} in inventory manifest"
    non_pdf_by_ext = report.get("non_pdf_by_extension")
    if isinstance(non_pdf_by_ext, dict):
        assert non_pdf_by_ext.get(".txt") == 1, f"Expected .txt count 1, got {non_pdf_by_ext}"


def test_f6_sampled_documents_preserve_source_authority_and_hash(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F6-04: Stored ArangoDB documents preserve retrieval_context_only, pdf type, sha256, pageCount."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "auth.pdf", topic="clifford", pages=2)

    proc = _run_pdf_ingest(
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
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR d IN alexandria_documents RETURN d",
    )
    assert len(docs) == 1
    d = docs[0]
    assert d["sourceAuthority"] == "retrieval_context_only"
    assert d["sourceType"] == "pdf"
    assert re.fullmatch(r"[0-9a-f]{64}", str(d.get("contentHash", "")))
    assert d["pageCount"] == 2


def test_f6_limit_flag_processes_exact_subset_cleanly(tmp_path: Path) -> None:
    """T1-F6-05: --limit 2 on 5 unique PDFs extracts exactly 2 documents and records total discovered."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    for i in range(5):
        build_structured_math_pdf(in_dir / f"doc_{i}.pdf", title=f"Doc {i}", topic="clifford")

    proc = _run_pdf_ingest(in_dir, out_dir, extra_args=["--limit", "2"])
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 2
    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 5


# ===========================================================================
# F7 — Searchable Formalization Context Retrieval (5 tests)
# ===========================================================================


def test_f7_retrieve_context_jsonl_mode_returns_ranked_attributed_hits(tmp_path: Path) -> None:
    """T1-F7-01: retrieve_context.py --input-dir returns ranked hits with provenance & authority."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "clifford.pdf", title="Clifford Spinors", topic="clifford")
    build_structured_math_pdf(in_dir / "octonions.pdf", title="Split Octonions", topic="octonions")
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    proc = run_cli(
        [
            str(RETRIEVE_CONTEXT_SCRIPT),
            "--input-dir", str(out_dir),
            "--query", "Clifford algebra spinor",
            "--top-k", "5",
        ]
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    packet = json.loads(proc.stdout)
    assert_retrieval_authority(packet)
    hits = packet.get("hits", [])
    assert len(hits) >= 1
    scores = [h["score"] for h in hits]
    assert scores == sorted(scores, reverse=True)
    first = hits[0]
    assert hit_field(first, "path")
    assert hit_field(first, "contentHash")
    assert hit_field(first, "pageStart") is not None


def test_f7_retrieve_context_arango_mode_returns_bm25_and_dag_neighbors(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F7-02: retrieve_context.py --arango returns BM25 hits, DAG neighbors, and retrieval_context_only."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "clifford.pdf", title="Clifford Spinors", topic="clifford")
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

    proc = run_cli(
        [
            str(RETRIEVE_CONTEXT_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "Hestenes Spinor Decomposition",
            "--top-k", "5",
        ],
        env_overrides={
            "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
            "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
        },
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    packet = json.loads(proc.stdout)
    assert_retrieval_authority(packet)
    hits = packet.get("hits", [])
    assert len(hits) >= 1
    first = hits[0]
    assert hit_field(first, "documentKey")
    assert hit_field(first, "path")
    assert hit_field(first, "contentHash")
    assert hit_field(first, "pageStart") is not None
    assert hit_field(first, "chunkKind")
    assert "neighbors" in first or "dagNeighbors" in first


def test_f7_graph_context_rank_arango_mode_ranks_subgraph(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F7-03: graph_context_rank.py --arango ranks subgraph with graphScore, lexicalScore, authority."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "peirce.pdf", title="Peirce Drazin", topic="peirce")
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

    proc = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "Peirce Drazin inverse",
            "--top-k", "5",
        ],
        env_overrides={
            "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
            "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
        },
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    packet = json.loads(proc.stdout)
    assert_retrieval_authority(packet)
    assert isinstance(packet.get("graph"), dict)
    assert isinstance(packet.get("seeds"), list)
    hits = packet.get("hits", [])
    assert len(hits) >= 1
    assert "graphScore" in hits[0] and "lexicalScore" in hits[0]


def test_f7_graph_rag_query_alexandria_scope_returns_pdf_hits(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F7-04: graph_rag_query.py --scope alexandria returns PDF hits and leaves gravity null."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "octonions.pdf", title="Split Octonions", topic="octonions")
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

    proc = run_cli(
        [
            str(GRAPH_RAG_QUERY_SCRIPT),
            "Albert Vector split octonions G2",
            "--scope", "alexandria",
            "--format", "json",
            "--no-gravity",
        ],
        env_overrides={
            "ALEXANDRIA_ARANGO_ENDPOINT": isolated_alexandria_db["endpoint"],
            "ALEXANDRIA_ARANGO_DB": isolated_alexandria_db["database"],
            "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
            "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
        },
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    payload = json.loads(proc.stdout)
    assert payload.get("gravity") is None
    alex_hits = payload.get("alexandria", [])
    assert len(alex_hits) >= 1
    assert "retrieval_context_only" in json.dumps(payload)


def test_f7_ask_repo_alexandria_scope_brief_and_answer_modes(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T1-F7-05: ask_repo.py --scope alexandria --brief and --answer cite PDFs as retrieval context only."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "clifford.pdf", title="Clifford Spinors", topic="clifford")
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

    env = {
        "ALEXANDRIA_ARANGO_ENDPOINT": isolated_alexandria_db["endpoint"],
        "ALEXANDRIA_ARANGO_DB": isolated_alexandria_db["database"],
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    for mode_flag in ("--brief", "--answer"):
        proc = run_cli(
            [str(ASK_REPO_SCRIPT), "Hestenes spinor Clifford", "--scope", "alexandria", mode_flag, "--no-gravity"],
            env_overrides=env,
        )
        assert proc.returncode == 0, f"{mode_flag} failed: {proc.stderr}"
        out_lower = proc.stdout.lower()
        assert "clifford" in out_lower or "hestenes" in out_lower
        assert "retrieval" in out_lower
        assert "not" in out_lower and "proof" in out_lower
