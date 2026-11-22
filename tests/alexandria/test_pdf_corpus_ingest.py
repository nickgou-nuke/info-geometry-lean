"""Unit and integration tests for tools/alexandria/pdf_corpus_ingest.py (F2, F3, F4)."""
from __future__ import annotations

import json
import os
import subprocess
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

import pytest
from pypdf import PdfWriter
from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas

from tools.alexandria import arango_ingest, pdf_corpus_ingest
from tools.alexandria.pdf_corpus_ingest import (
    DAG_EDGE_TYPES,
    ExtractionResult,
    build_document_artifacts,
    normalize_pages,
    run_pdf_corpus_pipeline,
    verify_and_prune_dag,
)


def _make_text_pdf(path: Path, pages: list[list[str]], *, title: str | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    c = canvas.Canvas(str(path), pagesize=letter)
    if title:
        c.setTitle(title)
    for page_lines in pages:
        y = 740
        for line in page_lines:
            if line:
                c.drawString(60, y, line)
                y -= 16
            else:
                y -= 48
            if y < 60:
                break
        c.showPage()
    c.save()


def _make_blank_pdf(path: Path, *, encrypted_password: str | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    writer = PdfWriter()
    writer.add_blank_page(width=612, height=792)
    if encrypted_password is not None:
        writer.encrypt(encrypted_password)
    with path.open("wb") as fh:
        writer.write(fh)


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_inventory_dedup_and_magic_header_accounting(tmp_path: Path) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()
    pages = [
        [
            "Abstract",
            "We study Clifford algebras and Krein spaces in noncommutative geometry.",
            "1. Introduction",
            "Definition 1.1 (Krein space). A Krein space is an indefinite inner product space.",
            "Theorem 1.2. Every fundamental symmetry J satisfies J^2 = I in our setting.",
            "Proof. This follows directly from Definition 1.1 and standard axioms.",
        ]
    ]
    canonical = corpus / "paper.pdf"
    _make_text_pdf(canonical, pages, title="Krein Clifford Paper")

    # Exact duplicate with browser copy name in subdir
    dup = corpus / "subdir" / "paper (1).pdf"
    dup.parent.mkdir(parents=True)
    dup.write_bytes(canonical.read_bytes())

    # Extensionless %PDF- magic header file (unique content)
    magic_src = tmp_path / "magic_tmp.pdf"
    _make_text_pdf(
        magic_src,
        [["1. Preliminaries", "Theorem 2.1. A Souriau symplectic cocycle gives a Gibbs state." * 2]],
        title="Magic PDF",
    )
    magic_file = corpus / "document_magic"
    magic_file.write_bytes(magic_src.read_bytes())

    # Non-PDF files
    (corpus / "notes.txt").write_text("not a pdf", encoding="utf-8")
    (corpus / "index.html").write_text("<html></html>", encoding="utf-8")
    (corpus / "image.png").write_bytes(b"\x89PNG\r\n\x1a\n")

    # 0-byte PDF
    (corpus / "empty.pdf").write_bytes(b"")

    # Symlink to existing PDF (followlinks=False must not double-count)
    symlink_pdf = corpus / "link_to_paper.pdf"
    os.symlink(canonical, symlink_pdf)

    out_dir = tmp_path / "out"
    report = run_pdf_corpus_pipeline(input_dir=corpus, output_dir=out_dir, workers=2)

    assert report["symlinks_skipped"] == 1
    assert report["non_pdf_skipped"] == 3
    assert report["pdf_extension_count"] == 3
    assert report["magic_header_non_pdf_ext_count"] == 1
    assert report["total_pdf_files"] == 4
    assert report["total_scanned_files"] == report["non_pdf_skipped"] + report["total_pdf_files"]
    assert report["unique_sha256_count"] == 3
    assert report["duplicate_skipped_count"] == 1
    assert sum(report["outcome_counts"].values()) == report["total_pdf_files"]
    assert report["outcome_counts"]["duplicate_skipped"] == 1
    assert report["outcome_counts"]["empty_0_bytes"] == 1
    assert report["outcome_counts"]["ingested"] == 2

    dup_group = report["duplicate_groups"][0]
    assert dup_group["canonicalPath"] == canonical.as_posix()
    assert dup_group["duplicatePaths"] == [dup.as_posix()]
    assert (out_dir / "corpus_inventory_report.json").exists()
    assert (out_dir / "corpus_inventory_report.md").exists()


def test_resilient_extraction_statuses_and_normalization(tmp_path: Path) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()

    # (a) Multi-page PDF with running headers/footers, ligature, theorem/proof/refs
    _make_text_pdf(
        corpus / "good.pdf",
        [
            [
                "JOURNAL RUNNING HEADER 2026",
                "1",
                "Abstract",
                "We de\ufb01ne Clifford structures on Krein spaces [1].",
                "1. Introduction",
                "Definition 1.1 (Fundamental symmetry). A fundamental symmetry satisfies J^2 = 1.",
                "Page Footer Text 1",
            ],
            [
                "JOURNAL RUNNING HEADER 2026",
                "2",
                "2. Main Results",
                "Theorem 2.1. By Definition 1.1, the Krein space splits orthogonally [1].",
                "Proof of Theorem 2.1. Using Definition 1.1 we obtain the orthogonal splitting.",
                "Page Footer Text 2",
            ],
            [
                "JOURNAL RUNNING HEADER 2026",
                "3",
                "References",
                "[1] A. Author, Noncommutative Krein Geometry, arXiv:2303.03452, 2023.",
                "Page Footer Text 3",
            ],
        ],
        title="Krein Space Foundations",
    )

    # (b) Blank-page PDF -> scanned_no_text
    _make_blank_pdf(corpus / "scanned.pdf")

    # (c) Encrypted blank PDF -> encrypted_no_text
    _make_blank_pdf(corpus / "encrypted.pdf", encrypted_password="secret")

    # (d) Very low text PDF (< 100 chars) -> very_low_text_skipped
    _make_text_pdf(corpus / "tiny.pdf", [["Too short."]])

    # (e) Corrupt PDF -> parse_error
    (corpus / "corrupt.pdf").write_bytes(b"%PDF-1.4\n%%corrupt-garbage-bytes\n")

    out_dir = tmp_path / "out"
    report = run_pdf_corpus_pipeline(input_dir=corpus, output_dir=out_dir, min_text_chars=100, workers=2)

    assert report["total_pdf_files"] == 5
    assert sum(report["outcome_counts"].values()) == 5
    assert report["outcome_counts"]["ingested"] == 1
    assert report["outcome_counts"]["scanned_no_text"] == 1
    assert report["outcome_counts"]["encrypted_no_text"] == 1
    assert report["outcome_counts"]["very_low_text_skipped"] == 1
    assert report["outcome_counts"]["parse_error"] == 1

    chunks = _read_jsonl(out_dir / "alexandria_chunks.jsonl")
    all_chunk_text = "\n".join(c["text"] for c in chunks)
    assert "Clifford structures on Krein spaces" in all_chunk_text
    assert "JOURNAL RUNNING HEADER 2026" not in all_chunk_text
    assert "Page Footer Text" not in all_chunk_text

    # Direct normalization checks for Unicode ligatures, control chars, PUA noise, and running headers
    raw_with_ligatures = (
        "HEADER TITLE\n1\nWe de\ufb01ne \ufb02ow and e\ufb00ect.\x02\x0c"
        "HEADER TITLE\n2\nSecond page \ue000\ue001 text.\x0c"
        "HEADER TITLE\n3\nThird page text."
    )
    norm_pages, noise_ratio, warnings = normalize_pages(raw_with_ligatures, expected_pages=3)
    joined_norm = "\n".join(txt for _, txt in norm_pages)
    assert "define flow and effect." in joined_norm
    assert "\ufb01" not in joined_norm
    assert "\x02" not in joined_norm
    assert "HEADER TITLE" not in joined_norm
    assert noise_ratio > 0.005
    assert "encoding_noise" in warnings

    thm_chunks = [c for c in chunks if c["chunkKind"] == "theorem"]
    assert len(thm_chunks) == 1
    assert thm_chunks[0]["provenance"]["pageStart"] == 2
    assert thm_chunks[0]["provenance"]["pageEnd"] == 2


def test_archetypal_dag_edges_and_acyclicity(tmp_path: Path) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()

    # Paper B (cited by Paper A via arXiv ID)
    _make_text_pdf(
        corpus / "2303.03452v1.pdf",
        [
            [
                "Abstract",
                "A foundational treatment of Drazin inverses on Krein spaces.",
                "1. Introduction",
                "Definition 1.1 (Drazin inverse). An operator T has a Drazin inverse if T^k T^D T = T^k.",
            ]
        ],
        title="Drazin Inverses in Krein Spaces",
    )

    # Paper A with abstract, definition, theorem, proof, equation, bibliography, cross-doc cite
    _make_text_pdf(
        corpus / "paper_a.pdf",
        [
            [
                "Abstract",
                "We connect Moore-Penrose and Drazin projectors in Clifford algebras [1].",
                "1. Preliminaries",
                "Definition 1.1 (Krein projector). A Krein projector P satisfies P^2 = P.",
                "",
                "P J = J P* (1.1)",
                "",
                "2. Main Theorem",
                "Theorem 2.1. By Definition 1.1 and Eq. (1.1), every Krein projector admits a decomposition [1].",
                "Proof of Theorem 2.1. Applying Definition 1.1 completes the argument.",
                "3. References",
                "[1] J. Researcher, Drazin Inverses in Krein Spaces, arXiv:2303.03452v1, 2023.",
            ]
        ],
        title="Krein Projectors and Drazin Theory",
    )

    out_dir = tmp_path / "out"
    report = run_pdf_corpus_pipeline(input_dir=corpus, output_dir=out_dir, workers=1)

    docs = _read_jsonl(out_dir / "alexandria_documents.jsonl")
    chunks = _read_jsonl(out_dir / "alexandria_chunks.jsonl")
    entities = _read_jsonl(out_dir / "alexandria_entities.jsonl")
    rel_edges = _read_jsonl(out_dir / "alexandria_entity_relation_edges.jsonl")
    dag_edges = _read_jsonl(out_dir / "alexandria_dag_edges.jsonl")

    assert len(docs) == 2
    for doc in docs:
        assert doc["_key"].startswith("doc_")
        assert len(doc["_key"]) == 24
        assert doc["sourceAuthority"] == "retrieval_context_only"

    kinds = {c["chunkKind"] for c in chunks}
    assert {"abstract", "definition", "theorem", "proof", "equation", "bibliography"} <= kinds
    for chunk in chunks:
        assert chunk["sourceAuthority"] == "retrieval_context_only"
        assert chunk["searchTerms"]

    # arango_ingest compatibility: chunkKey & documentKey on every entity and relation edge
    assert entities
    for ent in entities:
        assert ent.get("chunkKey")
        assert ent.get("documentKey")
    for rel in rel_edges:
        assert rel.get("chunkKey")
        assert rel.get("documentKey")

    edge_types = {e["edgeType"] for e in dag_edges}
    assert set(DAG_EDGE_TYPES) <= edge_types
    assert report["dag_edges_pruned_for_cycles"] == 0

    # Verify cycle pruning breaks injected mutual citation cycle
    cyclic = [
        {"_key": "e1", "_from": "alexandria_documents/a", "_to": "alexandria_documents/b", "edgeType": "document_cites_document"},
        {"_key": "e2", "_from": "alexandria_documents/b", "_to": "alexandria_documents/a", "edgeType": "document_cites_document"},
    ]
    kept, pruned = verify_and_prune_dag(cyclic)
    assert len(kept) == 1
    assert len(pruned) == 1


def test_arango_ingest_json_compatibility_skip_and_replace(tmp_path: Path) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()
    _make_text_pdf(
        corpus / "p1.pdf",
        [["1. Intro", "Definition 1.1 (Spinor). A spinor is an element of a Clifford module.", "Theorem 1.2. Spinors exist by Definition 1.1.", "Proof. Trivial."]],
        title="Spinor Paper",
    )
    _make_text_pdf(
        corpus / "p2.pdf",
        [["1. Intro", "Theorem 2.1. Souriau moment maps preserve symplectic form." * 2]],
        title="Souriau Paper",
    )
    out_dir = tmp_path / "out"
    run_pdf_corpus_pipeline(input_dir=corpus, output_dir=out_dir, workers=1)

    all_cols = arango_ingest.DOCUMENT_COLLECTIONS + arango_ingest.EDGE_COLLECTIONS
    assert "alexandria_dag_edges" in arango_ingest.EDGE_COLLECTIONS
    loaded = arango_ingest.load_artifacts(out_dir, all_cols)
    docs = loaded["alexandria_documents"]
    assert len(docs) == 2

    skip_key = docs[0]["_key"]
    keep_key = docs[1]["_key"]
    arango_ingest.drop_rows_for_documents(loaded, {skip_key})

    assert [d["_key"] for d in loaded["alexandria_documents"]] == [keep_key]
    assert all(c["documentKey"] == keep_key for c in loaded["alexandria_chunks"])
    assert all(e["documentKey"] == keep_key for e in loaded["alexandria_entities"])
    assert all(e["documentKey"] == keep_key for e in loaded["alexandria_dag_edges"])
    kept_chunk_keys = {c["_key"] for c in loaded["alexandria_chunks"]}
    kept_ent_keys = {e["_key"] for e in loaded["alexandria_entities"]}
    for edge in loaded["alexandria_chunk_entity_edges"]:
        assert edge["_from"].split("/", 1)[1] in kept_chunk_keys
        assert edge["_to"].split("/", 1)[1] in kept_ent_keys

    # add_search_terms preserves precomputed searchTerms
    for ch in loaded["alexandria_chunks"]:
        before = set(ch["searchTerms"])
        updated = arango_ingest.add_search_terms(dict(ch))
        assert before <= set(updated["searchTerms"])


def test_bounded_ollama_enrichment_and_fallback(tmp_path: Path) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()
    _make_text_pdf(
        corpus / "multi.pdf",
        [
            [
                "Abstract",
                "A study of Clifford algebras and Krein spaces.",
                "1. Setup",
                "Definition 1.1 (Krein space). An indefinite inner product space.",
                "Theorem 1.2. Every Krein space admits a fundamental symmetry.",
                "Theorem 1.3. Fundamental symmetries square to the identity.",
                "Theorem 1.4. Additional boundedness statement for testing cap.",
            ]
        ],
        title="Bounded Enrichment Test",
    )

    state = {"mode": "ok", "chat_calls": 0}

    class _Handler(BaseHTTPRequestHandler):
        def log_message(self, format: str, *args: Any) -> None:  # noqa: A002
            return

        def do_GET(self) -> None:  # noqa: N802
            if self.path == "/api/tags":
                body = json.dumps({"models": [{"name": "mock-model"}]}).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.end_headers()
                self.wfile.write(body)
                return
            self.send_response(404)
            self.end_headers()

        def do_POST(self) -> None:  # noqa: N802
            length = int(self.headers.get("Content-Length", "0"))
            _ = self.rfile.read(length)
            state["chat_calls"] += 1
            if state["mode"] == "fail":
                self.send_response(500)
                self.end_headers()
                return
            payload = {
                "message": {
                    "content": json.dumps(
                        {
                            "summary": "Mocked Ollama mathematical summary.",
                            "assumed_definitions": ["Krein space"],
                            "mathematical_entities": ["fundamental symmetry"],
                            "symbolic_terms": ["J^2 = I"],
                            "graph_triplets": [["Krein space", "admits", "fundamental symmetry"]],
                        }
                    )
                }
            }
            body = json.dumps(payload).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)

    server = ThreadingHTTPServer(("127.0.0.1", 0), _Handler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        endpoint = f"http://127.0.0.1:{port}"
        out_ok = tmp_path / "out_ok"
        rep_ok = run_pdf_corpus_pipeline(
            input_dir=corpus,
            output_dir=out_ok,
            enrich_ollama=True,
            ollama_endpoint=endpoint,
            ollama_model="mock-model",
            enrich_ollama_max_chunks=2,
            enrich_ollama_timeout=5.0,
            workers=1,
        )
        assert state["chat_calls"] == 2
        assert rep_ok["ollama_enrichment"]["enriched"] == 2
        chunks_ok = _read_jsonl(out_ok / "alexandria_chunks.jsonl")
        ollama_modes = [c for c in chunks_ok if c["semantic"]["semantic_mode"] == "ollama_mock-model_v1"]
        det_modes = [c for c in chunks_ok if c["semantic"]["semantic_mode"] == "deterministic_pdf_archetypal_v1"]
        assert len(ollama_modes) == 2
        assert len(det_modes) >= 1
        assert ollama_modes[0]["semantic"]["summary"] == "Mocked Ollama mathematical summary."
        # Never mutates raw text
        assert ollama_modes[0]["text"] == ollama_modes[0]["rawContent"]

        # Failure fallback + circuit breaker
        state["mode"] = "fail"
        state["chat_calls"] = 0
        out_fail = tmp_path / "out_fail"
        rep_fail = run_pdf_corpus_pipeline(
            input_dir=corpus,
            output_dir=out_fail,
            enrich_ollama=True,
            ollama_endpoint=endpoint,
            ollama_model="mock-model",
            enrich_ollama_max_chunks=5,
            enrich_ollama_timeout=5.0,
            enrich_ollama_max_failures=2,
            workers=1,
        )
        assert state["chat_calls"] == 2
        assert rep_fail["ollama_enrichment"]["circuit_breaker_tripped"] is True
        assert rep_fail["ollama_enrichment"]["fallbacks"] == 2
        chunks_fail = _read_jsonl(out_fail / "alexandria_chunks.jsonl")
        assert all(c["semantic"]["semantic_mode"] == "deterministic_pdf_archetypal_v1" for c in chunks_fail)
    finally:
        server.shutdown()
        server.server_close()


def test_pdf_corpus_ingest_rejects_forbidden_arango_target(tmp_path: Path) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()
    _make_text_pdf(corpus / "x.pdf", [["1. Intro", "Theorem 1.1. Sample content." * 5]])
    with pytest.raises(ValueError):
        run_pdf_corpus_pipeline(
            input_dir=corpus,
            output_dir=tmp_path / "out",
            ingest_arango=True,
            endpoint="http://127.0.0.1:8530",
            database="alexandria",
        )
    with pytest.raises(ValueError):
        run_pdf_corpus_pipeline(
            input_dir=corpus,
            output_dir=tmp_path / "out2",
            ingest_arango=True,
            endpoint="http://127.0.0.1:8532",
            database="infogeometry",
        )


def test_limit_negative_rejected_in_api_and_cli(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()
    _make_text_pdf(corpus / "x.pdf", [["1. Intro", "Theorem 1.1. Sample content." * 5]])
    with pytest.raises(ValueError, match="--limit must be >= 0"):
        run_pdf_corpus_pipeline(input_dir=corpus, output_dir=tmp_path / "out", limit=-1)
    assert not (tmp_path / "out").exists()

    with pytest.raises(SystemExit) as excinfo:
        pdf_corpus_ingest.main(["--input-dir", str(corpus), "--output-dir", str(tmp_path / "out2"), "--limit", "-1"])
    assert excinfo.value.code == 2
    assert "--limit must be >= 0" in capsys.readouterr().err


def test_head_sample_bibliography_exclusion_toc_and_allcaps_references(tmp_path: Path) -> None:
    corpus = tmp_path / "corpus"
    corpus.mkdir()

    # Citing PDF sorts alphabetically BEFORE cited PDF ("a_citing.pdf" < "z_cited.pdf")
    _make_text_pdf(
        corpus / "a_citing.pdf",
        [
            [
                "Contents",
                "1. Introduction",
                "2. References to Related Work",
                "References",
                "20",
                "Abstract",
                "This short paper studies Krein spaces [1].",
                "1. Introduction",
                "We cite work from arXiv.",
                "2. References to Related Work",
                "Section 2 discusses earlier ideas with doi:10.1000/ownpaper.",
                "REFERENCES",
                "[1] J. Cited, Target Paper, arXiv:2401.12345v1, 2024.",
            ]
        ],
        title="Citing Paper",
    )
    _make_text_pdf(
        corpus / "z_cited.pdf",
        [
            [
                "arXiv:2401.12345v1",
                "Abstract",
                "Target paper on Krein spaces and Clifford algebras.",
                "1. Introduction",
                "Definition 1.1 (Target). A target object.",
            ]
        ],
        title="Target Paper",
    )

    out_dir = tmp_path / "out"
    run_pdf_corpus_pipeline(input_dir=corpus, output_dir=out_dir, workers=1)

    docs = {d["relativePath"]: d for d in _read_jsonl(out_dir / "alexandria_documents.jsonl")}
    sections = _read_jsonl(out_dir / "alexandria_sections.jsonl")
    chunks = _read_jsonl(out_dir / "alexandria_chunks.jsonl")
    dag_edges = _read_jsonl(out_dir / "alexandria_dag_edges.jsonl")

    citing_doc_key = docs["a_citing.pdf"]["_key"]
    cited_doc_key = docs["z_cited.pdf"]["_key"]

    citing_secs = [s["title"] for s in sections if s["documentKey"] == citing_doc_key]
    assert "REFERENCES" in citing_secs
    bib_chunks = [c for c in chunks if c["documentKey"] == citing_doc_key and c["chunkKind"] == "bibliography"]
    assert len(bib_chunks) == 1

    sample = pdf_corpus_ingest._pre_bibliography_head_sample(
        [
            "Contents",
            "References",
            "20",
            "Abstract",
            "Short paper body.",
            "2. References to Related Work",
            "Body doi:10.1000/ownpaper",
            "REFERENCES",
            "[1] Cited arXiv:2401.12345v1",
        ]
    )
    assert "doi:10.1000/ownpaper" in sample
    assert "2401.12345v1" not in sample

    cross_edges = [e for e in dag_edges if e["edgeType"] == "document_cites_document"]
    assert len(cross_edges) == 1
    assert cross_edges[0]["_from"] == f"alexandria_documents/{citing_doc_key}"
    assert cross_edges[0]["_to"] == f"alexandria_documents/{cited_doc_key}"


def test_duplicate_bib_entries_emit_unique_edge_keys() -> None:
    ext = ExtractionResult(
        sha256="a" * 64,
        canonical_path=Path("/tmp/dup_bib.pdf"),
        rel_path="dup_bib.pdf",
        duplicate_paths=[],
        size_bytes=1234,
        outcome="ingested",
        reason="ok",
        page_count=1,
        char_count=300,
        parser="pdftotext",
        warnings=[],
        title="Duplicate Bib Test",
        author="",
        encrypted=False,
        encoding_noise_ratio=0.0,
        pages=[
            (
                1,
                "\n".join(
                    [
                        "1. Introduction",
                        "Definition 1.1 (Space). A space X.",
                        "Theorem 1.2. By Definition 1.1 and Definition 1.1 again, X holds [1].",
                        "REFERENCES",
                        "[1] A. First, Paper One (2020)",
                        "[1] A. First, Paper One (2020)",
                    ]
                ),
            )
        ],
    )
    pkt = build_document_artifacts(ext)
    for col in ("entities", "chunk_entity_edges", "entity_relation_edges", "dag_edges"):
        keys = [row["_key"] for row in pkt[col]]
        assert len(keys) == len(set(keys)), f"Duplicate _key found in {col}"


def test_run_pypdf_fallback_timeout_guard(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    dummy = tmp_path / "slow.pdf"
    _make_blank_pdf(dummy)

    def _raise_timeout(*args: Any, **kwargs: Any) -> Any:
        raise subprocess.TimeoutExpired(cmd=args[0], timeout=kwargs.get("timeout", 0.5))

    monkeypatch.setattr(pdf_corpus_ingest.subprocess, "run", _raise_timeout)
    text, pages, enc, meta, warnings = pdf_corpus_ingest._run_pypdf_fallback(dummy, timeout=0.5)
    assert text is None
    assert pages == 0
    assert enc is False
    assert meta == {}
    assert any(w.startswith("pypdf_timeout_0.5s") for w in warnings)

    # Also test real subprocess timeout via short-sleeping worker script
    monkeypatch.undo()
    monkeypatch.setattr(pdf_corpus_ingest, "_PYPDF_WORKER_CODE", "import time; time.sleep(2.0)")
    text2, _, _, _, warnings2 = pdf_corpus_ingest._run_pypdf_fallback(dummy, timeout=0.1)
    assert text2 is None
    assert "pypdf_timeout_0.1s" in warnings2


def test_clean_doi_and_bib_labels_and_pipeline_param_validation(tmp_path: Path) -> None:
    assert pdf_corpus_ingest._clean_doi("10.1234/abc)") == "10.1234/abc"
    assert pdf_corpus_ingest._clean_doi("10.1234/abc).") == "10.1234/abc"
    assert pdf_corpus_ingest._clean_doi("10.1016/0003-4916(83)90176-8)") == "10.1016/0003-4916(83)90176-8"
    assert pdf_corpus_ingest._clean_doi("10.1016/0003-4916(83)90176-8.") == "10.1016/0003-4916(83)90176-8"

    assert pdf_corpus_ingest._extract_labels("bibliography", "[1] Author, Paper (1984)\n[2] Other (2020)") == []

    corpus = tmp_path / "corpus"
    corpus.mkdir()
    _make_text_pdf(corpus / "x.pdf", [["1. Intro", "Theorem 1.1. Sample content." * 5]])
    for kwargs in (
        {"workers": 0},
        {"per_file_timeout": 0.0},
        {"per_file_timeout": -1.0},
        {"max_chunk_chars": 0},
        {"min_text_chars": -1},
    ):
        with pytest.raises(ValueError):
            run_pdf_corpus_pipeline(input_dir=corpus, output_dir=tmp_path / "out_bad", **kwargs)


def test_pre_bibliography_head_sample_toc_references_before_section_one() -> None:
    intro_sample = pdf_corpus_ingest._pre_bibliography_head_sample(
        [
            "Contents",
            "1. Introduction",
            "References",
            "1. Introduction",
            "Own DOI: doi:10.1000/own_intro",
            "REFERENCES",
            "[1] Cited, doi:10.9999/leak_intro",
        ]
    )
    assert "10.1000/own_intro" in intro_sample
    assert "10.9999/leak_intro" not in intro_sample

    subsec_sample = pdf_corpus_ingest._pre_bibliography_head_sample(
        [
            "Contents",
            "1. Preliminaries",
            "References",
            "1. Preliminaries",
            "1.1. Basic Setup",
            "Own DOI: doi:10.1000/own_subsec",
            "REFERENCES",
            "[1] Cited, doi:10.9999/leak_subsec",
        ]
    )
    assert "10.1000/own_subsec" in subsec_sample
    assert "10.9999/leak_subsec" not in subsec_sample
