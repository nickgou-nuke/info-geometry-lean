"""Tier 2: Boundary, corner-case, and negative E2E tests (38 tests across F1-F7)."""
from __future__ import annotations

import json
import os
from collections import defaultdict, deque
from pathlib import Path
from typing import Any

import pytest

from tests.e2e_alexandria_pdf.conftest import (
    ALEXANDRIA_ENDPOINT,
    ARANGO_INGEST_SCRIPT,
    ASK_REPO_SCRIPT,
    GRAPH_CONTEXT_RANK_SCRIPT,
    GRAPH_RAG_QUERY_SCRIPT,
    PDF_CORPUS_INGEST_SCRIPT,
    RETRIEVE_CONTEXT_SCRIPT,
    arango_aql,
    arango_collection_count,
    assert_retrieval_authority,
    build_corrupt_pdf,
    build_png_file,
    build_pua_noise_pdf,
    build_scanned_zero_text_pdf,
    build_structured_math_pdf,
    build_text_pdf,
    build_user_locked_encrypted_pdf,
    build_zero_byte_pdf,
    read_inventory_report,
    read_jsonl,
    report_metric,
    require_script,
    run_cli,
)

pytestmark = pytest.mark.tier2


def _run_pdf_ingest(in_dir: Path, out_dir: Path, extra_args: list[str] | None = None, **kwargs: Any) -> Any:
    script = require_script(PDF_CORPUS_INGEST_SCRIPT)
    cmd = [str(script), "--input-dir", str(in_dir), "--output-dir", str(out_dir)]
    if extra_args:
        cmd.extend(extra_args)
    return run_cli(cmd, **kwargs)


def _assert_dag_acyclic(edges: list[dict[str, Any]]) -> None:
    adj: dict[str, list[str]] = defaultdict(list)
    indeg: dict[str, int] = defaultdict(int)
    nodes: set[str] = set()
    for e in edges:
        src = str(e["_from"])
        dst = str(e["_to"])
        nodes.add(src)
        nodes.add(dst)
        adj[src].append(dst)
        indeg[dst] += 1
        indeg.setdefault(src, 0)
    q = deque([n for n in nodes if indeg[n] == 0])
    visited = 0
    while q:
        cur = q.popleft()
        visited += 1
        for nxt in adj[cur]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                q.append(nxt)
    assert visited == len(nodes), f"Cycle detected in alexandria_dag_edges ({visited}/{len(nodes)} acyclic)"


# ===========================================================================
# F1 — Lane Isolation & :8532 Guard Boundaries (6 tests)
# ===========================================================================


def test_f1_guard_rejects_port_8530_infogeometry_lane() -> None:
    """T2-F1-01: guard_alexandria_target rejects port 8530."""
    import igf.config.env_aliases as env_aliases

    guard = getattr(env_aliases, "guard_alexandria_target", None)
    assert callable(guard), "guard_alexandria_target missing from igf.config.env_aliases"
    with pytest.raises(ValueError, match="8530"):
        guard("http://127.0.0.1:8530", "alexandria")


def test_f1_guard_rejects_port_8540_hive_lane() -> None:
    """T2-F1-02: guard_alexandria_target rejects port 8540."""
    import igf.config.env_aliases as env_aliases

    guard = getattr(env_aliases, "guard_alexandria_target", None)
    assert callable(guard), "guard_alexandria_target missing from igf.config.env_aliases"
    with pytest.raises(ValueError, match="8540"):
        guard("http://127.0.0.1:8540", "alexandria")


def test_f1_guard_rejects_protected_databases_even_on_8532() -> None:
    """T2-F1-03: guard_alexandria_target rejects protected DBs even on :8532."""
    import igf.config.env_aliases as env_aliases

    guard = getattr(env_aliases, "guard_alexandria_target", None)
    assert callable(guard), "guard_alexandria_target missing from igf.config.env_aliases"
    for protected_db in ("infogeometry", "darwin_commits", "hive_live", "aiclaw_auto_rag"):
        with pytest.raises(ValueError):
            guard("http://127.0.0.1:8532", protected_db)


def test_f1_cli_rejects_8530_or_infogeometry_before_db_write(tmp_path: Path) -> None:
    """T2-F1-04: CLIs reject :8530 or protected DBs via guard before attempting HTTP writes/queries."""
    import igf.config.env_aliases as env_aliases

    guard = getattr(env_aliases, "guard_alexandria_target", None)
    assert callable(guard), "guard_alexandria_target missing from igf.config.env_aliases"
    # Verify guard is wired into CLIs BEFORE invoking them with live :8530
    ingest_src = ARANGO_INGEST_SCRIPT.read_text(encoding="utf-8")
    assert "guard_alexandria_target" in ingest_src, (
        "arango_ingest.py does not wire guard_alexandria_target yet; refusing unguarded :8530 invocation"
    )
    pdf_script = require_script(PDF_CORPUS_INGEST_SCRIPT)
    assert "guard_alexandria_target" in pdf_script.read_text(encoding="utf-8"), (
        "pdf_corpus_ingest.py does not wire guard_alexandria_target yet; refusing unguarded :8530 invocation"
    )
    retrieve_script = require_script(RETRIEVE_CONTEXT_SCRIPT)
    assert "guard_alexandria_target" in retrieve_script.read_text(encoding="utf-8"), (
        "retrieve_context.py does not wire guard_alexandria_target yet; refusing unguarded :8530 invocation"
    )
    rank_script = require_script(GRAPH_CONTEXT_RANK_SCRIPT)
    assert "guard_alexandria_target" in rank_script.read_text(encoding="utf-8"), (
        "graph_context_rank.py does not wire guard_alexandria_target yet; refusing unguarded :8530 invocation"
    )
    rag_script = require_script(GRAPH_RAG_QUERY_SCRIPT)
    assert "retrieve_arango_context" in rag_script.read_text(encoding="utf-8"), (
        "graph_rag_query.py does not wire retrieve_arango_context yet; refusing unguarded :8530 invocation"
    )
    ask_script = require_script(ASK_REPO_SCRIPT)
    assert "graph_rag_query.py" in ask_script.read_text(encoding="utf-8"), (
        "ask_repo.py does not delegate to graph_rag_query.py yet; refusing unguarded :8530 invocation"
    )

    proc1 = run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--endpoint", "http://127.0.0.1:8530",
            "--database", "infogeometry",
            "--search-view-only",
        ]
    )
    assert proc1.returncode != 0
    assert "8530" in (proc1.stderr + proc1.stdout) or "infogeometry" in (proc1.stderr + proc1.stdout).lower()

    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "x.pdf", topic="clifford")
    proc2 = run_cli(
        [
            str(pdf_script),
            "--input-dir", str(in_dir),
            "--output-dir", str(out_dir),
            "--ingest-arango",
            "--endpoint", "http://127.0.0.1:8530",
        ]
    )
    assert proc2.returncode != 0
    assert "8530" in (proc2.stderr + proc2.stdout)

    guarded_query_cases = [
        (retrieve_script, ["--arango", "--endpoint", "http://127.0.0.1:8530", "--database", "alexandria", "--query", "Clifford"], "8530"),
        (retrieve_script, ["--arango", "--endpoint", ALEXANDRIA_ENDPOINT, "--database", "infogeometry", "--query", "Clifford"], "infogeometry"),
        (rank_script, ["--arango", "--endpoint", "http://127.0.0.1:8530", "--database", "alexandria", "--query", "Clifford"], "8530"),
        (rank_script, ["--arango", "--endpoint", ALEXANDRIA_ENDPOINT, "--database", "infogeometry", "--query", "Clifford"], "infogeometry"),
        (rag_script, ["Clifford", "--scope", "alexandria", "--alexandria-endpoint", "http://127.0.0.1:8530", "--no-gravity"], "8530"),
        (rag_script, ["Clifford", "--scope", "alexandria", "--alexandria-endpoint", ALEXANDRIA_ENDPOINT, "--alexandria-database", "infogeometry", "--no-gravity"], "infogeometry"),
        (ask_script, ["Clifford", "--scope", "alexandria", "--alexandria-endpoint", "http://127.0.0.1:8530", "--no-gravity"], "8530"),
        (ask_script, ["Clifford", "--scope", "alexandria", "--alexandria-endpoint", ALEXANDRIA_ENDPOINT, "--alexandria-database", "infogeometry", "--no-gravity"], "infogeometry"),
    ]
    for script, args, expected_token in guarded_query_cases:
        proc = run_cli([str(script), *args])
        assert proc.returncode == 2, (
            f"Expected rc=2 guard rejection for {script.name} {args}, got {proc.returncode}; "
            f"stderr={proc.stderr!r} stdout={proc.stdout!r}"
        )
        assert "Traceback" not in proc.stderr, f"Unexpected traceback in {script.name}: {proc.stderr}"
        err_payload = json.loads(proc.stderr)
        err_msg = str(err_payload.get("error", ""))
        assert expected_token in err_msg.lower() or "8530" in err_msg or "infogeometry" in err_msg.lower(), (
            f"Expected {expected_token!r} in error JSON from {script.name}: {err_payload!r}"
        )


def test_f1_guard_handles_trailing_slash_localhost_and_uppercase_db() -> None:
    """T2-F1-05: guard_alexandria_target normalizes localhost, trailing slashes, and DB case."""
    import igf.config.env_aliases as env_aliases

    guard = getattr(env_aliases, "guard_alexandria_target", None)
    assert callable(guard), "guard_alexandria_target missing from igf.config.env_aliases"
    with pytest.raises(ValueError):
        guard("http://localhost:8530/", "ALEXANDRIA")
    with pytest.raises(ValueError):
        guard("http://127.0.0.1:8532/", "InfoGeometry")


def test_f1_unreachable_8532_port_fails_gracefully_with_nonzero_exit() -> None:
    """T2-F1-06: Unreachable ArangoDB endpoint exits non-zero cleanly without hanging."""
    proc = run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--endpoint", "http://127.0.0.1:59999",
            "--database", "alexandria_e2e_test_unreachable",
            "--search-view-only",
        ],
        timeout=15.0,
    )
    assert proc.returncode != 0


# ===========================================================================
# F2 — Corpus Inventory & Deduplication Boundaries (6 tests)
# ===========================================================================


def test_f2_nonexistent_input_dir_returns_nonzero_error(tmp_path: Path) -> None:
    """T2-F2-01: Missing --input-dir returns non-zero exit code with clear error message."""
    missing = tmp_path / "does_not_exist_xyz_123"
    out_dir = tmp_path / "out"
    proc = _run_pdf_ingest(missing, out_dir)
    assert proc.returncode != 0
    assert (proc.stderr + proc.stdout).strip()


def test_f2_empty_input_directory_produces_zero_counts(tmp_path: Path) -> None:
    """T2-F2-02: Empty existing --input-dir yields zero counts cleanly."""
    in_dir = tmp_path / "empty_in"
    in_dir.mkdir()
    out_dir = tmp_path / "out"
    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 0
    assert report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs") == 0
    assert read_jsonl(out_dir / "alexandria_documents.jsonl") == []


def test_f2_fake_pdf_extension_without_magic_header_rejected(tmp_path: Path) -> None:
    """T2-F2-03: Files ending in .pdf without %PDF- magic header are rejected and accounted."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    in_dir.mkdir()
    (in_dir / "fake.pdf").write_text("hello world not a pdf", encoding="utf-8")
    (in_dir / "image.pdf").write_bytes(b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 2
    assert read_jsonl(out_dir / "alexandria_documents.jsonl") == []


def test_f2_magic_pdf_without_pdf_extension_and_dotpdf_filename(tmp_path: Path) -> None:
    """T2-F2-04: Real %PDF- files named 'document', 'pdf', and '.pdf' do not crash and are accounted."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    in_dir.mkdir()
    p_doc = build_structured_math_pdf(in_dir / "tmp1.pdf", title="No Ext Doc", topic="clifford")
    p_pdf = build_structured_math_pdf(in_dir / "tmp2.pdf", title="Named pdf", topic="octonions")
    p_dot = build_structured_math_pdf(in_dir / "tmp3.pdf", title="Dot pdf", topic="peirce")
    (in_dir / "document").write_bytes(p_doc.read_bytes())
    (in_dir / "pdf").write_bytes(p_pdf.read_bytes())
    (in_dir / ".pdf").write_bytes(p_dot.read_bytes())
    p_doc.unlink()
    p_pdf.unlink()
    p_dot.unlink()

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 3
    assert report_metric(report, "uniquePdfCount", "unique_pdf_count", "unique_sha256_count", "uniquePdfs") == 3
    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 3


def test_f2_broken_symlinks_do_not_crash_directory_walk(tmp_path: Path) -> None:
    """T2-F2-05: Dangling symlinks inside input dir are skipped cleanly without crashing."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "good.pdf", topic="clifford")
    os.symlink("/nonexistent/missing_target.pdf", in_dir / "broken.pdf")
    os.symlink("/nonexistent/missing_lib.a", in_dir / "lib.a")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1


def test_f2_special_unicode_spaces_percent_encoded_filenames(tmp_path: Path) -> None:
    """T2-F2-06: Unicode accents, spaces, and percent-encoded filenames preserve path accurately."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    name1 = "Étienne Souriau (1).pdf"
    name2 = "0003-4916%2883%2990176-8.pdf"
    build_structured_math_pdf(in_dir / name1, title="Souriau Modes", topic="peirce")
    build_structured_math_pdf(in_dir / name2, title="Annals Physics", topic="clifford")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 2
    paths = " ".join(str(d.get("path", "")) for d in docs)
    assert name1 in paths and name2 in paths


# ===========================================================================
# F3 — Extraction & Normalization Failure Boundaries (6 tests)
# ===========================================================================


def test_f3_zero_byte_pdf_classified_empty_0_bytes(tmp_path: Path) -> None:
    """T2-F3-01: 0-byte PDF is accounted as empty_0_bytes with 0 chunks emitted."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_zero_byte_pdf(in_dir / "empty.pdf")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report["outcome_counts"]["empty_0_bytes"] == 1
    assert report["outcome_counts"]["ingested"] == 0
    assert len(report["unique_documents"]) == 1
    assert report["unique_documents"][0]["relativePath"] == "empty.pdf"
    assert report["unique_documents"][0]["outcome"] == "empty_0_bytes"
    assert report["unique_documents"][0]["sizeBytes"] == 0
    assert read_jsonl(out_dir / "alexandria_documents.jsonl") == []
    assert read_jsonl(out_dir / "alexandria_chunks.jsonl") == []


def test_f3_scanned_zero_text_pdf_classified_scanned_no_text(tmp_path: Path) -> None:
    """T2-F3-02: Image-only 0-text PDF is classified scanned_no_text with pageCount >= 1."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_scanned_zero_text_pdf(in_dir / "scanned.pdf", pages=2)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report["outcome_counts"]["scanned_no_text"] == 1
    assert report["outcome_counts"]["ingested"] == 0
    assert len(report["unique_documents"]) == 1
    rec = report["unique_documents"][0]
    assert rec["relativePath"] == "scanned.pdf"
    assert rec["outcome"] == "scanned_no_text"
    assert rec["pageCount"] >= 1
    assert rec["charCount"] == 0
    assert read_jsonl(out_dir / "alexandria_documents.jsonl") == []
    assert read_jsonl(out_dir / "alexandria_chunks.jsonl") == []


def test_f3_user_password_encrypted_pdf_classified_encrypted_no_text(tmp_path: Path) -> None:
    """T2-F3-03: User-password-locked PDF fails gracefully as encrypted_no_text without hanging."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_user_locked_encrypted_pdf(in_dir / "locked.pdf")

    proc = _run_pdf_ingest(in_dir, out_dir, timeout=30.0)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report["outcome_counts"]["encrypted_no_text"] == 1
    assert report["outcome_counts"]["ingested"] == 0
    assert len(report["unique_documents"]) == 1
    rec = report["unique_documents"][0]
    assert rec["relativePath"] == "locked.pdf"
    assert rec["outcome"] == "encrypted_no_text"
    assert rec["charCount"] == 0
    assert read_jsonl(out_dir / "alexandria_documents.jsonl") == []
    assert read_jsonl(out_dir / "alexandria_chunks.jsonl") == []


def test_f3_very_low_text_pdf_classified_very_low_text_skipped(tmp_path: Path) -> None:
    """T2-F3-04: PDF with only ~15 characters is classified very_low_text_skipped."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_text_pdf(in_dir / "tiny.pdf", [["Title Page 1"]], title="Tiny")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report["outcome_counts"]["very_low_text_skipped"] == 1
    assert report["outcome_counts"]["ingested"] == 0
    assert len(report["unique_documents"]) == 1
    rec = report["unique_documents"][0]
    assert rec["relativePath"] == "tiny.pdf"
    assert rec["outcome"] == "very_low_text_skipped"
    assert 0 < rec["charCount"] < 100
    assert read_jsonl(out_dir / "alexandria_documents.jsonl") == []
    assert read_jsonl(out_dir / "alexandria_chunks.jsonl") == []


def test_f3_corrupt_truncated_pdf_classified_parse_error(tmp_path: Path) -> None:
    """T2-F3-05: Truncated corrupt %PDF-1.4 file records parse_error while valid PDFs succeed."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_corrupt_pdf(in_dir / "corrupt.pdf")
    build_structured_math_pdf(in_dir / "valid_after.pdf", topic="clifford")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report["outcome_counts"]["parse_error"] == 1
    assert report["outcome_counts"]["ingested"] == 1
    by_rel = {r["relativePath"]: r for r in report["unique_documents"]}
    assert set(by_rel.keys()) == {"corrupt.pdf", "valid_after.pdf"}
    assert by_rel["corrupt.pdf"]["outcome"] == "parse_error"
    assert by_rel["valid_after.pdf"]["outcome"] == "ingested"
    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 1
    assert "valid_after.pdf" in docs[0]["path"]
    assert len(read_jsonl(out_dir / "alexandria_chunks.jsonl")) >= 1


def test_f3_high_pua_encoding_noise_flagged_in_warnings(tmp_path: Path) -> None:
    """T2-F3-06: High PUA/replacement-char encoding noise computes encodingNoiseRatio > 0 and warns."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_pua_noise_pdf(in_dir / "noisy.pdf")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report["outcome_counts"]["ingested"] == 1
    assert len(report["unique_documents"]) == 1
    rec = report["unique_documents"][0]
    assert rec["outcome"] == "ingested"
    assert "encoding_noise" in rec.get("warnings", [])
    assert rec.get("encodingNoiseRatio", 0.0) > 0.0

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    assert len(docs) == 1
    assert "encoding_noise" in docs[0].get("warnings", [])
    assert docs[0].get("encodingNoiseRatio", 0.0) > 0.0
    assert any(c.get("provenance", {}).get("encodingNoiseRatio", 0.0) > 0.0 for c in chunks)


# ===========================================================================
# F4 — Archetypal & DAG Extraction Boundaries (5 tests)
# ===========================================================================


def test_f4_unstructured_prose_only_pdf_falls_back_gracefully(tmp_path: Path) -> None:
    """T2-F4-01: Prose-only PDF with zero math headings falls back to prose chunks cleanly."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_text_pdf(
        in_dir / "prose.pdf",
        [[
            "This narrative discusses geometric intuition in classical mechanics over smooth manifolds.",
            "Every tangent bundle carries natural vertical and horizontal distributions along trajectories.",
            "No formal headings, equations, or bibliographic references appear in this essay.",
        ]],
        title="Prose Essay",
    )

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    dag_edges = read_jsonl(out_dir / "alexandria_dag_edges.jsonl")
    assert len(docs) == 1
    assert len(chunks) >= 1
    assert any(c.get("chunkKind") == "prose" for c in chunks)
    assert isinstance(dag_edges, list) and all(
        "_from" in e and "_to" in e and "edgeType" in e for e in dag_edges
    )


def test_f4_mutual_references_do_not_introduce_dag_cycles(tmp_path: Path) -> None:
    """T2-F4-02: Mutual cross-references between Theorem 1 and Lemma 2 never create DAG cycles."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "cycle.pdf", title="Mutual Refs", mutual_cycle=True)

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    dag_edges = read_jsonl(out_dir / "alexandria_dag_edges.jsonl")
    _assert_dag_acyclic(dag_edges)


def test_f4_unicode_math_symbols_and_combining_accents_preserved(tmp_path: Path) -> None:
    """T2-F4-03: Unicode math symbols and accented author names round-trip without Mojibake."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_text_pdf(
        in_dir / "unicode.pdf",
        [[
            "1. Stochastic Analysis of Rémi Léandre",
            "Theorem 1.1: Evaluate ∇ × B and inner product ⟨ψ|φ⟩ on ℝ^{n} and ℂ over ℓ².",
            "Proof. Direct integration preserves the symplectic two-form on ℝ^{n}. QED.",
        ]],
        title="Unicode Math",
    )

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    combined = "\n".join(
        [s.get("title", "") for s in read_jsonl(out_dir / "alexandria_sections.jsonl")]
        + [f"{c.get('title', '')}\n{c.get('text', '')}" for c in read_jsonl(out_dir / "alexandria_chunks.jsonl")]
    )
    for token in ("Rémi Léandre", "∇", "⟨ψ|φ⟩", "ℂ"):
        assert token in combined, f"Lost Unicode token {token!r} in extracted JSONL"


def test_f4_enrich_ollama_unreachable_falls_back_to_deterministic(tmp_path: Path) -> None:
    """T2-F4-04: --enrich-ollama with unreachable endpoint falls back cleanly to deterministic mode."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "ollama.pdf", topic="clifford")

    proc = _run_pdf_ingest(
        in_dir,
        out_dir,
        extra_args=["--enrich-ollama", "--ollama-endpoint", "http://127.0.0.1:59998"],
        env_overrides={"OLLAMA_HOST": "http://127.0.0.1:59998"},
        timeout=30.0,
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    assert chunks
    for ch in chunks:
        mode = str(ch.get("semantic", {}).get("semantic_mode", "")).lower()
        assert mode, "semantic_mode must be populated on fallback"
        assert "ollama" not in mode or "fallback" in mode or "deterministic" in mode


def test_f4_huge_single_theorem_exceeding_chunk_limit_handled_safely(tmp_path: Path) -> None:
    """T2-F4-05: 25,000-char theorem block is handled without crash and preserves adjacency."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "huge.pdf", title="Huge Theorem", extra_body_chars=25000)

    proc = _run_pdf_ingest(in_dir, out_dir, timeout=60.0)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    adj_edges = read_jsonl(out_dir / "alexandria_chunk_adjacent_edges.jsonl")
    assert len(chunks) > 1
    assert any(c.get("chunkKind") in {"theorem", "definition", "prose"} for c in chunks)
    assert max(len(c.get("text", "")) for c in chunks) <= 3200
    assert len(adj_edges) == len(chunks) - 1
    assert len(adj_edges) >= 1
    chunk_ids = {f"alexandria_chunks/{c['_key']}" for c in chunks}
    assert all(
        e.get("kind") == "adjacent"
        and e.get("_from") in chunk_ids
        and e.get("_to") in chunk_ids
        and e.get("_from") != e.get("_to")
        for e in adj_edges
    )


# ===========================================================================
# F5 — ArangoDB Storage & View Boundaries (5 tests)
# ===========================================================================


def test_f5_missing_input_dir_without_search_view_only_errors() -> None:
    """T2-F5-01: arango_ingest.py without --input-dir and without --search-view-only exits 2."""
    proc = run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--endpoint", ALEXANDRIA_ENDPOINT,
            "--database", "alexandria_e2e_test_argparse",
        ]
    )
    assert proc.returncode == 2


def test_f5_empty_jsonl_artifacts_ingest_without_error(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T2-F5-02: Empty 0-byte JSONL files ingest cleanly, ensuring collections and search view."""
    empty_dir = tmp_path / "empty_jsonl"
    empty_dir.mkdir()
    for name in (
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
        (empty_dir / f"{name}.jsonl").write_text("", encoding="utf-8")

    proc = run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--input-dir", str(empty_dir),
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--username", isolated_alexandria_db["username"],
            "--password", isolated_alexandria_db["password"],
        ]
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    assert arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_documents",
    ) == 0


def test_f5_replace_documents_purges_shrunk_document_stale_chunks_and_dag_edges(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T2-F5-03: --replace-documents removes stale chunks and alexandria_dag_edges when doc shrinks."""
    in_dir = tmp_path / "in"
    out_v1 = tmp_path / "v1"
    build_structured_math_pdf(in_dir / "evolving.pdf", title="Evolving Paper", topic="clifford", pages=3)
    assert _run_pdf_ingest(in_dir, out_v1).returncode == 0

    ingest_base = [
        str(ARANGO_INGEST_SCRIPT),
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
        "--username", isolated_alexandria_db["username"],
        "--password", isolated_alexandria_db["password"],
    ]
    assert run_cli([*ingest_base, "--input-dir", str(out_v1)]).returncode == 0

    doc_key = read_jsonl(out_v1 / "alexandria_documents.jsonl")[0]["_key"]
    sec_key = read_jsonl(out_v1 / "alexandria_sections.jsonl")[0]["_key"]

    # Build shrunk v2 JSONL with same documentKey, only 2 chunks and 0 DAG edges
    out_v2 = tmp_path / "v2"
    out_v2.mkdir()
    doc_v2 = dict(read_jsonl(out_v1 / "alexandria_documents.jsonl")[0])
    doc_v2["contentHash"] = "b" * 64
    sec_v2 = {"_key": sec_key, "documentKey": doc_key, "title": "Shrunk Section", "level": 1, "ordinal": 1}
    chunks_v2 = [
        {
            "_key": f"{doc_key}_c1",
            "documentKey": doc_key,
            "sectionKey": sec_key,
            "ordinal": 1,
            "chunkKind": "prose",
            "title": "Shrunk Section",
            "text": "Shrunk replacement chunk one.",
            "tokens": ["shrunk", "replacement", "chunk", "one"],
            "sourceAuthority": "retrieval_context_only",
            "provenance": {"path": doc_v2["path"], "contentHash": doc_v2["contentHash"], "sourceFormat": "pdf", "pageStart": 1, "pageEnd": 1},
        },
        {
            "_key": f"{doc_key}_c2",
            "documentKey": doc_key,
            "sectionKey": sec_key,
            "ordinal": 2,
            "chunkKind": "prose",
            "title": "Shrunk Section",
            "text": "Shrunk replacement chunk two.",
            "tokens": ["shrunk", "replacement", "chunk", "two"],
            "sourceAuthority": "retrieval_context_only",
            "provenance": {"path": doc_v2["path"], "contentHash": doc_v2["contentHash"], "sourceFormat": "pdf", "pageStart": 1, "pageEnd": 1},
        },
    ]
    (out_v2 / "alexandria_documents.jsonl").write_text(json.dumps(doc_v2) + "\n", encoding="utf-8")
    (out_v2 / "alexandria_sections.jsonl").write_text(json.dumps(sec_v2) + "\n", encoding="utf-8")
    (out_v2 / "alexandria_chunks.jsonl").write_text(
        "".join(json.dumps(c) + "\n" for c in chunks_v2), encoding="utf-8"
    )
    for empty_name in (
        "alexandria_entities",
        "alexandria_document_section_edges",
        "alexandria_section_chunk_edges",
        "alexandria_chunk_adjacent_edges",
        "alexandria_chunk_entity_edges",
        "alexandria_entity_relation_edges",
        "alexandria_dag_edges",
    ):
        (out_v2 / f"{empty_name}.jsonl").write_text("", encoding="utf-8")

    proc2 = run_cli([*ingest_base, "--input-dir", str(out_v2), "--replace-documents"])
    assert proc2.returncode == 0, f"stderr={proc2.stderr}"

    chunks_in_db = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR c IN alexandria_chunks FILTER c.documentKey == @dk RETURN c._key",
        {"dk": doc_key},
    )
    dag_in_db = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "FOR e IN alexandria_dag_edges FILTER e.documentKey == @dk RETURN e._key",
        {"dk": doc_key},
    )
    assert len(chunks_in_db) == 2
    assert len(dag_in_db) == 0


def test_f5_skip_unchanged_only_imports_newly_added_or_modified_docs(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T2-F5-04: --skip-unchanged skips existing doc A and imports newly added doc B."""
    in_dir = tmp_path / "in"
    out_1 = tmp_path / "out1"
    out_2 = tmp_path / "out2"
    build_structured_math_pdf(in_dir / "docA.pdf", title="Doc A", topic="clifford")
    assert _run_pdf_ingest(in_dir, out_1).returncode == 0

    ingest_base = [
        str(ARANGO_INGEST_SCRIPT),
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
        "--username", isolated_alexandria_db["username"],
        "--password", isolated_alexandria_db["password"],
    ]
    assert run_cli([*ingest_base, "--input-dir", str(out_1)]).returncode == 0

    build_structured_math_pdf(in_dir / "docB.pdf", title="Doc B", topic="octonions")
    assert _run_pdf_ingest(in_dir, out_2).returncode == 0
    proc2 = run_cli([*ingest_base, "--input-dir", str(out_2), "--skip-unchanged"])
    assert proc2.returncode == 0, f"stderr={proc2.stderr}"
    summary = json.loads(proc2.stdout)
    assert summary["skippedUnchanged"] == 1
    assert summary["imported"]["alexandria_documents"] == 1
    assert arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_documents",
    ) == 2


def test_f5_invalid_json_line_in_jsonl_fails_explicitly(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T2-F5-05: Corrupt JSON line in alexandria_chunks.jsonl causes explicit non-zero failure."""
    bad_dir = tmp_path / "bad_jsonl"
    bad_dir.mkdir()
    (bad_dir / "alexandria_documents.jsonl").write_text('{"_key": "doc_1", "contentHash": "a"}\n', encoding="utf-8")
    (bad_dir / "alexandria_chunks.jsonl").write_text("{not_json\n", encoding="utf-8")

    proc = run_cli(
        [
            str(ARANGO_INGEST_SCRIPT),
            "--input-dir", str(bad_dir),
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--username", isolated_alexandria_db["username"],
            "--password", isolated_alexandria_db["password"],
        ]
    )
    assert proc.returncode != 0


# ===========================================================================
# F6 — Corpus Batch & Integrity Boundaries (5 tests)
# ===========================================================================


def test_f6_mixed_failure_batch_continues_and_accounts_100_percent(tmp_path: Path) -> None:
    """T2-F6-01: 7-file mixed failure corpus extracts 2 valid PDFs and accounts for all 7."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    v1 = build_structured_math_pdf(in_dir / "valid1.pdf", title="Valid One", topic="clifford")
    build_structured_math_pdf(in_dir / "valid2.pdf", title="Valid Two", topic="octonions")
    (in_dir / "valid1_copy.pdf").write_bytes(v1.read_bytes())
    build_zero_byte_pdf(in_dir / "empty.pdf")
    build_corrupt_pdf(in_dir / "corrupt.pdf")
    build_scanned_zero_text_pdf(in_dir / "scan.pdf", pages=1)
    build_png_file(in_dir / "pic.png")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    report = read_inventory_report(out_dir)
    assert report_metric(report, "totalFilesScanned", "total_files_scanned", "total_scanned_files", "totalFiles") == 7
    docs = read_jsonl(out_dir / "alexandria_documents.jsonl")
    assert len(docs) == 2


def test_f6_limit_zero_or_negative_handled_deterministically(tmp_path: Path) -> None:
    """T2-F6-02: --limit 0 processes all PDFs (0 = all), --limit 1 caps at 1, and --limit -1 exits non-zero."""
    in_dir = tmp_path / "in"
    out_0 = tmp_path / "out0"
    out_1 = tmp_path / "out1"
    out_neg = tmp_path / "out_neg"
    build_structured_math_pdf(in_dir / "a.pdf", topic="clifford")
    build_structured_math_pdf(in_dir / "b.pdf", topic="octonions")

    proc0 = _run_pdf_ingest(in_dir, out_0, extra_args=["--limit", "0"])
    assert proc0.returncode == 0, f"--limit 0 (all) failed: stderr={proc0.stderr}"
    assert len(read_jsonl(out_0 / "alexandria_documents.jsonl")) == 2

    proc1 = _run_pdf_ingest(in_dir, out_1, extra_args=["--limit", "1"])
    assert proc1.returncode == 0, f"--limit 1 failed: stderr={proc1.stderr}"
    assert len(read_jsonl(out_1 / "alexandria_documents.jsonl")) == 1

    proc_neg = _run_pdf_ingest(in_dir, out_neg, extra_args=["--limit", "-1"])
    assert proc_neg.returncode != 0
    assert (proc_neg.stderr + proc_neg.stdout).strip()


def test_f6_parallel_workers_gt_1_produces_identical_deterministic_output(tmp_path: Path) -> None:
    """T2-F6-03: --workers 1 and --workers 4 yield identical _key sets and inventory counts."""
    in_dir = tmp_path / "in"
    out_w1 = tmp_path / "out_w1"
    out_w4 = tmp_path / "out_w4"
    for i, topic in enumerate(("clifford", "octonions", "peirce", "spectral")):
        build_structured_math_pdf(in_dir / f"p_{i}.pdf", title=f"Paper {i}", topic=topic)

    assert _run_pdf_ingest(in_dir, out_w1, extra_args=["--workers", "1"]).returncode == 0
    assert _run_pdf_ingest(in_dir, out_w4, extra_args=["--workers", "4"]).returncode == 0

    for fname in (
        "alexandria_documents.jsonl",
        "alexandria_sections.jsonl",
        "alexandria_chunks.jsonl",
        "alexandria_dag_edges.jsonl",
    ):
        s1 = sorted(r["_key"] for r in read_jsonl(out_w1 / fname))
        s4 = sorted(r["_key"] for r in read_jsonl(out_w4 / fname))
        assert s1 == s4, f"Worker race/non-determinism detected in {fname}"


def test_f6_reingestion_of_same_corpus_produces_zero_count_drift(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T2-F6-04: Re-running full pipeline with --ingest-arango --skip-unchanged causes zero count drift."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "p1.pdf", topic="clifford")
    build_structured_math_pdf(in_dir / "p2.pdf", topic="peirce")

    args = [
        "--ingest-arango",
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
        "--skip-unchanged",
    ]
    env = {
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    assert _run_pdf_ingest(in_dir, out_dir, extra_args=args, env_overrides=env).returncode == 0

    cols = ("alexandria_documents", "alexandria_sections", "alexandria_chunks", "alexandria_entities", "alexandria_dag_edges")
    counts_before = {
        c: arango_collection_count(
            isolated_alexandria_db["endpoint"],
            isolated_alexandria_db["database"],
            isolated_alexandria_db["username"],
            isolated_alexandria_db["password"],
            c,
        )
        for c in cols
    }
    assert _run_pdf_ingest(in_dir, out_dir, extra_args=args, env_overrides=env).returncode == 0
    counts_after = {
        c: arango_collection_count(
            isolated_alexandria_db["endpoint"],
            isolated_alexandria_db["database"],
            isolated_alexandria_db["username"],
            isolated_alexandria_db["password"],
            c,
        )
        for c in cols
    }
    assert counts_after == counts_before


def test_f6_output_dir_nested_nonexistent_parent_auto_created(tmp_path: Path) -> None:
    """T2-F6-05: Deep nested non-existent --output-dir is created automatically."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "nested" / "deep" / "out"
    build_structured_math_pdf(in_dir / "one.pdf", topic="clifford")

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    assert (out_dir / "corpus_inventory_report.json").exists()
    assert (out_dir / "alexandria_documents.jsonl").exists()


# ===========================================================================
# F7 — Retrieval & Query Boundaries (5 tests)
# ===========================================================================


def test_f7_empty_and_whitespace_query_returns_empty_hits_or_clean_error(tmp_path: Path) -> None:
    """T2-F7-01: Empty and whitespace queries exit 0 with empty hits and retrieval_context_only authority."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "q.pdf", topic="clifford")
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    for script in (RETRIEVE_CONTEXT_SCRIPT, GRAPH_CONTEXT_RANK_SCRIPT):
        for q in ("", "   "):
            proc = run_cli([str(script), "--input-dir", str(out_dir), "--query", q])
            assert "Traceback" not in proc.stderr, f"Unhandled traceback on {script.name} q={q!r}: {proc.stderr}"
            assert proc.returncode == 0, (
                f"Expected clean rc=0 on {script.name} q={q!r}, got {proc.returncode}; "
                f"stderr={proc.stderr!r} stdout={proc.stdout!r}"
            )
            payload = json.loads(proc.stdout)
            assert payload.get("hits") == []
            assert_retrieval_authority(payload)


def test_f7_zero_match_query_returns_empty_hits_with_authority_label(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T2-F7-02: Zero-match query returns empty hits and preserves retrieval_context_only authority."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "q.pdf", topic="clifford")
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

    for extra, env in (
        (["--input-dir", str(out_dir)], None),
        (
            ["--arango", "--endpoint", isolated_alexandria_db["endpoint"], "--database", isolated_alexandria_db["database"]],
            {"ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"], "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"]},
        ),
    ):
        proc = run_cli([str(RETRIEVE_CONTEXT_SCRIPT), *extra, "--query", "xqzv99nonexistenttoken77"], env_overrides=env)
        assert proc.returncode == 0, f"stderr={proc.stderr}"
        payload = json.loads(proc.stdout)
        assert payload["hits"] == []
        assert payload.get("authority") == "retrieval_context_only"


def test_f7_top_k_zero_and_large_top_k_bounds(tmp_path: Path) -> None:
    """T2-F7-03: --top-k 0 returns 0 hits, --top-k 10000 returns bounded non-empty hits, and --top-k -1 exits 2."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "q.pdf", topic="clifford")
    assert _run_pdf_ingest(in_dir, out_dir).returncode == 0

    proc0 = run_cli([str(RETRIEVE_CONTEXT_SCRIPT), "--input-dir", str(out_dir), "--query", "Clifford", "--top-k", "0"])
    assert proc0.returncode == 0, f"stderr={proc0.stderr}"
    payload0 = json.loads(proc0.stdout)
    assert payload0["hits"] == []
    assert_retrieval_authority(payload0)

    total_chunks = len(read_jsonl(out_dir / "alexandria_chunks.jsonl"))
    assert total_chunks >= 1
    proc_big = run_cli([str(RETRIEVE_CONTEXT_SCRIPT), "--input-dir", str(out_dir), "--query", "Clifford", "--top-k", "10000"])
    assert proc_big.returncode == 0, f"stderr={proc_big.stderr}"
    big_payload = json.loads(proc_big.stdout)
    assert_retrieval_authority(big_payload)
    assert 1 <= len(big_payload["hits"]) <= total_chunks

    proc_neg = run_cli([str(RETRIEVE_CONTEXT_SCRIPT), "--input-dir", str(out_dir), "--query", "Clifford", "--top-k", "-1"])
    assert proc_neg.returncode == 2, f"Expected rc=2 for --top-k -1, got {proc_neg.returncode}; stderr={proc_neg.stderr!r}"
    assert "Traceback" not in proc_neg.stderr
    assert (proc_neg.stderr + proc_neg.stdout).strip()


def test_f7_special_chars_unicode_and_aql_injection_safe_in_query(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T2-F7-04: AQL injection string and Unicode punctuation never mutate DB or crash retrieval."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_structured_math_pdf(in_dir / "q.pdf", topic="clifford")
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

    before_chunks = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_chunks",
    )
    evil_query = 'Dirac–Hestenes Cl(1,1) "; REMOVE c IN alexandria_chunks //'

    for extra, env in (
        (["--input-dir", str(out_dir)], None),
        (
            ["--arango", "--endpoint", isolated_alexandria_db["endpoint"], "--database", isolated_alexandria_db["database"]],
            {"ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"], "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"]},
        ),
    ):
        proc = run_cli([str(RETRIEVE_CONTEXT_SCRIPT), *extra, "--query", evil_query], env_overrides=env)
        assert proc.returncode == 0, f"stderr={proc.stderr}"
        json.loads(proc.stdout)

    after_chunks = arango_collection_count(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "alexandria_chunks",
    )
    assert after_chunks == before_chunks


def test_f7_retrieve_context_missing_input_dir_or_unreachable_arango_errors_cleanly(tmp_path: Path) -> None:
    """T2-F7-05: Missing --input-dir, unreachable --arango, and invalid/empty --scope fail cleanly."""
    missing_dir = str(tmp_path / "missing")
    for script in (RETRIEVE_CONTEXT_SCRIPT, GRAPH_CONTEXT_RANK_SCRIPT):
        proc = run_cli([str(script), "--input-dir", missing_dir, "--query", "Clifford"])
        assert proc.returncode != 0, f"Expected non-zero exit for missing --input-dir on {script.name}"
        assert "Traceback" not in proc.stderr, f"Unexpected traceback in {script.name}: {proc.stderr}"
        err_payload = json.loads(proc.stderr)
        assert str(err_payload.get("error", "")).strip(), f"Expected non-empty error on {script.name}: {err_payload!r}"

    unreachable_cases = [
        (RETRIEVE_CONTEXT_SCRIPT, ["--arango", "--endpoint", "http://127.0.0.1:59999", "--database", "alexandria_e2e_test_missing", "--query", "Clifford"]),
        (GRAPH_CONTEXT_RANK_SCRIPT, ["--arango", "--endpoint", "http://127.0.0.1:59999", "--database", "alexandria_e2e_test_missing", "--query", "Clifford"]),
        (GRAPH_RAG_QUERY_SCRIPT, ["Clifford", "--scope", "alexandria", "--alexandria-endpoint", "http://127.0.0.1:59999", "--no-gravity"]),
        (ASK_REPO_SCRIPT, ["Clifford", "--scope", "alexandria", "--alexandria-endpoint", "http://127.0.0.1:59999", "--no-gravity"]),
    ]
    for script, args in unreachable_cases:
        proc = run_cli([str(script), *args], timeout=15.0)
        assert proc.returncode != 0, f"Expected non-zero exit for unreachable :59999 on {script.name}"
        assert "Traceback" not in proc.stderr, f"Unexpected traceback in {script.name}: {proc.stderr}"
        err_payload = json.loads(proc.stderr)
        assert str(err_payload.get("error", "")).strip(), f"Expected non-empty error on {script.name}: {err_payload!r}"

    for script in (GRAPH_RAG_QUERY_SCRIPT, ASK_REPO_SCRIPT):
        proc_bogus = run_cli([str(script), "Clifford", "--scope", "bogus_scope"])
        assert proc_bogus.returncode == 2, (
            f"Expected rc=2 for --scope bogus_scope on {script.name}, got {proc_bogus.returncode}; "
            f"stderr={proc_bogus.stderr!r}"
        )
        assert "Traceback" not in proc_bogus.stderr
        assert "invalid scope(s): bogus_scope" in proc_bogus.stderr, (
            f"Expected invalid scope error on {script.name}: {proc_bogus.stderr!r}"
        )

        proc_empty = run_cli([str(script), "Clifford", "--scope", ""])
        assert proc_empty.returncode == 2, (
            f"Expected rc=2 for --scope '' on {script.name}, got {proc_empty.returncode}; "
            f"stderr={proc_empty.stderr!r}"
        )
        assert "Traceback" not in proc_empty.stderr
        assert "scope must not be empty" in proc_empty.stderr, (
            f"Expected empty scope error on {script.name}: {proc_empty.stderr!r}"
        )
