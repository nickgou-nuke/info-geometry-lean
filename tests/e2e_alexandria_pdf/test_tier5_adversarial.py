"""Tier 5: White-box adversarial coverage hardening tests (T5-01..T5-07 for BUG-01..BUG-11)."""
from __future__ import annotations

import json
import os
import stat
import uuid
from pathlib import Path
from typing import Any
from urllib.parse import quote

import pytest

from tests.e2e_alexandria_pdf.conftest import (
    ALEXANDRIA_ENDPOINT,
    ARANGO_INGEST_SCRIPT,
    GRAPH_CONTEXT_RANK_SCRIPT,
    PDF_CORPUS_INGEST_SCRIPT,
    REPO_ROOT,
    RETRIEVE_CONTEXT_SCRIPT,
    arango_aql,
    arango_http_json,
    arango_list_databases,
    assert_retrieval_authority,
    assert_safe_test_target,
    build_text_pdf,
    build_zero_byte_pdf,
    read_inventory_report,
    read_jsonl,
    require_alexandria_8532,
    require_script,
    run_cli,
)
from tools.alexandria import pdf_corpus_ingest, retrieve_context

RESEARCH_DIGEST_WORKER_SCRIPT = REPO_ROOT / "tools" / "infra" / "research_digest_worker.py"

pytestmark = pytest.mark.tier5


def _run_pdf_ingest(in_dir: Path, out_dir: Path, extra_args: list[str] | None = None, **kwargs: Any) -> Any:
    script = require_script(PDF_CORPUS_INGEST_SCRIPT)
    cmd = [str(script), "--input-dir", str(in_dir), "--output-dir", str(out_dir)]
    if extra_args:
        cmd.extend(extra_args)
    return run_cli(cmd, **kwargs)


def test_t5_01_graph_context_rank_200_cap_saturation_no_keyerror(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T5-01 (BUG-01): --seed-k 60 --hops 2 with >200 chunks and non-seed neighbors saturates cap without KeyError."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"

    # Create 7 PDFs x 10 items (Definition, Lemma, Theorem, Proof, Equation) = 350 chunks total.
    # Only Theorem chunks (70 total) contain "xqzvcap77"; Definition, Lemma, Proof, and Equation
    # neighbors do NOT contain "xqzvcap77", so --seed-k 60 --hops 2 pulls 60 seeds and saturates
    # the 200-node cap with non-seed neighbors. A naive single-pass loop fills the cap before all
    # 60 seeds are visited and raises KeyError.
    for doc_idx in range(7):
        pages: list[list[str]] = []
        for item_idx in range(1, 11):
            tag = f"{doc_idx + 1}.{item_idx}"
            pages.append(
                [
                    f"{tag} Spectral Block {tag}",
                    f"Definition {tag} (Krein Module {tag}): Auxiliary normed space without seed token.",
                    f"Lemma {tag}: Bounded projector identity following Definition {tag}.",
                    (
                        f"Theorem {tag} (Main Result {tag}): Every xqzvcap77 operator in "
                        f"Definition {tag} and Lemma {tag} splits orthogonally."
                    ),
                    f"Proof of Theorem {tag}. Apply Lemma {tag} and Definition {tag} directly. QED.",
                    f"P_{tag} = Q_{tag} + R_{tag} ({tag})",
                ]
            )
        build_text_pdf(in_dir / f"cap_doc_{doc_idx}.pdf", pages, title=f"Theorem Saturation Paper {doc_idx}")

    env = {
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    ingest_proc = _run_pdf_ingest(
        in_dir,
        out_dir,
        extra_args=[
            "--ingest-arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--max-chunk-chars", "600",
        ],
        env_overrides=env,
    )
    assert ingest_proc.returncode == 0, f"stderr={ingest_proc.stderr}"

    total_chunks = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        "RETURN LENGTH(alexandria_chunks)",
    )[0]
    assert total_chunks > 200, f"Expected >200 chunks for cap saturation, got {total_chunks}"

    rank_proc = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "xqzvcap77",
            "--seed-k", "60",
            "--top-k", "15",
            "--hops", "2",
        ],
        env_overrides=env,
    )
    assert rank_proc.returncode == 0, f"stderr={rank_proc.stderr}\nstdout={rank_proc.stdout}"
    assert "KeyError" not in rank_proc.stderr
    packet = json.loads(rank_proc.stdout)
    assert_retrieval_authority(packet)
    assert len(packet["hits"]) > 0
    assert len(packet["seeds"]) == 60
    assert packet["graph"]["nodeCount"] == 200


def test_t5_02_nonseed_ppr_dag_neighbors_and_seed_k_zero_parity(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T5-02 (BUG-02, BUG-03, BUG-12, BUG-14, BUG-15): Non-seed PPR dagNeighbors, no bogus 2-hop bib edges, hops=2 direction parity, seed_k=0 & top_k<0 parity."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_text_pdf(
        in_dir / "ppr_dag.pdf",
        [[
            "1. General Analysis",
            "Theorem 1.1 (XQZVPEIRCE77 Decomposition): Every xqzvpeirce77 operator splits orthogonally.",
            "Proof of Theorem 1.1. By modular involution and idempotent projection, the result holds. QED.",
        ]],
        title="General Analysis",
    )
    build_text_pdf(
        in_dir / "shared_bib.pdf",
        [[
            "1. Introduction",
            "Theorem 1.1 (XQZVSHAREDBIB88 Decomposition): Every xqzvsharedbib88 operator cites [1].",
            "2. Later Section",
            "Lemma 2.1: An auxiliary orthogonal complement also cites [1].",
            "References",
            "[1] A. Reference, Shared Bibliography Entry, 2024.",
        ]],
        title="Shared Bibliography Paper",
    )
    build_text_pdf(
        in_dir / "chain_and_bib.pdf",
        [[
            "1. Preliminaries",
            "Definition 1.1 (XQZVDEF11 Chain): Base algebraic space.",
            "2. Main Result",
            "Theorem 2.1 (XQZVTHM21 Chain): By Definition 1.1 and [1], the chain holds.",
            "Proof of Theorem 2.1. Applying xqzvhop2dir99 directly finishes the proof. QED.",
            "3. Auxiliary Corollary",
            "Lemma 3.1 (XQZVLEM31 Chain): Also cites [1] independently with xqzvlemma31hop2.",
            "References",
            "[1] A. Chain, Shared Reference Entry, 2025.",
        ]],
        title="Two Hop Chain Paper",
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

    r_jsonl = run_cli(
        [str(GRAPH_CONTEXT_RANK_SCRIPT), "--input-dir", str(out_dir), "--query", "xqzvpeirce77", "--top-k", "5"]
    )
    r_arango = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "xqzvpeirce77",
            "--top-k", "5",
        ],
        env_overrides=env,
    )
    assert r_jsonl.returncode == 0, f"stderr={r_jsonl.stderr}"
    assert r_arango.returncode == 0, f"stderr={r_arango.stderr}"
    pkt_j = json.loads(r_jsonl.stdout)
    pkt_a = json.loads(r_arango.stdout)
    assert_retrieval_authority(pkt_j)
    assert_retrieval_authority(pkt_a)

    # Proof chunk has zero lexical overlap with xqzvpeirce77, so only Theorem 1.1 is a seed
    assert len(pkt_a["seeds"]) == 1
    assert len(pkt_a["hits"]) == 2
    proof_hit_a = next((h for h in pkt_a["hits"] if h.get("chunkKind") == "proof"), None)
    assert proof_hit_a is not None, f"Expected PPR-promoted proof hit in arango mode: {pkt_a['hits']!r}"
    assert proof_hit_a["dagNeighbors"], f"Expected non-empty dagNeighbors on PPR-promoted proof hit: {proof_hit_a!r}"
    assert any(
        n.get("edgeType") == "proof_proves_theorem" and n.get("direction") == "outbound"
        for n in proof_hit_a["dagNeighbors"]
    ), f"Expected outbound proof_proves_theorem neighbor on proof hit: {proof_hit_a['dagNeighbors']!r}"

    # BUG-12: hops=2 entity-mediated path (Theorem 1.1 -> [1] <- Lemma 2.1) must NOT fabricate chunk-to-chunk chunk_cites_entry
    r_shared = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "xqzvsharedbib88",
            "--top-k", "10",
            "--seed-k", "5",
            "--hops", "2",
        ],
        env_overrides=env,
    )
    assert r_shared.returncode == 0, f"stderr={r_shared.stderr}"
    pkt_shared = json.loads(r_shared.stdout)
    assert_retrieval_authority(pkt_shared)
    assert len(pkt_shared["seeds"]) == 1
    thm_shared = next((h for h in pkt_shared["hits"] if "Theorem 1.1" in str(h.get("title", ""))), None)
    lem_shared = next((h for h in pkt_shared["hits"] if "Lemma 2.1" in str(h.get("title", ""))), None)
    assert thm_shared is not None and lem_shared is not None, f"Expected both Theorem 1.1 and Lemma 2.1 hits: {pkt_shared['hits']!r}"
    assert any(
        n.get("edgeType") == "chunk_cites_entry" and str(n.get("_id", "")).startswith("alexandria_entities/")
        for n in thm_shared["dagNeighbors"]
    ), f"Expected genuine entity chunk_cites_entry neighbor on Theorem 1.1: {thm_shared['dagNeighbors']!r}"
    assert not any(
        n.get("edgeType") == "chunk_cites_entry" and str(n.get("_id", "")).startswith("alexandria_chunks/")
        for n in thm_shared["dagNeighbors"]
    ), f"Bogus chunk-to-chunk chunk_cites_entry fabricated on Theorem 1.1: {thm_shared['dagNeighbors']!r}"
    assert not any(
        n.get("edgeType") == "chunk_cites_entry" and str(n.get("_id", "")).startswith("alexandria_chunks/")
        for n in lem_shared["dagNeighbors"]
    ), f"Bogus chunk-to-chunk chunk_cites_entry fabricated on Lemma 2.1: {lem_shared['dagNeighbors']!r}"

    # seed_k == 0 parity between JSONL and Arango modes
    z_jsonl = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--input-dir", str(out_dir),
            "--query", "xqzvpeirce77",
            "--top-k", "5",
            "--seed-k", "0",
        ]
    )
    z_arango = run_cli(
        [
            str(GRAPH_CONTEXT_RANK_SCRIPT),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "xqzvpeirce77",
            "--top-k", "5",
            "--seed-k", "0",
        ],
        env_overrides=env,
    )
    assert z_jsonl.returncode == 0 and z_arango.returncode == 0
    z_pkt_j = json.loads(z_jsonl.stdout)
    z_pkt_a = json.loads(z_arango.stdout)
    assert z_pkt_j["seeds"] == [] and z_pkt_j["hits"] == []
    assert z_pkt_a["seeds"] == [] and z_pkt_a["hits"] == []

    # BUG-15: retrieve_context.py --hops 2 direction parity between JSONL and ArangoDB
    # 2-hop chain: Proof -> Theorem 2.1 -> Definition 1.1, and Theorem 2.1 -> [1] <- Lemma 3.1
    ret_jsonl = run_cli(
        [
            str(require_script(RETRIEVE_CONTEXT_SCRIPT)),
            "--input-dir", str(out_dir),
            "--query", "xqzvhop2dir99",
            "--top-k", "5",
            "--hops", "2",
        ]
    )
    ret_arango = run_cli(
        [
            str(require_script(RETRIEVE_CONTEXT_SCRIPT)),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "xqzvhop2dir99",
            "--top-k", "5",
            "--hops", "2",
        ],
        env_overrides=env,
    )
    assert ret_jsonl.returncode == 0, f"stderr={ret_jsonl.stderr}"
    assert ret_arango.returncode == 0, f"stderr={ret_arango.stderr}"
    ret_pkt_j = json.loads(ret_jsonl.stdout)
    ret_pkt_a = json.loads(ret_arango.stdout)
    assert_retrieval_authority(ret_pkt_j)
    assert_retrieval_authority(ret_pkt_a)
    assert len(ret_pkt_j["hits"]) == 1 and len(ret_pkt_a["hits"]) == 1

    dirs_j = {(n["_id"], n["edgeType"]): n["direction"] for n in ret_pkt_j["hits"][0]["dagNeighbors"]}
    dirs_a = {(n["_id"], n["edgeType"]): n["direction"] for n in ret_pkt_a["hits"][0]["dagNeighbors"]}
    assert dirs_a == dirs_j, f"hops=2 dagNeighbors direction mismatch: arango={dirs_a!r} vs jsonl={dirs_j!r}"
    edge_dirs_a = {n["edgeType"]: n["direction"] for n in ret_pkt_a["hits"][0]["dagNeighbors"]}
    assert edge_dirs_a.get("proof_proves_theorem") == "outbound"
    assert edge_dirs_a.get("chunk_uses_definition") == "outbound", (
        f"2-hop outbound chunk_uses_definition inverted: {ret_pkt_a['hits'][0]['dagNeighbors']!r}"
    )
    assert edge_dirs_a.get("chunk_cites_entry") == "outbound", (
        f"2-hop outbound chunk_cites_entry inverted: {ret_pkt_a['hits'][0]['dagNeighbors']!r}"
    )

    lem_ret_j = run_cli(
        [
            str(require_script(RETRIEVE_CONTEXT_SCRIPT)),
            "--input-dir", str(out_dir),
            "--query", "xqzvlemma31hop2",
            "--top-k", "5",
            "--hops", "2",
        ]
    )
    lem_ret_a = run_cli(
        [
            str(require_script(RETRIEVE_CONTEXT_SCRIPT)),
            "--arango",
            "--endpoint", isolated_alexandria_db["endpoint"],
            "--database", isolated_alexandria_db["database"],
            "--query", "xqzvlemma31hop2",
            "--top-k", "5",
            "--hops", "2",
        ],
        env_overrides=env,
    )
    assert lem_ret_j.returncode == 0 and lem_ret_a.returncode == 0
    lem_pkt_j = json.loads(lem_ret_j.stdout)
    lem_pkt_a = json.loads(lem_ret_a.stdout)
    assert len(lem_pkt_j["hits"]) == 1 and len(lem_pkt_a["hits"]) == 1
    lem_dirs_j = {(n["_id"], n["edgeType"]): n["direction"] for n in lem_pkt_j["hits"][0]["dagNeighbors"]}
    lem_dirs_a = {(n["_id"], n["edgeType"]): n["direction"] for n in lem_pkt_a["hits"][0]["dagNeighbors"]}
    assert lem_dirs_a == lem_dirs_j, f"Lemma hops=2 direction mismatch: arango={lem_dirs_a!r} vs jsonl={lem_dirs_j!r}"
    assert any(
        n.get("edgeType") == "chunk_cites_entry"
        and str(n.get("_id", "")).startswith("alexandria_entities/")
        and n.get("direction") == "outbound"
        for n in lem_pkt_a["hits"][0]["dagNeighbors"]
    )
    assert any(
        n.get("edgeType") == "chunk_cites_entry"
        and str(n.get("_id", "")).startswith("alexandria_chunks/")
        and n.get("direction") == "inbound"
        for n in lem_pkt_a["hits"][0]["dagNeighbors"]
    )

    # BUG-14: Python API top_k < 0 parity between retrieve_jsonl_context and retrieve_arango_context
    with pytest.raises(ValueError, match="top_k must be >= 0"):
        retrieve_context.retrieve_jsonl_context(out_dir, "xqzvpeirce77", top_k=-1)
    with pytest.raises(ValueError, match="top_k must be >= 0"):
        retrieve_context.retrieve_arango_context(
            "xqzvpeirce77",
            endpoint=isolated_alexandria_db["endpoint"],
            database=isolated_alexandria_db["database"],
            username=isolated_alexandria_db["username"],
            password=isolated_alexandria_db["password"],
            top_k=-1,
        )

    # Negative bounds exit 2
    neg_seed = run_cli(
        [str(GRAPH_CONTEXT_RANK_SCRIPT), "--input-dir", str(out_dir), "--query", "xqzvpeirce77", "--seed-k", "-1"]
    )
    neg_top = run_cli(
        [str(GRAPH_CONTEXT_RANK_SCRIPT), "--input-dir", str(out_dir), "--query", "xqzvpeirce77", "--top-k", "-1"]
    )
    assert neg_seed.returncode == 2
    assert neg_top.returncode == 2


def test_t5_03_bibliography_years_not_extracted_as_equation_labels(tmp_path: Path) -> None:
    """T5-03 (BUG-04): (YYYY) publication years in bibliography chunks never become equation labels or DAG targets."""
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_text_pdf(
        in_dir / "bib_years.pdf",
        [[
            "1. Introduction",
            "Theorem 1.1. By Eq. (1984) and Equation (2020), the Clifford algebra stabilizes [1][2].",
            "Proof. Direct algebraic verification completes Theorem 1.1. QED.",
            "References",
            "[1] D. Hestenes and G. Sobczyk, Clifford Algebra to Geometric Calculus (1984)",
            "[2] J. Author, Modern Spinor Analysis (2020)",
        ]],
        title="Bibliography Year Label Regression",
    )

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    chunks = read_jsonl(out_dir / "alexandria_chunks.jsonl")
    entities = read_jsonl(out_dir / "alexandria_entities.jsonl")
    dag_edges = read_jsonl(out_dir / "alexandria_dag_edges.jsonl")

    bib_chunks = [c for c in chunks if c["chunkKind"] == "bibliography"]
    assert len(bib_chunks) == 1
    bib = bib_chunks[0]
    assert bib["provenance"]["labels"] == []
    assert "Equation 1984" not in bib["title"]
    assert "Equation 2020" not in bib["title"]

    bib_chunk_keys = {c["_key"] for c in bib_chunks}
    bib_chunk_ids = {f"alexandria_chunks/{k}" for k in bib_chunk_keys}
    bogus_entities = [
        e for e in entities
        if e.get("entityType") == "math_label"
        and (e.get("chunkKey") in bib_chunk_keys or e.get("normalized") in {"equation 1984", "equation 2020"})
    ]
    assert bogus_entities == [], f"Unexpected math_label entities from bibliography years: {bogus_entities!r}"
    bogus_edges = [
        e for e in dag_edges
        if e.get("edgeType") == "chunk_references_result" and e.get("_to") in bib_chunk_ids
    ]
    assert bogus_edges == [], f"Unexpected chunk_references_result edge pointing to bibliography: {bogus_edges!r}"


def test_t5_04_toc_head_sample_and_parenthesized_doi_normalization(tmp_path: Path) -> None:
    """T5-04 (BUG-05, BUG-06): TOC variants isolate body vs bibliography DOIs; unmatched ')' stripped from DOIs."""
    # White-box checks on _pre_bibliography_head_sample for both TOC failure modes
    prelim_sample = pdf_corpus_ingest._pre_bibliography_head_sample(
        [
            "Contents",
            "1. Preliminaries",
            "References",
            "20",
            "1. Preliminaries",
            "Own DOI: doi:10.1000/ownpaper",
            "REFERENCES",
            "[1] Cited Paper, doi:10.9999/cited_leak",
        ]
    )
    assert "10.1000/ownpaper" in prelim_sample
    assert "10.9999/cited_leak" not in prelim_sample

    multiline_sample = pdf_corpus_ingest._pre_bibliography_head_sample(
        [
            "Contents",
            "1. Introduction",
            "References",
            "Appendix A",
            "Appendix B",
            "Appendix C",
            "Notation",
            "1. Introduction",
            "Own DOI: doi:10.1000/ownpaper",
            "REFERENCES",
            "[1] Cited Paper, doi:10.9999/cited_leak",
        ]
    )
    assert "10.1000/ownpaper" in multiline_sample
    assert "10.9999/cited_leak" not in multiline_sample

    # BUG-13: TOC "References" immediately followed by "1. Introduction" / "1. Preliminaries" without page number line
    intro_direct_sample = pdf_corpus_ingest._pre_bibliography_head_sample(
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
    assert "10.1000/own_intro" in intro_direct_sample
    assert "10.9999/leak_intro" not in intro_direct_sample

    subsec_direct_sample = pdf_corpus_ingest._pre_bibliography_head_sample(
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
    assert "10.1000/own_subsec" in subsec_direct_sample
    assert "10.9999/leak_subsec" not in subsec_direct_sample

    # End-to-end pipeline verification with parenthesized & balanced Elsevier DOIs
    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_text_pdf(
        in_dir / "a_prelim_toc.pdf",
        [[
            "Contents",
            "1. Preliminaries",
            "References",
            "20",
            "1. Preliminaries",
            "We establish the main theorem here (doi:10.1000/prelimown) and reference (doi:10.1016/0003-4916(83)90176-8).",
            "Theorem 1.1. Every finite-dimensional Clifford module splits orthogonally.",
            "REFERENCES",
            "[1] Leaked Target, Some Journal (doi:10.9999/leakedtarget).",
        ]],
        title="Prelim TOC Paper",
    )
    build_text_pdf(
        in_dir / "b_multiline_toc.pdf",
        [[
            "Contents",
            "1. Introduction",
            "References",
            "Appendix A",
            "Appendix B",
            "Appendix C",
            "Notation",
            "1. Introduction",
            "This work introduces (doi:10.1234/multitoc) and builds on [1].",
            "Theorem 1.1. The modular operator stabilizes under adiabatic deformation.",
            "References",
            "[1] Prelim Author, Prelim TOC Paper (doi:10.1000/prelimown).",
            "[2] Elsevier Classic, Annals of Physics (doi:10.1016/0003-4916(83)90176-8).",
        ]],
        title="Multiline TOC Paper",
    )
    build_text_pdf(
        in_dir / "z_leaked_target.pdf",
        [[
            "doi:10.9999/leakedtarget",
            "1. Introduction",
            "Theorem 1.1. Target theorem referenced only by a_prelim_toc bibliography.",
        ]],
        title="Leaked Target Paper",
    )

    proc = _run_pdf_ingest(in_dir, out_dir)
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    docs = {d["relativePath"]: d["_key"] for d in read_jsonl(out_dir / "alexandria_documents.jsonl")}
    entities = read_jsonl(out_dir / "alexandria_entities.jsonl")
    dag_edges = read_jsonl(out_dir / "alexandria_dag_edges.jsonl")

    bib_dois = {
        e["metadata"]["doi"]
        for e in entities
        if e.get("entityType") == "bib_entry" and isinstance(e.get("metadata"), dict) and e["metadata"].get("doi")
    }
    assert "10.9999/leakedtarget" in bib_dois
    assert "10.1000/prelimown" in bib_dois
    assert "10.1016/0003-4916(83)90176-8" in bib_dois
    assert not any(d.endswith(")") and d.count(")") > d.count("(") for d in bib_dois), (
        f"Unbalanced trailing ')' survived in bib DOIs: {bib_dois!r}"
    )

    cross_pairs = {
        (e["_from"], e["_to"], e.get("evidence"))
        for e in dag_edges
        if e.get("edgeType") == "document_cites_document"
    }
    a_id = f"alexandria_documents/{docs['a_prelim_toc.pdf']}"
    b_id = f"alexandria_documents/{docs['b_multiline_toc.pdf']}"
    z_id = f"alexandria_documents/{docs['z_leaked_target.pdf']}"

    assert (a_id, z_id, "doi:10.9999/leakedtarget") in cross_pairs, (
        f"Expected a_prelim_toc -> z_leaked_target citation edge, got {cross_pairs!r}"
    )
    assert (b_id, a_id, "doi:10.1000/prelimown") in cross_pairs, (
        f"Expected b_multiline_toc -> a_prelim_toc citation edge, got {cross_pairs!r}"
    )
    assert not any(src == b_id and dst == z_id for src, dst, _ in cross_pairs)


def test_t5_05_unreadable_chmod000_pdf_and_invalid_cli_bounds(tmp_path: Path) -> None:
    """T5-05 (BUG-07, BUG-08): chmod 000 non-empty PDF -> parse_error (not empty_0_bytes); invalid flags exit 2."""
    assert os.geteuid() != 0, "Tier 5 chmod 000 permission test requires non-root execution"

    in_dir = tmp_path / "in"
    out_dir = tmp_path / "out"
    build_text_pdf(
        in_dir / "valid.pdf",
        [[
            "1. Intro",
            "Theorem 1.1. Readable mathematical content with sufficient characters for full ingestion into Alexandria.",
            "Proof. Every finite-dimensional Clifford algebra satisfies the standard identity. QED.",
        ]],
        title="Valid Paper",
    )
    build_zero_byte_pdf(in_dir / "empty.pdf")
    unreadable = build_text_pdf(
        in_dir / "unreadable.pdf",
        [["1. Secret", "Theorem 1.1. Non-empty file whose permissions will be revoked."]],
        title="Unreadable Paper",
    )
    orig_size = unreadable.stat().st_size
    assert orig_size > 100

    unreadable.chmod(0)
    try:
        proc = _run_pdf_ingest(in_dir, out_dir)
    finally:
        unreadable.chmod(stat.S_IRUSR | stat.S_IWUSR)

    assert proc.returncode == 0, f"stderr={proc.stderr}"
    report = read_inventory_report(out_dir)
    assert report["outcome_counts"]["empty_0_bytes"] == 1
    assert report["outcome_counts"]["parse_error"] == 1
    assert report["outcome_counts"]["ingested"] == 1

    by_rel = {row["relativePath"]: row for row in report["unique_documents"]}
    assert by_rel["empty.pdf"]["outcome"] == "empty_0_bytes"
    assert by_rel["empty.pdf"]["sizeBytes"] == 0
    assert by_rel["unreadable.pdf"]["outcome"] == "parse_error"
    assert by_rel["unreadable.pdf"]["sizeBytes"] == orig_size
    assert "PermissionError" in by_rel["unreadable.pdf"]["reason"]

    # Invalid CLI parameter bounds must exit 2 via argparse without creating parse errors
    for idx, bad_flag in enumerate(
        [
            ["--workers", "0"],
            ["--workers", "-2"],
            ["--per-file-timeout", "0"],
            ["--per-file-timeout", "-1"],
            ["--max-chunk-chars", "0"],
            ["--min-text-chars", "-5"],
        ]
    ):
        bad_out = tmp_path / f"bad_out_{idx}"
        bad_proc = _run_pdf_ingest(in_dir, bad_out, extra_args=bad_flag)
        assert bad_proc.returncode == 2, f"Expected exit 2 for {bad_flag}, got {bad_proc.returncode}"
        assert not bad_out.exists()


def test_t5_06_incremental_skip_unchanged_cross_doc_citation_and_arango_ingest_errors(
    tmp_path: Path, isolated_alexandria_db: dict[str, str]
) -> None:
    """T5-06 (BUG-09, BUG-10): --skip-unchanged imports new doc_unchanged->doc_new edges; arango_ingest handles missing input/DB cleanly."""
    in_dir = tmp_path / "in"
    out_1 = tmp_path / "out1"
    out_2 = tmp_path / "out2"

    build_text_pdf(
        in_dir / "a_citing.pdf",
        [[
            "1. Introduction",
            "Theorem 1.1. This unchanged paper cites a target paper added in a later batch [1].",
            "References",
            "[1] Target Author, Added Later Paper, doi:10.5555/target2026, 2026.",
        ]],
        title="Citing Unchanged Paper",
    )

    env = {
        "ALEXANDRIA_ARANGO_USERNAME": isolated_alexandria_db["username"],
        "ALEXANDRIA_ARANGO_PASSWORD": isolated_alexandria_db["password"],
    }
    base_args = [
        "--ingest-arango",
        "--endpoint", isolated_alexandria_db["endpoint"],
        "--database", isolated_alexandria_db["database"],
        "--skip-unchanged",
    ]

    p1 = _run_pdf_ingest(in_dir, out_1, extra_args=base_args, env_overrides=env)
    assert p1.returncode == 0, f"stderr={p1.stderr}"

    # Add newly cited document in batch 2 while a_citing.pdf remains unchanged
    build_text_pdf(
        in_dir / "z_cited.pdf",
        [[
            "doi:10.5555/target2026",
            "1. Introduction",
            "Definition 1.1 (Target Object): Newly added target paper discovered in batch 2.",
        ]],
        title="Added Later Paper",
    )

    p2 = _run_pdf_ingest(in_dir, out_2, extra_args=base_args, env_overrides=env)
    assert p2.returncode == 0, f"stderr={p2.stderr}"
    rep2 = read_inventory_report(out_2)
    assert rep2["arango_ingest"]["skippedUnchanged"] == 1
    assert rep2["arango_ingest"]["imported"].get("alexandria_documents") == 1

    cross_edges = arango_aql(
        isolated_alexandria_db["endpoint"],
        isolated_alexandria_db["database"],
        isolated_alexandria_db["username"],
        isolated_alexandria_db["password"],
        'FOR e IN alexandria_dag_edges FILTER e.edgeType == "document_cites_document" RETURN e',
    )
    assert len(cross_edges) == 1, f"Expected doc_unchanged->doc_new edge in ArangoDB, got {cross_edges!r}"
    assert cross_edges[0]["evidence"] == "doi:10.5555/target2026"

    # BUG-10: nonexistent --input-dir and --search-view-only on missing DB fail cleanly with JSON error, no empty DB created
    user, pw = require_alexandria_8532()
    missing_db = f"alexandria_e2e_test_{uuid.uuid4().hex[:8]}"
    assert_safe_test_target(ALEXANDRIA_ENDPOINT, missing_db)
    try:
        bad_dir_proc = run_cli(
            [
                str(ARANGO_INGEST_SCRIPT),
                "--input-dir", str(tmp_path / "does_not_exist"),
                "--endpoint", ALEXANDRIA_ENDPOINT,
                "--database", missing_db,
                "--username", user,
                "--password", pw,
            ]
        )
        assert bad_dir_proc.returncode == 1
        assert "Traceback" not in bad_dir_proc.stderr
        assert "error" in json.loads(bad_dir_proc.stderr)
        assert missing_db not in arango_list_databases(ALEXANDRIA_ENDPOINT, user, pw)

        missing_view_proc = run_cli(
            [
                str(ARANGO_INGEST_SCRIPT),
                "--search-view-only",
                "--endpoint", ALEXANDRIA_ENDPOINT,
                "--database", missing_db,
                "--username", user,
                "--password", pw,
            ]
        )
        assert missing_view_proc.returncode == 1
        assert "Traceback" not in missing_view_proc.stderr
        assert "error" in json.loads(missing_view_proc.stderr)
    finally:
        arango_http_json("DELETE", f"{ALEXANDRIA_ENDPOINT}/_api/database/{quote(missing_db)}", user, pw, timeout=5.0)


def test_t5_07_research_digest_worker_error_handling_and_cli_validation() -> None:
    """T5-07 (BUG-11): Unreachable Hive endpoint emits JSON error without traceback; empty endpoint / invalid bounds exit 2."""
    script = require_script(RESEARCH_DIGEST_WORKER_SCRIPT)

    unreachable = run_cli(
        [str(script), "--once", "--hive-endpoint", "http://127.0.0.1:59999"],
        timeout=30.0,
    )
    assert unreachable.returncode == 1
    assert "Traceback" not in unreachable.stderr
    err_payload = json.loads(unreachable.stderr)
    assert "error" in err_payload and err_payload["error"]

    empty_ep = run_cli(
        [
            str(script),
            "--once",
            "--alexandria-endpoint", "",
            "--hive-endpoint", "http://127.0.0.1:59999",
        ],
        timeout=30.0,
    )
    assert empty_ep.returncode == 2
    assert "Traceback" not in empty_ep.stderr
    assert "error" in json.loads(empty_ep.stderr)

    for bad_flag in (["--lease-seconds", "0"], ["--timeout", "0"], ["--poll-interval", "0"]):
        proc = run_cli([str(script), "--once", *bad_flag], timeout=30.0)
        assert proc.returncode == 2, f"Expected exit 2 for {bad_flag}, got {proc.returncode}"
