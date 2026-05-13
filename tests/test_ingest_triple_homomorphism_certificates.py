import json
from pathlib import Path

from tools.infra.ingest_triple_homomorphism_certificates import (
    DEFAULT_OUTPUT,
    materialize_edges,
    normalize_certificate_edge,
)


def write_json(path: Path, row: dict) -> None:
    path.write_text(json.dumps(row, sort_keys=True) + "\n", encoding="utf-8")


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_triple_hom_certificate_edge_classifies_verified_audit() -> None:
    edge = normalize_certificate_edge(
        {
            "sourceTriples": 2,
            "targetTriples": 2,
            "objectMappings": 3,
            "relationMappings": 2,
            "checkedTriples": 2,
            "preservedTriples": 2,
            "missingTriples": 0,
            "leanVerified": True,
            "verificationTier": "lean_native_finite_triple_homomorphism",
            "proofAuthority": "Lean finite triple preservation checker",
            "checker": "DAG.TripleHomomorphismExport.auditHomomorphism",
        },
        source_id="ig_decl_topologies/source",
        target_id="ig_decl_topologies/target",
        source_label="A.source",
        target_label="A.target",
    )

    assert edge["kind"] == "triple_homomorphism_certificate"
    assert edge["status"] == "triple_hom_verified"
    assert edge["leanVerified"] is True
    assert edge["safeForDedupSCC"] is True
    assert edge["safeForAutoRewrite"] is False
    assert edge["graphUse"] == "triple-homomorphism-scc"
    assert "triple_preserved" in edge["tags"]


def test_triple_hom_certificate_edge_classifies_rejected_audit() -> None:
    edge = normalize_certificate_edge(
        {
            "checkedTriples": 2,
            "preservedTriples": 1,
            "missingTriples": 1,
            "leanVerified": False,
            "verificationTier": "lean_native_finite_triple_homomorphism",
        },
        source_id="ig_decl_topologies/source",
        target_id="ig_decl_topologies/target",
    )

    assert edge["status"] == "triple_hom_rejected"
    assert edge["leanVerified"] is False
    assert edge["safeForDedupSCC"] is False
    assert edge["safeForAutoRewrite"] is False
    assert edge["graphUse"] == "rejected-candidate"
    assert "missing_mapped_triples" in edge["tags"]


def test_materialize_triple_hom_edges_includes_missing_evidence(tmp_path: Path) -> None:
    audit = tmp_path / "audit.json"
    missing = tmp_path / "missing.jsonl"
    write_json(
        audit,
        {
            "sourceTriples": 2,
            "targetTriples": 1,
            "objectMappings": 3,
            "relationMappings": 2,
            "checkedTriples": 2,
            "preservedTriples": 1,
            "missingTriples": 1,
            "leanVerified": False,
            "verificationTier": "lean_native_finite_triple_homomorphism",
            "proofAuthority": "Lean finite triple preservation checker",
            "checker": "DAG.TripleHomomorphismExport.auditHomomorphism",
        },
    )
    write_jsonl(
        missing,
        [
            {
                "subject": "expr_1",
                "predicate": "uses_const",
                "object": "Nat.add",
                "mappedSubject": "expr_A",
                "mappedPredicate": "uses_const",
                "mappedObject": "Nat.add",
            }
        ],
    )

    edges = materialize_edges(
        audit,
        missing,
        source_id="ig_decl_topologies/source",
        target_id="ig_decl_topologies/target",
    )

    assert len(edges) == 2
    assert edges[0]["kind"] == "triple_homomorphism_certificate"
    assert edges[0]["status"] == "triple_hom_rejected"
    assert edges[1]["kind"] == "missing_mapped_triple"
    assert edges[1]["mappedSubject"] == "expr_A"
    assert edges[1]["certificateHash"] == edges[0]["certificateHash"]


def test_default_triple_hom_output_matches_wire_topology_ingest_dir() -> None:
    assert DEFAULT_OUTPUT == Path("artifacts/expr-graph/wire-topology/ig_triple_homomorphism_edges.jsonl")
