import json
from pathlib import Path

from tools.infra.report_certificate_authority_layers import build_markdown, build_report


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_certificate_authority_report_classifies_layered_actions(tmp_path: Path) -> None:
    triple_edges = tmp_path / "ig_triple_homomorphism_edges.jsonl"
    kernel_edges = tmp_path / "ig_kernel_equivalence_edges.jsonl"

    write_jsonl(
        triple_edges,
        [
            {
                "_from": "ig_decl_topologies/triple_only_a",
                "_to": "ig_decl_topologies/triple_only_b",
                "kind": "triple_homomorphism_certificate",
                "status": "triple_hom_verified",
                "sourceLabel": "A.tripleOnly",
                "targetLabel": "B.tripleOnly",
                "missingTriples": 0,
                "leanVerified": True,
                "safeForDedupSCC": True,
                "safeForAutoRewrite": False,
                "certificateHash": "sha256:triple-only",
            },
            {
                "_from": "ig_decl_topologies/statement_a",
                "_to": "ig_decl_topologies/statement_b",
                "kind": "triple_homomorphism_certificate",
                "status": "triple_hom_verified",
                "sourceLabel": "A.statement",
                "targetLabel": "B.statement",
                "missingTriples": 0,
                "leanVerified": True,
                "safeForDedupSCC": True,
                "safeForAutoRewrite": False,
                "certificateHash": "sha256:statement-triple",
            },
            {
                "_from": "ig_decl_topologies/rewrite_a",
                "_to": "ig_decl_topologies/rewrite_b",
                "kind": "triple_homomorphism_certificate",
                "status": "triple_hom_verified",
                "sourceLabel": "A.rewrite",
                "targetLabel": "B.rewrite",
                "missingTriples": 0,
                "leanVerified": True,
                "safeForDedupSCC": True,
                "safeForAutoRewrite": False,
                "certificateHash": "sha256:rewrite-triple",
            },
            {
                "_from": "ig_decl_topologies/rejected_a",
                "_to": "ig_decl_topologies/rejected_b",
                "kind": "triple_homomorphism_certificate",
                "status": "triple_hom_rejected",
                "sourceLabel": "A.rejected",
                "targetLabel": "B.rejected",
                "missingTriples": 1,
                "leanVerified": False,
                "safeForDedupSCC": False,
                "safeForAutoRewrite": False,
                "certificateHash": "sha256:rejected-triple",
            },
            {
                "_from": "ig_decl_topologies/rejected_a",
                "_to": "ig_decl_topologies/rejected_b",
                "kind": "missing_mapped_triple",
                "status": "missing_mapped_triple",
                "missingTripleHash": "sha256:missing",
            },
        ],
    )
    write_jsonl(
        kernel_edges,
        [
            {
                "_from": "ig_decl_topologies/statement_a",
                "_to": "ig_decl_topologies/statement_b",
                "kind": "kernel_equivalence_certificate",
                "status": "verified_not_rewrite_safe",
                "sourceDecl": "A.statement",
                "targetDecl": "B.statement",
                "leanVerified": True,
                "safeForAutoRewrite": False,
                "verificationTier": "lean_kernel_type_defeq",
                "certificateHash": "sha256:statement-kernel",
            },
            {
                "_from": "ig_decl_topologies/rewrite_a",
                "_to": "ig_decl_topologies/rewrite_b",
                "kind": "kernel_equivalence_certificate",
                "status": "rewrite_safe",
                "sourceDecl": "A.rewrite",
                "targetDecl": "B.rewrite",
                "leanVerified": True,
                "safeForAutoRewrite": True,
                "verificationTier": "lean_kernel_type_and_value_defeq",
                "certificateHash": "sha256:rewrite-kernel",
            },
        ],
    )

    report = build_report(triple_edges, kernel_edges)
    markdown = build_markdown(report)
    rows = {row["pair"]: row for row in report["pairs"]}

    assert report["stats"]["pairs"] == 4
    assert report["recommended_action_counts"] == {
        "candidate-rejected-with-missing-triples": 1,
        "rewrite-safe-dedup-scc": 1,
        "statement-equivalence-review": 1,
        "structural-equivalence-review": 1,
    }
    assert rows["A.tripleOnly -> B.tripleOnly"]["recommendedAction"] == "structural-equivalence-review"
    assert rows["A.statement -> B.statement"]["recommendedAction"] == "statement-equivalence-review"
    assert rows["A.rewrite -> B.rewrite"]["recommendedAction"] == "rewrite-safe-dedup-scc"
    assert rows["A.rejected -> B.rejected"]["recommendedAction"] == "candidate-rejected-with-missing-triples"
    assert rows["A.rejected -> B.rejected"]["missingTriples"] == 1
    assert rows["A.rewrite -> B.rewrite"]["safeForAutoRewrite"] is True

    assert "Certificate Authority Layers Report" in markdown
    assert "rewrite-safe-dedup-scc" in markdown
    assert "structural-equivalence-review" in markdown


def test_certificate_authority_report_treats_missing_inputs_as_empty(tmp_path: Path) -> None:
    report = build_report(tmp_path / "missing-triple.jsonl", tmp_path / "missing-kernel.jsonl")
    markdown = build_markdown(report)

    assert report["stats"]["pairs"] == 0
    assert report["pairs"] == []
    assert "_No certificate pairs found._" in markdown
