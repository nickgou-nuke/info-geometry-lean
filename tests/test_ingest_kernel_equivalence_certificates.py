import json
from pathlib import Path

from tools.infra.ingest_kernel_equivalence_certificates import (
    materialize_edges,
    normalize_certificate_edge,
)


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_kernel_certificate_edge_classifies_type_only_as_not_rewrite_safe() -> None:
    edge = normalize_certificate_edge(
        {
            "sourceDecl": "A.left",
            "targetDecl": "A.right",
            "mode": "type",
            "sourceFound": True,
            "targetFound": True,
            "sourceKind": "theorem",
            "targetKind": "theorem",
            "sameKind": True,
            "kernelTypeDefEq": True,
            "kernelValueDefEq": False,
            "sourceHasValue": True,
            "targetHasValue": True,
            "leanVerified": True,
            "safeForAutoRewrite": False,
            "verificationTier": "lean_kernel_type_defeq",
            "proofAuthority": "lean-kernel-isDefEq",
            "checker": "Lean.Meta.isDefEq",
            "certificateHash": "lean-kernel-hash:1",
        }
    )

    assert edge["kind"] == "kernel_equivalence_certificate"
    assert edge["status"] == "verified_not_rewrite_safe"
    assert edge["leanVerified"] is True
    assert edge["kernelTypeDefEq"] is True
    assert edge["kernelValueDefEq"] is False
    assert edge["safeForAutoRewrite"] is False
    assert edge["graphUse"] == "verified-equivalence-only"
    assert edge["tags"] == [
        "kernel_type_defeq",
        "lean_verified",
        "rewrite_not_authorized",
    ]


def test_kernel_certificate_edge_classifies_type_and_value_as_rewrite_safe() -> None:
    edge = normalize_certificate_edge(
        {
            "sourceDecl": "A.left",
            "targetDecl": "A.right",
            "mode": "type-and-value",
            "kernelTypeDefEq": True,
            "kernelValueDefEq": True,
            "sourceHasValue": True,
            "targetHasValue": True,
            "leanVerified": True,
            "safeForAutoRewrite": True,
            "verificationTier": "lean_kernel_type_and_value_defeq",
            "certificateHash": "lean-kernel-hash:2",
        }
    )

    assert edge["status"] == "rewrite_safe"
    assert edge["graphUse"] == "rewrite-safe-scc"
    assert "kernel_type_defeq" in edge["tags"]
    assert "kernel_value_defeq" in edge["tags"]
    assert "rewrite_safe" in edge["tags"]


def test_kernel_certificate_edge_classifies_rejected_pair() -> None:
    edge = normalize_certificate_edge(
        {
            "sourceDecl": "A.left",
            "targetDecl": "A.right",
            "mode": "type-and-value",
            "kernelTypeDefEq": True,
            "kernelValueDefEq": False,
            "leanVerified": False,
            "safeForAutoRewrite": False,
            "verificationTier": "lean_kernel_type_and_value_defeq",
            "error": "",
        }
    )

    assert edge["status"] == "rejected"
    assert edge["graphUse"] == "rejected-candidate"
    assert "kernel_rejected" in edge["tags"]
    assert "rewrite_not_authorized" in edge["tags"]


def test_materialize_kernel_certificate_edges_from_jsonl(tmp_path: Path) -> None:
    certs = tmp_path / "certs.jsonl"
    write_jsonl(
        certs,
        [
            {
                "sourceDecl": "A.left",
                "targetDecl": "A.right",
                "mode": "type",
                "kernelTypeDefEq": True,
                "kernelValueDefEq": False,
                "leanVerified": True,
                "safeForAutoRewrite": False,
                "verificationTier": "lean_kernel_type_defeq",
            },
            {
                "sourceDecl": "A.left",
                "targetDecl": "A.clone",
                "mode": "type-and-value",
                "kernelTypeDefEq": True,
                "kernelValueDefEq": True,
                "sourceHasValue": True,
                "targetHasValue": True,
                "leanVerified": True,
                "safeForAutoRewrite": True,
                "verificationTier": "lean_kernel_type_and_value_defeq",
            },
        ],
    )

    edges = materialize_edges(certs)

    assert len(edges) == 2
    assert edges[0]["sourceDecl"] == "A.left"
    assert edges[0]["targetDecl"] == "A.right"
    assert edges[0]["graphUse"] == "verified-equivalence-only"
    assert edges[1]["targetDecl"] == "A.clone"
    assert edges[1]["graphUse"] == "rewrite-safe-scc"
    assert all(edge["_from"].startswith("ig_decl_topologies/") for edge in edges)
    assert all(edge["_to"].startswith("ig_decl_topologies/") for edge in edges)
