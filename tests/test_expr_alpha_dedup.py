from pathlib import Path

from tools.infra.generate_expr_alpha_dedup import (
    build_enriched_raw_rows,
    compute_debruijn_node_hash,
    compute_debruijn_incidence_hash,
    compute_binder_incidence_hash,
    compute_alpha_local_hash,
    stable_hash,
    sha256_hex,
)


def test_sha256_hex_deterministic() -> None:
    assert sha256_hex("hello") == sha256_hex("hello")
    assert sha256_hex("hello") != sha256_hex("world")
    assert len(sha256_hex("test")) == 64  # SHA-256 hex is 64 chars


def test_stable_hash_is_sha256() -> None:
    assert stable_hash("test") == sha256_hex("test")
    assert len(stable_hash("anything")) == 64


def test_compute_debruijn_node_hash_deterministic() -> None:
    node = {
        "decl": "MyTheorem",
        "sectionTag": "type",
        "path": "type.body",
        "deBruijnIdx": 2,
    }
    h1 = compute_debruijn_node_hash(node)
    h2 = compute_debruijn_node_hash(node)
    assert h1 == h2
    assert len(h1) == 64


def test_compute_debruijn_node_hash_varies_with_idx() -> None:
    base = {"decl": "T", "sectionTag": "type", "path": "body"}
    h0 = compute_debruijn_node_hash({**base, "deBruijnIdx": 0})
    h1 = compute_debruijn_node_hash({**base, "deBruijnIdx": 1})
    assert h0 != h1


def test_compute_debruijn_node_hash_varies_with_decl() -> None:
    base = {"sectionTag": "type", "path": "body", "deBruijnIdx": 0}
    ha = compute_debruijn_node_hash({**base, "decl": "TheoremA"})
    hb = compute_debruijn_node_hash({**base, "decl": "TheoremB"})
    assert ha != hb


def test_compute_debruijn_incidence_hash_deterministic() -> None:
    src = {"_key": "x_42", "decl": "T", "sectionTag": "type"}
    dst = {"_key": "x_10", "decl": "T", "sectionTag": "type"}
    h1 = compute_debruijn_incidence_hash(src, dst, 1)
    h2 = compute_debruijn_incidence_hash(src, dst, 1)
    assert h1 == h2
    assert len(h1) == 64


def test_compute_debruijn_incidence_hash_varies_with_idx() -> None:
    src = {"_key": "x_1", "decl": "T", "sectionTag": "type"}
    dst = {"_key": "x_2", "decl": "T", "sectionTag": "type"}
    h0 = compute_debruijn_incidence_hash(src, dst, 0)
    h1 = compute_debruijn_incidence_hash(src, dst, 1)
    assert h0 != h1


def test_compute_binder_incidence_hash_deterministic() -> None:
    h1 = compute_binder_incidence_hash("x_10", ["x_1", "x_2", "x_3"], "MyDecl")
    h2 = compute_binder_incidence_hash("x_10", ["x_1", "x_2", "x_3"], "MyDecl")
    assert h1 == h2
    assert len(h1) == 64


def test_compute_binder_incidence_hash_varies_with_bvars() -> None:
    h1 = compute_binder_incidence_hash("x_10", ["x_1"], "T")
    h2 = compute_binder_incidence_hash("x_10", ["x_1", "x_2"], "T")
    assert h1 != h2


def test_compute_binder_incidence_hash_order_invariant() -> None:
    """Order of bvar keys should not matter (sorted internally)."""
    h1 = compute_binder_incidence_hash("x_10", ["x_3", "x_1", "x_2"], "T")
    h2 = compute_binder_incidence_hash("x_10", ["x_1", "x_2", "x_3"], "T")
    assert h1 == h2


def test_compute_alpha_local_hash_deterministic() -> None:
    children = [("fn", "abc123"), ("arg", "def456")]
    h1 = compute_alpha_local_hash("x_1", children, "app", "f a")
    h2 = compute_alpha_local_hash("x_1", children, "app", "f a")
    assert h1 == h2
    assert len(h1) == 64


def test_compute_alpha_local_hash_varies_with_children() -> None:
    h1 = compute_alpha_local_hash("x_1", [("fn", "aaa")], "app", "f a")
    h2 = compute_alpha_local_hash("x_1", [("fn", "bbb")], "app", "f a")
    assert h1 != h2


def test_compute_alpha_local_hash_role_order_invariant() -> None:
    """Role order should not matter (sorted internally)."""
    h1 = compute_alpha_local_hash("x_1", [("arg", "z"), ("fn", "a")], "app", "f a")
    h2 = compute_alpha_local_hash("x_1", [("fn", "a"), ("arg", "z")], "app", "f a")
    assert h1 == h2


def test_build_enriched_raw_rows_populates_sha256_identity_fields() -> None:
    nodes = [
        {
            "_key": "x_bvar",
            "graphKind": "expr",
            "exprTag": "bvar",
            "decl": "T",
            "sectionTag": "type",
            "path": "type.body",
            "deBruijnIdx": 0,
            "deBruijnHash": "h_process_local",
        },
        {
            "_key": "x_lam",
            "graphKind": "expr",
            "exprTag": "lam",
            "decl": "T",
            "sectionTag": "type",
            "path": "type",
        },
    ]
    edges = [
        {
            "_key": "e_bind",
            "_from": "ig_nodes/x_bvar",
            "_to": "ig_nodes/x_lam",
            "kind": "bind",
            "role": "bound_by",
            "deBruijnIdx": 0,
            "incidenceHash": "h_process_local",
        }
    ]
    node_by_key = {str(node["_key"]): node for node in nodes}
    binder_hash = compute_binder_incidence_hash("x_lam", ["x_bvar"], "T")

    enriched_nodes, enriched_edges = build_enriched_raw_rows(
        nodes,
        edges,
        node_by_key,
        {"x_bvar": "alpha_bvar", "x_lam": "alpha_lam"},
        [{"binder_key": "x_lam", "binderIncidenceHash": binder_hash}],
    )

    assert enriched_nodes[0]["deBruijnHash"] == compute_debruijn_node_hash(nodes[0])
    assert enriched_nodes[0]["deBruijnHash"] != "h_process_local"
    assert enriched_nodes[0]["alphaLocalHash"] == "alpha_bvar"
    assert enriched_nodes[1]["alphaLocalHash"] == "alpha_lam"
    assert enriched_edges[0]["incidenceHash"] == compute_debruijn_incidence_hash(nodes[0], nodes[1], 0)
    assert enriched_edges[0]["binderIncidenceHash"] == binder_hash
