import json
from pathlib import Path

from tools.infra.arango_expr_graph_ingest import (
    expr_index_specs,
    normalize_expr_row,
    preflight,
)


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def test_expr_graph_ingest_preserves_debruijn_incidence_fields(tmp_path: Path) -> None:
    write_jsonl(
        tmp_path / "ig_nodes.jsonl",
        [
            {
                "_key": "x_0",
                "graphKind": "expr",
                "exprTag": "bvar",
                "deBruijnIdx": 1,
                "deBruijnHash": "h_bvar",
                "alphaLocalHash": "h_alpha",
                "shapeHash": 123,
                "decl": "A.foo",
                "module": "A",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_edges.jsonl",
        [
            {
                "_key": "e_0",
                "_from": "ig_nodes/x_0",
                "_to": "ig_nodes/x_1",
                "kind": "bind",
                "role": "bound_by",
                "deBruijnIdx": 1,
                "incidenceHash": "h_incidence",
                "binderIncidenceHash": "h_binder",
                "decl": "A.foo",
            }
        ],
    )

    pf = preflight(tmp_path)
    assert pf["missing_files"] == []
    assert pf["counts"] == {"ig_nodes": 1, "ig_edges": 1}

    node = next(json.loads(line) for line in (tmp_path / "ig_nodes.jsonl").read_text().splitlines())
    edge = next(json.loads(line) for line in (tmp_path / "ig_edges.jsonl").read_text().splitlines())

    assert normalize_expr_row("ig_nodes", node)["deBruijnHash"] == "h_bvar"
    assert normalize_expr_row("ig_nodes", node)["alphaLocalHash"] == "h_alpha"
    assert normalize_expr_row("ig_edges", edge)["incidenceHash"] == "h_incidence"
    assert normalize_expr_row("ig_edges", edge)["binderIncidenceHash"] == "h_binder"
    assert normalize_expr_row("ig_edges", edge)["role"] == "bound_by"


def test_expr_graph_index_specs_cover_exact_symbolic_fields() -> None:
    specs = expr_index_specs()

    assert ["deBruijnHash"] in specs["ig_nodes"]
    assert ["alphaLocalHash"] in specs["ig_nodes"]
    assert ["alphaLocalHash", "exprTag"] in specs["ig_nodes"]
    assert ["shapeHash"] in specs["ig_nodes"]
    assert ["exprTag"] in specs["ig_nodes"]
    assert ["decl"] in specs["ig_nodes"]
    assert ["module"] in specs["ig_nodes"]

    assert ["incidenceHash"] in specs["ig_edges"]
    assert ["binderIncidenceHash"] in specs["ig_edges"]
    assert ["deBruijnIdx"] in specs["ig_edges"]
    assert ["_from", "role"] in specs["ig_edges"]
    assert ["_to", "role"] in specs["ig_edges"]
