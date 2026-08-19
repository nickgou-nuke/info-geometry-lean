import json

import pytest

from tools.infra.arango_causal_memory import (
    ArangoCausalMemory,
    ArangoError,
    ArangoTarget,
    local_preflight,
    normalize_embedding,
)


class CapturingMemory(ArangoCausalMemory):
    def __init__(self):
        super().__init__(ArangoTarget("http://127.0.0.1:8530", "db", "", ""))
        self.captured = None

    def execute_aql(self, query, bind_vars=None, *, allow_write=False, batch_size=1000):
        self.captured = (query, bind_vars, allow_write, batch_size)
        return {"result": []}


def test_normalize_embedding_rejects_empty_and_non_numeric() -> None:
    with pytest.raises(ArangoError):
        normalize_embedding([])
    with pytest.raises(ArangoError):
        normalize_embedding([1.0, True])
    with pytest.raises(ArangoError):
        normalize_embedding([1.0, "x"])


def test_attention_preflight_uses_collection_bind_vars_and_dimension_filter() -> None:
    client = CapturingMemory()
    client.execute_graph_attention([1, 2.5], decl_collection="ig_nodes", edge_collection="ig_edges", limit=3, depth=2)
    assert client.captured is not None
    query, bind_vars, allow_write, _batch_size = client.captured
    assert allow_write is False
    assert "FOR node IN @@decl_collection" in query
    assert "OUTBOUND node @@edge_collection" in query
    assert "LENGTH(node.embedding) == query_dim" in query
    assert "{decl_collection}" not in query
    assert bind_vars["@decl_collection"] == "ig_nodes"
    assert bind_vars["@edge_collection"] == "ig_edges"
    assert bind_vars["prompt_embedding"] == [1.0, 2.5]


def test_attention_preflight_rejects_bad_collection_name() -> None:
    client = CapturingMemory()
    with pytest.raises(ArangoError):
        client.execute_graph_attention([1.0], decl_collection="ig_nodes RETURN 1", edge_collection="ig_edges")


def test_local_preflight_prefers_dag_and_leantrail(tmp_path) -> None:
    dag_index = tmp_path / "artifacts" / "dag" / "index"
    dag_index.mkdir(parents=True)
    (dag_index / "decls.jsonl").write_text(
        json.dumps(
            {
                "name": "InfoGeometry.Test.fooBar",
                "kind": "theorem",
                "module": "InfoGeometry.Test",
                "file": "lean/InfoGeometry/Test.lean",
                "line": 12,
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (dag_index / "edges.jsonl").write_text(
        json.dumps({"src": "InfoGeometry.Test.fooBar", "dst": "InfoGeometry.Test.helper", "kind": "dependsOn"}) + "\n",
        encoding="utf-8",
    )
    leantrail_dir = tmp_path / "artifacts" / "leantrail"
    (leantrail_dir / "arango").mkdir(parents=True)
    (leantrail_dir / "graph_snapshot.json").write_text("{}\n", encoding="utf-8")
    (leantrail_dir / "arango" / "metadata.json").write_text("{}\n", encoding="utf-8")
    (leantrail_dir / "arango" / "ig_nodes.jsonl").write_text("{}\n", encoding="utf-8")
    (leantrail_dir / "arango" / "ig_edges.jsonl").write_text("{}\n", encoding="utf-8")
    records = tmp_path / "artifacts" / "leansearch_local" / "records.jsonl"
    records.parent.mkdir(parents=True)
    records.write_text(
        json.dumps(
            {
                "schema": "info_geometry.leansearch_local.record.v1",
                "authority": "navigation",
                "name": "InfoGeometry.Test.fooBar",
                "kind": "theorem",
                "module": "InfoGeometry.Test",
                "file": "lean/InfoGeometry/Test.lean",
                "line": 12,
                "doc": "foo bar theorem",
                "type": "True",
                "snippet": "theorem fooBar : True := by trivial",
            }
        )
        + "\n",
        encoding="utf-8",
    )

    out = local_preflight(
        "fooBar",
        index_dir=dag_index,
        leantrail_dir=leantrail_dir,
        records_path=records,
        depth=1,
        limit=5,
    )

    assert out["authority"]["level"] == "dag_leantrail_navigation"
    assert out["artifacts"]["dag"]["decls"]["exists"] is True
    assert out["artifacts"]["leantrail"]["snapshot"]["exists"] is True
    assert out["artifacts"]["leansearch_local"]["exists"] is True
    assert out["local_search"][0]["name"] == "InfoGeometry.Test.fooBar"
    assert out["local_attention"]["hits"][0]["name"] == "InfoGeometry.Test.fooBar"
    assert out["local_neighborhood"]["resolved"] == "InfoGeometry.Test.fooBar"
