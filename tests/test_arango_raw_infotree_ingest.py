import json
from pathlib import Path

from tools.infra.arango_raw_infotree_ingest import raw_row_edges


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def test_raw_infotree_edges_preserve_projection_descent(tmp_path: Path) -> None:
    write_jsonl(tmp_path / "raw_infotree_roots.jsonl", [{"rootKey": "r0", "file": "A.lean", "module": "A"}])
    write_jsonl(
        tmp_path / "raw_infotree_nodes.jsonl",
        [
            {"rootKey": "r0", "nodeKey": "n0", "kind": "context"},
            {"rootKey": "r0", "nodeKey": "n1", "kind": "tactic", "payloadKey": "p0"},
        ],
    )
    write_jsonl(
        tmp_path / "raw_infotree_edges.jsonl",
        [{"rootKey": "r0", "edgeKey": "e0", "parentKey": "n0", "childKey": "n1", "siblingIndex": 0}],
    )
    write_jsonl(tmp_path / "raw_infotree_contexts.jsonl", [{"contextKey": "c0", "nodeKey": "n0", "contextKind": "commandCtx"}])
    write_jsonl(tmp_path / "raw_infotree_payloads.jsonl", [{"payloadKey": "p0", "nodeKey": "n1", "kind": "tactic"}])
    write_jsonl(tmp_path / "raw_infotree_payload_fields.jsonl", [{"fieldKey": "pf0", "payloadKey": "p0", "nodeKey": "n1", "field": "goalsBefore"}])
    write_jsonl(tmp_path / "raw_infotree_decl_links.jsonl", [{"linkKey": "dl0", "nodeKey": "n1", "declName": "A.foo"}])
    write_jsonl(tmp_path / "raw_infotree_env_refs.jsonl", [{"envRefKey": "er0", "nodeKey": "n0", "role": "env", "present": True}])
    write_jsonl(tmp_path / "raw_infotree_mctx_refs.jsonl", [{"mctxRefKey": "mr0", "mctxKey": "mc0", "nodeKey": "n1"}])
    write_jsonl(tmp_path / "raw_infotree_mctx_decls.jsonl", [{"declKey": "md0", "mctxKey": "mc0", "nodeKey": "n1", "mvarId": "m.1"}])
    write_jsonl(
        tmp_path / "raw_infotree_lctx_refs.jsonl",
        [
            {"lctxRefKey": "lr0", "nodeKey": "n1", "sourceKind": "mctx_decl", "sourceKey": "md0", "lctxKey": "lc0", "lctxSize": 1},
            {"lctxRefKey": "lr1", "nodeKey": "n1", "sourceKind": "term", "sourceKey": "itlcs_p0_term", "lctxKey": "lc1", "lctxSize": 1},
        ],
    )
    write_jsonl(
        tmp_path / "raw_infotree_lctx_decls.jsonl",
        [
            {"lctxDeclKey": "ld0", "nodeKey": "n1", "sourceKind": "lctx_context", "sourceKey": "lc0", "lctxKey": "lc0", "fvarId": "f.1"},
            {"lctxDeclKey": "ld1", "nodeKey": "n1", "sourceKind": "lctx_context", "sourceKey": "lc1", "lctxKey": "lc1", "fvarId": "f.2"},
        ],
    )
    write_jsonl(
        tmp_path / "raw_infotree_projection_leakage.jsonl",
        [{"rootKey": "r0", "nodeKey": "n1", "field": "term_expr_graph", "reason": "not serialized"}],
    )
    write_jsonl(
        tmp_path / "raw_infotree_fvar_lineage.jsonl",
        [{"rootKey": "r0", "nodeKey": "n1", "lineageKey": "fl0", "fvarId": "f.1", "role": "intro"}],
    )
    write_jsonl(
        tmp_path / "raw_infotree_tactic_arguments.jsonl",
        [{"rootKey": "r0", "nodeKey": "n1", "argumentKey": "ta0", "declName": "A.foo"}],
    )
    write_jsonl(
        tmp_path / "raw_infotree_messages.jsonl",
        [{"rootKey": "r0", "nodeKey": "n1", "messageKey": "msg0", "severity": "warning", "text": "test"}],
    )
    write_jsonl(
        tmp_path / "raw_infotree_goal_states.jsonl",
        [{"rootKey": "r0", "nodeKey": "n1", "stateKey": "gs0", "mvarId": "m.1", "role": "before", "index": 0}],
    )

    edges = raw_row_edges(tmp_path)

    assert edges["raw_infotree_tree_edges"][0]["_from"] == "raw_infotree_nodes/n0"
    assert edges["raw_infotree_tree_edges"][0]["_to"] == "raw_infotree_nodes/n1"
    assert edges["raw_infotree_tree_edges"][0]["siblingIndex"] == 0

    assert edges["raw_infotree_node_context_edges"][0]["_to"] == "raw_infotree_contexts/c0"
    assert edges["raw_infotree_node_payload_edges"][0]["_to"] == "raw_infotree_payloads/p0"
    assert edges["raw_infotree_payload_field_edges"][0]["_from"] == "raw_infotree_payloads/p0"
    assert edges["raw_infotree_node_mctx_ref_edges"][0]["_to"] == "raw_infotree_mctx_refs/mr0"
    assert edges["raw_infotree_mctx_decl_edges"][0]["_from"] == "raw_infotree_mctx_refs/mr0"

    lctx_refs = edges["raw_infotree_source_lctx_ref_edges"]
    assert lctx_refs[0]["_from"] == "raw_infotree_mctx_decls/md0"
    assert lctx_refs[0]["_to"] == "raw_infotree_lctx_refs/lr0"
    assert lctx_refs[1]["_from"] == "raw_infotree_nodes/n1"
    assert lctx_refs[1]["_to"] == "raw_infotree_lctx_refs/lr1"

    lctx_decl_edges = edges["raw_infotree_lctx_ref_decl_edges"]
    assert lctx_decl_edges[0]["_from"] == "raw_infotree_lctx_refs/lr0"
    assert lctx_decl_edges[0]["_to"] == "raw_infotree_lctx_decls/ld0"
    assert lctx_decl_edges[1]["_from"] == "raw_infotree_lctx_refs/lr1"
    assert lctx_decl_edges[1]["_to"] == "raw_infotree_lctx_decls/ld1"

    leakage = edges["raw_infotree_node_leakage_edges"]
    assert len(leakage) == 1
    assert leakage[0]["_from"] == "raw_infotree_nodes/n1"
    assert leakage[0]["_to"].startswith("raw_infotree_projection_leakage/")

    fvar_edges = edges["raw_infotree_node_fvar_edges"]
    assert len(fvar_edges) == 1
    assert fvar_edges[0]["_from"] == "raw_infotree_nodes/n1"
    assert fvar_edges[0]["_to"] == "raw_infotree_fvar_lineage/fl0"

    arg_edges = edges["raw_infotree_node_argument_edges"]
    assert len(arg_edges) == 1
    assert arg_edges[0]["_from"] == "raw_infotree_nodes/n1"
    assert arg_edges[0]["_to"] == "raw_infotree_tactic_arguments/ta0"

    msg_edges = edges["raw_infotree_node_message_edges"]
    assert len(msg_edges) == 1
    assert msg_edges[0]["_from"] == "raw_infotree_nodes/n1"
    assert msg_edges[0]["_to"] == "raw_infotree_messages/msg0"

    goal_edges = edges["raw_infotree_node_goal_edges"]
    assert len(goal_edges) == 1
    assert goal_edges[0]["_from"] == "raw_infotree_nodes/n1"
    assert goal_edges[0]["_to"] == "raw_infotree_goal_states/gs0"
