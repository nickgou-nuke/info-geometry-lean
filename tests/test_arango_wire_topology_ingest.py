import json
from pathlib import Path

from tools.infra.arango_wire_topology_ingest import (
    normalize_wire_row,
    preflight,
    wire_index_specs,
)


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def test_wire_topology_ingest_preserves_derived_raw_backpointers(tmp_path: Path) -> None:
    write_jsonl(
        tmp_path / "ig_wires.jsonl",
        [
            {
                "_key": "wire_1",
                "wireHash": "sha256:wire",
                "deBruijnHash": "sha256:bvar",
                "incidenceHash": "sha256:inc",
                "rawBvarId": "ig_nodes/x_bvar",
                "binderRawId": "ig_nodes/x_lam",
                "binderExpr": "ig_nodes/x_lam",
                "decl": "A.foo",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_gates.jsonl",
        [
            {
                "_key": "gate_1",
                "gateHash": "sha256:gate",
                "gateKind": "const",
                "operatorName": "HMul.hMul",
                "constName": "HMul.hMul",
                "rawExprId": "ig_nodes/x_const",
                "constDeclId": "ig_nodes/d_hmul",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_wire_edges.jsonl",
        [
            {
                "_key": "we_1",
                "_from": "ig_gates/gate_1",
                "_to": "ig_wires/wire_1",
                "kind": "binds_wire",
                "role": "binder_controls_wire",
                "incidenceHash": "sha256:inc",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_scc.jsonl",
        [
            {
                "_key": "scc_1",
                "kind": "wire_scc",
                "memberCount": 2,
                "sccPatternHash": "sha256:scc",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_scc_edges.jsonl",
        [
            {
                "_key": "se_1",
                "_from": "ig_wires/wire_1",
                "_to": "ig_scc/scc_1",
                "kind": "member_of_scc",
                "role": "member_of_scc",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_decl_topologies.jsonl",
        [
            {
                "_key": "topo_1",
                "decl": "A.foo",
                "ownerAwareHash": "sha256:owner",
                "patternHash": "sha256:pattern",
                "roleHash": "sha256:role",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_hashes.jsonl",
        [
            {
                "_key": "hash_1",
                "decl": "A.foo",
                "hash": "sha256:pattern",
                "hashKind": "patternHash",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_logic_tokens.jsonl",
        [
            {
                "_key": "tok_1",
                "decl": "A.foo",
                "hashKind": "patternHash",
                "value": "constClass:mul",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_logic_vectors.jsonl",
        [
            {
                "_key": "lv_1",
                "decl": "A.foo",
                "module": "A",
                "featureHash": "sha256:features",
                "featureCount": 1,
                "dimension": 2,
                "features": {"constClass:mul": 1},
                "logicVector": [1.0, 0.0],
                "identity": {"patternHash": "sha256:pattern"},
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_text_index_docs.jsonl",
        [
            {
                "_key": "doc_1",
                "decl": "A.foo",
                "module": "A",
                "featureHash": "sha256:features",
                "logicVector": [1.0, 0.0],
                "patternHash": "sha256:pattern",
                "reviewOnly": True,
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_translation_candidates.jsonl",
        [
            {
                "_key": "tc_1",
                "sourceDecl": "A.foo",
                "targetDecl": "A.bar",
                "candidateKind": "same_patternHash",
                "verified": True,
                "reviewOnly": False,
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_translation_edges.jsonl",
        [
            {
                "_key": "te_1",
                "_from": "ig_decl_topologies/topo_1",
                "_to": "ig_decl_topologies/topo_2",
                "kind": "verified_translation",
                "translationKind": "same_patternHash",
                "sourceDecl": "A.foo",
                "targetDecl": "A.bar",
                "translationHash": "sha256:translation",
                "safeForDedupSCC": True,
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_translation_scc.jsonl",
        [
            {
                "_key": "tscc_1",
                "kind": "translation_scc",
                "memberCount": 2,
                "translationSccHash": "sha256:tscc",
            }
        ],
    )
    write_jsonl(
        tmp_path / "ig_translation_scc_edges.jsonl",
        [
            {
                "_key": "tse_1",
                "_from": "ig_decl_topologies/topo_1",
                "_to": "ig_translation_scc/tscc_1",
                "kind": "member_of_translation_scc",
                "role": "member_of_translation_scc",
                "sourceDecl": "A.foo",
            }
        ],
    )

    pf = preflight(tmp_path)
    assert pf["missing_files"] == []
    assert pf["counts"] == {
        "ig_wires": 1,
        "ig_gates": 1,
        "ig_wire_edges": 1,
        "ig_scc": 1,
        "ig_scc_edges": 1,
        "ig_decl_topologies": 1,
        "ig_hashes": 1,
        "ig_logic_tokens": 1,
        "ig_logic_vectors": 1,
        "ig_text_index_docs": 1,
        "ig_translation_candidates": 1,
        "ig_translation_edges": 1,
        "ig_translation_scc": 1,
        "ig_translation_scc_edges": 1,
    }

    wire = next(json.loads(line) for line in (tmp_path / "ig_wires.jsonl").read_text().splitlines())
    gate = next(json.loads(line) for line in (tmp_path / "ig_gates.jsonl").read_text().splitlines())
    edge = next(json.loads(line) for line in (tmp_path / "ig_wire_edges.jsonl").read_text().splitlines())

    assert normalize_wire_row("ig_wires", wire)["wireKey"] == "wire_1"
    assert normalize_wire_row("ig_gates", gate)["gateKey"] == "gate_1"
    assert normalize_wire_row("ig_wire_edges", edge)["incidenceHash"] == "sha256:inc"
    assert normalize_wire_row("ig_scc", {"_key": "scc_1", "sccPatternHash": "sha256:scc"})["sccPatternHash"] == "sha256:scc"
    assert normalize_wire_row("ig_scc_edges", {"_key": "se_1", "_from": "ig_wires/wire_1", "_to": "ig_scc/scc_1"})["_from"] == "ig_wires/wire_1"
    assert normalize_wire_row("ig_decl_topologies", {"_key": "topo_1", "decl": "A.foo"})["decl"] == "A.foo"
    assert normalize_wire_row("ig_hashes", {"_key": "hash_1", "hash": "h", "hashKind": "patternHash"})["hash"] == "h"
    assert normalize_wire_row("ig_logic_tokens", {"_key": "tok_1", "decl": "A.foo", "value": "constClass:mul"})["value"] == "constClass:mul"
    assert normalize_wire_row("ig_logic_vectors", {"_key": "lv_1", "decl": "A.foo", "logicVector": [1.0], "features": {}})["decl"] == "A.foo"
    assert normalize_wire_row("ig_text_index_docs", {"_key": "doc_1", "decl": "A.foo", "logicVector": [1.0]})["decl"] == "A.foo"
    assert normalize_wire_row("ig_translation_candidates", {"_key": "tc_1", "sourceDecl": "A.foo", "targetDecl": "A.bar", "candidateKind": "same_patternHash"})["sourceDecl"] == "A.foo"
    assert normalize_wire_row("ig_translation_edges", {"_key": "te_1", "_from": "ig_decl_topologies/topo_1", "_to": "ig_decl_topologies/topo_2", "translationKind": "same_patternHash"})["translationKind"] == "same_patternHash"
    assert normalize_wire_row("ig_translation_scc", {"_key": "tscc_1", "translationSccHash": "sha256:tscc"})["translationSccHash"] == "sha256:tscc"
    assert normalize_wire_row("ig_translation_scc_edges", {"_key": "tse_1", "_from": "ig_decl_topologies/topo_1", "_to": "ig_translation_scc/tscc_1"})["_to"] == "ig_translation_scc/tscc_1"


def test_wire_topology_index_specs_cover_dual_overlay_fields() -> None:
    specs = wire_index_specs()

    wire_fields = [spec["fields"] for spec in specs["ig_wires"]]
    gate_fields = [spec["fields"] for spec in specs["ig_gates"]]
    edge_fields = [spec["fields"] for spec in specs["ig_wire_edges"]]
    scc_fields = [spec["fields"] for spec in specs["ig_scc"]]
    scc_edge_fields = [spec["fields"] for spec in specs["ig_scc_edges"]]
    topology_fields = [spec["fields"] for spec in specs["ig_decl_topologies"]]
    hash_fields = [spec["fields"] for spec in specs["ig_hashes"]]
    token_fields = [spec["fields"] for spec in specs["ig_logic_tokens"]]
    vector_fields = [spec["fields"] for spec in specs["ig_logic_vectors"]]
    doc_fields = [spec["fields"] for spec in specs["ig_text_index_docs"]]
    candidate_fields = [spec["fields"] for spec in specs["ig_translation_candidates"]]
    translation_edge_fields = [spec["fields"] for spec in specs["ig_translation_edges"]]
    translation_scc_fields = [spec["fields"] for spec in specs["ig_translation_scc"]]

    assert ["wireKey"] in wire_fields
    assert ["wireHash"] in wire_fields
    assert ["deBruijnHash"] in wire_fields
    assert ["incidenceHash"] in wire_fields
    assert ["binderExpr"] in wire_fields

    assert ["gateKey"] in gate_fields
    assert ["gateHash"] in gate_fields
    assert ["gateKind"] in gate_fields
    assert ["operatorName"] in gate_fields
    assert ["constName"] in gate_fields

    assert ["incidenceHash"] in edge_fields
    assert ["wireHash"] in edge_fields
    assert ["_from", "role"] in edge_fields
    assert ["_to", "role"] in edge_fields

    assert ["sccPatternHash"] in scc_fields
    assert ["memberCount"] in scc_fields
    assert ["kind", "role"] in scc_edge_fields

    assert ["ownerAwareHash"] in topology_fields
    assert ["patternHash"] in topology_fields
    assert ["roleHash"] in topology_fields

    assert ["hashKind", "hash"] in hash_fields
    assert ["hashKind", "value"] in token_fields
    assert ["featureHash"] in vector_fields
    assert ["identity.patternHash"] in vector_fields
    assert ["featureHash"] in doc_fields
    assert ["reviewOnly"] in doc_fields
    assert ["sourceDecl", "targetDecl"] in candidate_fields
    assert ["reviewOnly"] in candidate_fields
    assert ["verificationTier"] in candidate_fields
    assert ["leanVerified"] in candidate_fields
    assert ["safeForDerivedSCC"] in candidate_fields
    assert ["safeForAutoRewrite"] in candidate_fields
    assert ["translationHash"] in translation_edge_fields
    assert ["verificationTier"] in translation_edge_fields
    assert ["leanVerified"] in translation_edge_fields
    assert ["safeForDerivedSCC"] in translation_edge_fields
    assert ["safeForDedupSCC"] in translation_edge_fields
    assert ["safeForAutoRewrite"] in translation_edge_fields
    assert ["translationSccHash"] in translation_scc_fields
