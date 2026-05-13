import json
from pathlib import Path

from tools.infra.wire_topology_transform import transform


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_wire_topology_transform_derives_wires_gates_and_backpointers(tmp_path: Path) -> None:
    input_dir = tmp_path / "in"
    output_dir = tmp_path / "out"
    input_dir.mkdir()

    write_jsonl(
        input_dir / "ig_nodes.jsonl",
        [
            {
                "_key": "x_lam",
                "graphKind": "expr",
                "exprTag": "lam",
                "decl": "A.foo",
                "module": "A",
                "shapeHash": 10,
                "quality": "ok",
            },
            {
                "_key": "x_app",
                "graphKind": "expr",
                "exprTag": "app",
                "decl": "A.foo",
                "module": "A",
                "shapeHash": 11,
                "quality": "ok",
            },
            {
                "_key": "x_bvar",
                "graphKind": "expr",
                "exprTag": "bvar",
                "decl": "A.foo",
                "module": "A",
                "deBruijnIdx": 0,
                "deBruijnHash": "h_bvar",
                "shapeHash": 12,
                "quality": "ok",
            },
            {
                "_key": "x_bvar_again",
                "graphKind": "expr",
                "exprTag": "bvar",
                "decl": "A.foo",
                "module": "A",
                "deBruijnIdx": 0,
                "deBruijnHash": "h_bvar_again",
                "shapeHash": 14,
                "quality": "ok",
            },
            {
                "_key": "x_const",
                "graphKind": "expr",
                "exprTag": "const",
                "info": "HMul.hMul",
                "decl": "A.foo",
                "module": "A",
                "shapeHash": 13,
                "quality": "ok",
            },
            {
                "_key": "d_hmul",
                "graphKind": "decl",
                "decl": "HMul.hMul",
                "kind": "def",
                "module": "Init",
            },
        ],
    )
    write_jsonl(
        input_dir / "ig_edges.jsonl",
        [
            {
                "_key": "e_body",
                "_from": "ig_nodes/x_lam",
                "_to": "ig_nodes/x_app",
                "kind": "ast",
                "role": "body",
                "decl": "A.foo",
            },
            {
                "_key": "e_arg",
                "_from": "ig_nodes/x_app",
                "_to": "ig_nodes/x_bvar",
                "kind": "ast",
                "role": "arg",
                "decl": "A.foo",
            },
            {
                "_key": "e_bind",
                "_from": "ig_nodes/x_bvar",
                "_to": "ig_nodes/x_lam",
                "kind": "bind",
                "role": "bound_by",
                "decl": "A.foo",
                "deBruijnIdx": 0,
                "incidenceHash": "h_incidence",
            },
            {
                "_key": "e_bind_again",
                "_from": "ig_nodes/x_bvar_again",
                "_to": "ig_nodes/x_lam",
                "kind": "bind",
                "role": "bound_by",
                "decl": "A.foo",
                "deBruijnIdx": 0,
                "incidenceHash": "h_incidence_again",
            },
            {
                "_key": "e_const",
                "_from": "ig_nodes/x_const",
                "_to": "ig_nodes/d_hmul",
                "kind": "const_ref",
                "role": "const_ref",
                "decl": "A.foo",
            },
        ],
    )

    report = transform(input_dir, output_dir)

    assert report["counts"]["ig_wires"] == 5
    assert report["counts"]["ig_gates"] == 3
    assert report["counts"]["ig_scc"] >= 1
    assert report["truth_boundary"] == "derived projection; raw Lean evidence remains ig_nodes/ig_edges"

    wires = read_jsonl(output_dir / "ig_wires.jsonl")
    gates = read_jsonl(output_dir / "ig_gates.jsonl")
    wire_edges = read_jsonl(output_dir / "ig_wire_edges.jsonl")

    fiber_wire = next(w for w in wires if w["wireLevel"] == "fiber")
    occurrence_wires = [w for w in wires if w["wireLevel"] == "occurrence"]
    pattern_wires = [w for w in wires if w["wireLevel"] == "pattern"]

    assert len(occurrence_wires) == 2
    assert fiber_wire["rawBvarId"] == "ig_nodes/x_bvar"
    assert fiber_wire["rawBvarIds"] == ["ig_nodes/x_bvar", "ig_nodes/x_bvar_again"]
    assert fiber_wire["occurrenceCount"] == 2
    assert fiber_wire["binderRawId"] == "ig_nodes/x_lam"
    assert fiber_wire["binderExpr"] == "ig_nodes/x_lam"
    assert fiber_wire["wireKey"] == fiber_wire["_key"]
    assert fiber_wire["deBruijnHash"] == ""
    assert fiber_wire["deBruijnHashes"] == ["h_bvar", "h_bvar_again"]
    assert fiber_wire["incidenceHash"] == ""
    assert fiber_wire["incidenceHashes"] == ["h_incidence", "h_incidence_again"]
    assert len(pattern_wires) == 2
    assert all(w["type"] == "causal_string_pattern" for w in pattern_wires)
    assert all(w["binderKind"] == "binder" for w in pattern_wires)

    const_gate = next(g for g in gates if g["gateKind"] == "const")
    assert const_gate["gateKey"] == const_gate["_key"]
    assert const_gate["operatorName"] == "HMul.hMul"
    assert const_gate["constName"] == "HMul.hMul"
    assert const_gate["constDeclId"] == "ig_nodes/d_hmul"

    roles = {edge["role"] for edge in wire_edges}
    assert "binder_controls_wire" in roles
    assert "wire_occurs_at" in roles
    assert "occurrence_collapses_to_fiber" in roles
    assert "fiber_instantiates_pattern" in roles
    assert any(edge.get("wireRole") == "wire_argument_to_gate" for edge in wire_edges)

    sccs = read_jsonl(output_dir / "ig_scc.jsonl")
    scc_edges = read_jsonl(output_dir / "ig_scc_edges.jsonl")
    assert all(scc["sccPatternHash"].startswith("sha256:") for scc in sccs)
    assert "member_of_scc" in {edge["role"] for edge in scc_edges}

    topologies = read_jsonl(output_dir / "ig_decl_topologies.jsonl")
    hashes = read_jsonl(output_dir / "ig_hashes.jsonl")
    logic_tokens = read_jsonl(output_dir / "ig_logic_tokens.jsonl")

    assert topologies[0]["decl"] == "A.foo"
    assert topologies[0]["ownerAwareHash"].startswith("sha256:")
    assert topologies[0]["patternHash"].startswith("sha256:")
    assert topologies[0]["roleHash"].startswith("sha256:")
    assert {h["hashKind"] for h in hashes} == {"ownerAwareHash", "patternHash", "roleHash"}
    assert "constClass:mul" in {t["value"] for t in logic_tokens}


def test_wire_topology_transform_ignores_malformed_partial_bind_edges(tmp_path: Path) -> None:
    input_dir = tmp_path / "in"
    output_dir = tmp_path / "out"
    input_dir.mkdir()

    write_jsonl(
        input_dir / "ig_nodes.jsonl",
        [
            {"_key": "x_lam", "graphKind": "expr", "exprTag": "lam", "decl": "A.bad", "module": "A"},
            {"_key": "x_bvar", "graphKind": "expr", "exprTag": "bvar", "decl": "A.bad", "module": "A", "deBruijnIdx": 0},
            {"_key": "x_app", "graphKind": "expr", "exprTag": "app", "decl": "A.bad", "module": "A"},
        ],
    )
    write_jsonl(
        input_dir / "ig_edges.jsonl",
        [
            {
                "_key": "e_kind_only",
                "_from": "ig_nodes/x_bvar",
                "_to": "ig_nodes/x_lam",
                "kind": "bind",
                "role": "not_bound_by",
                "decl": "A.bad",
            },
            {
                "_key": "e_role_only",
                "_from": "ig_nodes/x_bvar",
                "_to": "ig_nodes/x_lam",
                "kind": "ast",
                "role": "bound_by",
                "decl": "A.bad",
            },
        ],
    )

    report = transform(input_dir, output_dir)

    assert report["counts"]["ig_wires"] == 0
    assert report["counts"]["ig_wire_edges"] == 0
