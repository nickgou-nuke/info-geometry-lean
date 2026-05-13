import json
from pathlib import Path

from tools.infra.build_dual_graph import run


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_build_dual_graph_wrapper_emits_integrated_wire_schema(tmp_path: Path) -> None:
    input_dir = tmp_path / "in"
    output_dir = tmp_path / "out"

    write_jsonl(
        input_dir / "ig_nodes.jsonl",
        [
            {"_key": "x_lam", "graphKind": "expr", "exprTag": "lam", "decl": "A.foo", "module": "A"},
            {
                "_key": "x_bvar",
                "graphKind": "expr",
                "exprTag": "bvar",
                "decl": "A.foo",
                "module": "A",
                "deBruijnIdx": 0,
                "deBruijnHash": "sha256:bvar",
            },
        ],
    )
    write_jsonl(
        input_dir / "ig_edges.jsonl",
        [
            {
                "_key": "e_bind",
                "_from": "ig_nodes/x_bvar",
                "_to": "ig_nodes/x_lam",
                "kind": "bind",
                "role": "bound_by",
                "decl": "A.foo",
                "deBruijnIdx": 0,
                "incidenceHash": "sha256:inc",
            }
        ],
    )

    report = run(input_dir, output_dir)
    wires = read_jsonl(output_dir / "ig_wires.jsonl")
    sccs = read_jsonl(output_dir / "ig_scc.jsonl")

    assert report["truth_boundary"] == "derived projection; raw Lean evidence remains ig_nodes/ig_edges"
    assert {wire["wireLevel"] for wire in wires} == {"occurrence", "fiber", "pattern"}
    assert all(wire["kind"] == "wire" for wire in wires)
    assert sccs
    assert all("sccPatternHash" in scc for scc in sccs)
