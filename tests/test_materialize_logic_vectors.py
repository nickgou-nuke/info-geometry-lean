import json
from pathlib import Path

from tools.infra.materialize_logic_vectors import materialize


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_materialize_logic_vectors_builds_deterministic_feature_rows(tmp_path: Path) -> None:
    wire_dir = tmp_path / "wire"
    rdf_dir = tmp_path / "rdf"
    out_dir = tmp_path / "out"

    write_jsonl(
        wire_dir / "ig_decl_topologies.jsonl",
        [
            {
                "decl": "A.foo",
                "module": "A",
                "ownerAwareHash": "sha256:owner",
                "patternHash": "sha256:pattern",
                "roleHash": "sha256:role",
                "patternHashTokens": ["constClass:mul", "edge.role:arg"],
            }
        ],
    )
    write_jsonl(
        wire_dir / "ig_hashes.jsonl",
        [{"decl": "A.foo", "module": "A", "hashKind": "patternHash", "hash": "sha256:pattern"}],
    )
    write_jsonl(
        wire_dir / "ig_logic_tokens.jsonl",
        [{"decl": "A.foo", "module": "A", "hashKind": "patternHash", "value": "constClass:mul", "multiplicity": 2}],
    )
    write_jsonl(
        wire_dir / "ig_scc.jsonl",
        [
            {
                "sccPatternHash": "sha256:scc",
                "decls": ["A.foo"],
                "dominantGateClasses": ["mul"],
            }
        ],
    )
    write_jsonl(
        rdf_dir / "ig_triples.jsonl",
        [
            {
                "decl": "A.foo",
                "kind": "deBruijn_binding",
                "predicate": "bound_by:deBruijnIdx=0",
                "incidenceHash": "sha256:inc",
            }
        ],
    )
    write_jsonl(
        rdf_dir / "ig_binder_incidence.jsonl",
        [
            {
                "decl": "A.foo",
                "binderIncidenceHash": "sha256:binder",
                "bound_bvar_count": 1,
                "binder_expr_tag": "lam",
            }
        ],
    )

    report1 = materialize(wire_dir, rdf_dir, out_dir, dimension=16)
    rows1 = read_jsonl(out_dir / "ig_logic_vectors.jsonl")
    docs1 = read_jsonl(out_dir / "ig_text_index_docs.jsonl")
    report2 = materialize(wire_dir, rdf_dir, out_dir, dimension=16)
    rows2 = read_jsonl(out_dir / "ig_logic_vectors.jsonl")

    assert report1["counts"] == {"ig_logic_vectors": 1, "ig_text_index_docs": 1}
    assert report2["counts"] == report1["counts"]
    assert rows1 == rows2
    assert rows1[0]["decl"] == "A.foo"
    assert rows1[0]["dimension"] == 16
    assert len(rows1[0]["logicVector"]) == 16
    assert rows1[0]["identity"]["patternHash"] == "sha256:pattern"
    assert rows1[0]["features"]["logicToken:constClass:mul"] == 2.0
    assert rows1[0]["features"]["rdf.predicate:bound_by:deBruijnIdx=0"] == 1.0
    assert rows1[0]["features"]["binderIncidenceHash:sha256:binder"] == 1.0
    assert rows1[0]["truthBoundary"] == "derived vector shadow; exact evidence remains RDF/deBruijn/wire graph"
    assert docs1[0]["reviewOnly"] is True
    assert docs1[0]["logicVector"] == rows1[0]["logicVector"]
