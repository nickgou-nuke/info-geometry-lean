import json
from pathlib import Path

from tools.infra.leansearch_local import (
    build_records,
    build_source_records,
    query_tokens,
    search_records,
    tokenize,
)


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_tokenize_keeps_lean_identifier_words() -> None:
    assert tokenize("SamePositiveRay normalized_shape") == ["samepositiveray", "normalized_shape"]


def test_query_tokens_split_lean_identifiers() -> None:
    assert query_tokens("finitePrimonPartition_eq_evaluatedWeylDenominator_inv") == [
        "finiteprimonpartition_eq_evaluatedweyldenominator_inv",
        "finite",
        "primon",
        "partition",
        "eq",
        "evaluated",
        "weyl",
        "denominator",
        "inv",
    ]


def test_build_records_and_search_rank_local_declarations(tmp_path: Path) -> None:
    lean_file = tmp_path / "Example.lean"
    lean_file.write_text(
        "\n".join(
            [
                "namespace Example",
                "/-- Scale invariance of normalized projective shapes. -/",
                "theorem normalizedShape_scale_counts : True := by",
                "  trivial",
                "end Example",
            ]
        ),
        encoding="utf-8",
    )
    decls = tmp_path / "decls.jsonl"
    types = tmp_path / "types.jsonl"
    records = tmp_path / "records.jsonl"
    _write_jsonl(
        decls,
        [
            {
                "name": "Example.normalizedShape_scale_counts",
                "kind": "theorem",
                "module": "Example",
                "file": str(lean_file),
                "line": 3,
                "doc": "Scale invariance of normalized projective shapes.",
            },
            {
                "name": "Example.unrelated",
                "kind": "def",
                "module": "Example",
                "file": str(lean_file),
                "line": 1,
                "doc": "A tiny unrelated helper.",
            },
        ],
    )
    _write_jsonl(
        types,
        [
            {
                "declName": "Example.normalizedShape_scale_counts",
                "typeStr": "normalizedShape counts = normalizedShape scaledCounts",
            }
        ],
    )

    summary = build_records(decls_path=decls, types_path=types, out_path=records)
    result = search_records(records_path=records, query="normalized scale projective", top_k=2)

    assert summary["records"] == 2
    assert result["hits"][0]["name"] == "Example.normalizedShape_scale_counts"
    assert result["hits"][0]["kind"] == "theorem"
    assert "normalizedShape_scale_counts" in result["hits"][0]["snippet"]


def test_search_exact_lean_identifier_query_matches_split_record_tokens(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    _write_jsonl(
        records,
        [
            {
                "schema": "info_geometry.leansearch_local.record.v1",
                "name": "Example.finitePrimeGasPartition_eq_weylDenominator_inv",
                "kind": "theorem",
                "module": "Example",
                "file": "Example.lean",
                "line": 7,
                "doc": "Finite prime gas partition is the inverse Weyl denominator.",
                "type": "",
                "snippet": "theorem finitePrimeGasPartition_eq_weylDenominator_inv : True := by trivial",
                "nameTokens": [
                    "example",
                    "finite",
                    "prime",
                    "gas",
                    "partition",
                    "eq",
                    "weyl",
                    "denominator",
                    "inv",
                ],
                "searchTokens": [
                    "example",
                    "finite",
                    "prime",
                    "gas",
                    "partition",
                    "eq",
                    "weyl",
                    "denominator",
                    "inv",
                ],
            },
            {
                "schema": "info_geometry.leansearch_local.record.v1",
                "name": "Example.finitePrimonPartition_eq_evaluatedWeylDenominator_inv",
                "kind": "theorem",
                "module": "Example",
                "file": "Example.lean",
                "line": 11,
                "doc": "",
                "type": "",
                "snippet": "theorem finitePrimonPartition_eq_evaluatedWeylDenominator_inv : True := by trivial",
                "nameTokens": [
                    "example",
                    "finite",
                    "primon",
                    "partition",
                    "eq",
                    "evaluated",
                    "weyl",
                    "denominator",
                    "inv",
                ],
                "searchTokens": [
                    "example",
                    "finite",
                    "primon",
                    "partition",
                    "eq",
                    "evaluated",
                    "weyl",
                    "denominator",
                    "inv",
                ],
            }
        ],
    )

    result = search_records(
        records_path=records,
        query="finitePrimonPartition_eq_evaluatedWeylDenominator_inv",
        top_k=1,
    )

    assert result["hits"][0]["name"] == "Example.finitePrimonPartition_eq_evaluatedWeylDenominator_inv"


def test_build_source_records_from_external_lean_root(tmp_path: Path) -> None:
    source_root = tmp_path / "spin"
    dag_dir = source_root / "DAG"
    dag_dir.mkdir(parents=True)
    lean_file = dag_dir / "BlockDecomposition.lean"
    lean_file.write_text(
        "\n".join(
            [
                "namespace DAG.BlockDecomposition",
                "structure BlockDecomp where",
                "  dim : Nat",
                "theorem dimensionsOf_eq : True := by",
                "  trivial",
                "end DAG.BlockDecomposition",
            ]
        ),
        encoding="utf-8",
    )
    records = tmp_path / "source_records.jsonl"

    summary = build_source_records(source_roots=[source_root], out_path=records)
    result = search_records(records_path=records, query="dimensionsOf_eq", top_k=1)

    assert summary["schema"] == "info_geometry.leansearch_local.source_build_summary.v1"
    assert summary["records"] == 2
    assert result["hits"][0]["schema"] == "info_geometry.leansearch_local.source_record.v1"
    assert result["hits"][0]["name"] == "DAG.BlockDecomposition.dimensionsOf_eq"
    assert result["hits"][0]["module"] == "DAG.BlockDecomposition"
    assert result["hits"][0]["doc"] == ""
