import json
from pathlib import Path

from tools.infra.leansearch_local import build_records, search_records, tokenize


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_tokenize_keeps_lean_identifier_words() -> None:
    assert tokenize("SamePositiveRay normalized_shape") == ["samepositiveray", "normalized_shape"]


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
