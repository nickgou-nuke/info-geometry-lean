import json
from pathlib import Path

from tools.alexandria.batch_check_recovered_lean import build_batch_source, load_lean_candidates


def test_batch_check_recovered_lean_builds_namespaced_source(tmp_path: Path) -> None:
    blocks = tmp_path / "recovered_pdf_code_blocks.jsonl"
    blocks.write_text(
        "\n".join(
            [
                json.dumps(
                    {
                        "key": "lean_candidate_one",
                        "language": "lean4",
                        "pageStart": 3,
                        "pageEnd": 3,
                        "text": "import Hidden.Source\ndef two : Nat := 2",
                        "metadata": {"page": 3},
                    }
                ),
                json.dumps(
                    {
                        "key": "python_candidate",
                        "language": "python",
                        "pageStart": 4,
                        "pageEnd": 4,
                        "text": "def f(x):\n    return x",
                    }
                ),
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    candidates = load_lean_candidates(
        blocks,
        max_candidates=0,
        min_page=0,
        max_page=0,
        candidate_keys=set(),
    )
    source = build_batch_source(
        candidates,
        preamble="import Mathlib",
        namespace="PdfRecoveredLean.Test",
        start_index=1,
    )

    assert len(candidates) == 1
    assert "namespace PdfRecoveredLean.Test" in source
    assert "-- skipped recovered import command: import Hidden.Source" in source
    assert "def two : Nat := 2" in source
    assert "python_candidate" not in source
