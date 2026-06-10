from argparse import Namespace
from pathlib import Path

from tools.alexandria.artifact_ast_lint import process_artifact


def test_artifact_ast_lint_extracts_candidates_and_flags_authority_claims(tmp_path: Path) -> None:
    source = tmp_path / "paper.md"
    source.write_text(
        r"""
# Candidate Paper

This paragraph claims zero sorries and kernel-verified closure.

\begin{theorem}
This intentionally has no closing environment.

```lean
theorem candidate_truth : True := by
  trivial
```

```python
def symbolic_step(x):
    return x + 1
```
""",
        encoding="utf-8",
    )

    args = Namespace(
        source_format="auto",
        max_chars=512,
        no_bind_proofs=False,
        check_lean_candidates=False,
        lean_preamble="",
        lean_timeout=5,
        no_check_python_candidates=False,
    )

    rows = process_artifact(source, args)

    candidates = rows["artifact_code_candidates"]
    findings = rows["artifact_lint_findings"]
    codes = {finding["code"] for finding in findings}

    assert len(rows["alexandria_chunks"]) >= 1
    assert {candidate["language"] for candidate in candidates} == {"lean4", "python"}
    assert next(candidate for candidate in candidates if candidate["language"] == "python")[
        "validationStatus"
    ] == "passed"
    assert next(candidate for candidate in candidates if candidate["language"] == "lean4")[
        "validationStatus"
    ] == "not_checked"
    assert "authority_claim_requires_kernel_evidence" in codes
    assert "lean_candidate_not_kernel_checked" in codes
    assert "latex_unclosed_environment" in codes
    assert rows["artifact_purification_requests"]
