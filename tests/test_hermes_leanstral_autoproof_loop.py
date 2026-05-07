from __future__ import annotations

import json
from pathlib import Path

from tools.infra import hermes_leanstral_autoproof_loop as loop


def fake_lean(goal: str, tactic: str, *, imports: list[str], context: str, timeout: int) -> dict:
    ok = tactic.strip() == "rfl"
    return {
        "status": "success" if ok else "failure",
        "goal": goal,
        "tactic": tactic,
        "imports": imports,
        "context": context,
        "proof_state_before": "⊢ 1 = 1",
        "lean": {
            "ok": ok,
            "returncode": 0 if ok else 1,
            "stdout": "⊢ 1 = 1\n",
            "stderr": "" if ok else "error: type mismatch\n",
        },
    }


def test_autoproof_stops_after_first_verified_candidate() -> None:
    calls: list[str] = []

    def proposer(prompt: loop.ProofPrompt) -> dict[str, object]:
        calls.append(prompt.kind)
        return {"status": "ok", "candidate": "rfl", "raw_candidate": "rfl"}

    result = loop.run_autoproof(
        goal="1 = 1",
        imports=["Init"],
        max_iterations=3,
        proposer=proposer,
        lean_checker=fake_lean,
    )

    assert calls == ["initial"]
    assert result["schema"] == "hermes_leanstral_autoproof_loop.v1"
    assert result["status"] == "verified"
    assert result["authority"] == "proposal_with_lean_evidence"
    assert result["promotion_allowed"] is False
    assert result["verified_tactic"] == "rfl"
    assert result["iterations"][0]["lean_status"] == "success"


def test_autoproof_repairs_after_lean_error() -> None:
    candidates = iter(["exact 0", "rfl"])
    prompts: list[loop.ProofPrompt] = []

    def proposer(prompt: loop.ProofPrompt) -> dict[str, object]:
        prompts.append(prompt)
        return {"status": "ok", "candidate": next(candidates), "raw_candidate": "raw"}

    result = loop.run_autoproof(
        goal="1 = 1",
        imports=["Init"],
        max_iterations=3,
        proposer=proposer,
        lean_checker=fake_lean,
    )

    assert [prompt.kind for prompt in prompts] == ["initial", "repair"]
    assert "type mismatch" in prompts[1].lean_feedback
    assert result["status"] == "verified"
    assert result["verified_tactic"] == "rfl"
    assert [item["candidate"] for item in result["iterations"]] == ["exact 0", "rfl"]


def test_autoproof_returns_failed_without_promotion_when_exhausted() -> None:
    def proposer(prompt: loop.ProofPrompt) -> dict[str, object]:
        return {"status": "ok", "candidate": "exact 0", "raw_candidate": "exact 0"}

    result = loop.run_autoproof(
        goal="1 = 1",
        imports=["Init"],
        max_iterations=2,
        proposer=proposer,
        lean_checker=fake_lean,
    )

    assert result["status"] == "failed"
    assert result["verified_tactic"] is None
    assert result["promotion_allowed"] is False
    assert len(result["iterations"]) == 2


def test_cli_fake_candidates_prints_json(tmp_path: Path, capsys) -> None:
    candidates = tmp_path / "candidates.json"
    candidates.write_text(json.dumps(["exact 0", "rfl"]), encoding="utf-8")

    code = loop.main(
        [
            "--goal",
            "1 = 1",
            "--import",
            "Init",
            "--max-iterations",
            "2",
            "--fake-candidates",
            str(candidates),
        ],
        lean_checker=fake_lean,
    )

    captured = capsys.readouterr()
    payload = json.loads(captured.out)
    assert code == 0
    assert payload["status"] == "verified"
    assert payload["verified_tactic"] == "rfl"
