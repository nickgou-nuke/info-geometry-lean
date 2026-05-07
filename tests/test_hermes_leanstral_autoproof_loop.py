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


def test_autoproof_records_lean_dojo_style_repair_attempt_trace() -> None:
    candidates = iter(["exact 0", "rfl"])

    def proposer(prompt: loop.ProofPrompt) -> dict[str, object]:
        return {"status": "ok", "candidate": next(candidates), "raw_candidate": "raw"}

    result = loop.run_autoproof(
        goal="1 = 1",
        imports=["Init"],
        max_iterations=3,
        proposer=proposer,
        lean_checker=fake_lean,
    )

    trace = result["autoproof_trace"]
    assert trace["kind"] == "AutoproofTracePacket"
    assert trace["authority"] == "proposal"
    assert trace["promotion_allowed"] is False
    assert trace["budgets"]["max_iterations"] == 3
    assert trace["result"]["status"] == "verified"
    assert [attempt["attempt_index"] for attempt in trace["attempts"]] == [1, 2]
    assert trace["attempts"][0]["mode"] == "tactic"
    assert trace["attempts"][0]["candidate_text"] == "exact 0"
    assert trace["attempts"][0]["lean_result"]["accepted"] is False
    assert trace["attempts"][0]["error_signature"].startswith("lean_error:")
    assert trace["attempts"][1]["mode"] == "repair"
    assert trace["attempts"][1]["lean_result"]["accepted"] is True


def test_autoproof_marks_strategy_switch_after_repeated_error_signature() -> None:
    def proposer(prompt: loop.ProofPrompt) -> dict[str, object]:
        return {"status": "ok", "candidate": "exact 0", "raw_candidate": "exact 0"}

    result = loop.run_autoproof(
        goal="1 = 1",
        imports=["Init"],
        max_iterations=3,
        proposer=proposer,
        lean_checker=fake_lean,
    )

    trace = result["autoproof_trace"]
    assert result["status"] == "failed"
    assert [attempt["lean_result"]["accepted"] for attempt in trace["attempts"]] == [False, False, False]
    assert trace["attempts"][1]["changed_strategy"] is True
    assert trace["attempts"][1]["strategy"] == "changed_strategy_after_repeated_error"
    assert trace["frontier"]["last_error_signature"].startswith("lean_error:")
    assert trace["frontier"]["next_recommended_bee"] in {"RetrieverBee", "SocratesBee", "PauliBee"}


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
