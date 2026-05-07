from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools.infra import hive_leanstral_bee_worker as worker
from tools.infra.hive_bee_runner import RunnerError
from tools.infra.hive_local_packet_store import append_packet, read_store


def base_task(tmp_path: Path) -> dict:
    now = "2026-01-01T00:00:00Z"
    return {
        "id": "bee_task_leanstral_demo",
        "kind": "BeeTask",
        "status": "pending",
        "lineage_id": "lin-demo",
        "revision": 1,
        "origin_run_id": "run-demo",
        "created_at": now,
        "updated_at": now,
        "task_id": "leanstral_demo",
        "assigned_role": "HermesLeanstralBee",
        "task_kind": "leanstral.autoproof",
        "target_packet_id": "seed-demo",
        "input_packet_ids": ["seed-demo"],
        "allowed_output_kinds": ["TheoremCandidatePacket", "ResiduePacket"],
        "forbidden_output_kinds": [
            "ExecutionIntentPacket",
            "LeanVerificationPacket",
            "BuildPacket",
            "AuditPacket",
            "PromotionDecisionPacket",
        ],
        "authority_ceiling": "proposal",
        "instruction": "Prove goal: 1 = 1",
        "dry_run": False,
        "store_path": str(tmp_path / "store.jsonl"),
        "lean_goal": "1 = 1",
        "lean_imports": ["Init"],
        "max_iterations": 3,
    }


def seed_packet() -> dict:
    now = "2026-01-01T00:00:00Z"
    return {
        "id": "seed-demo",
        "kind": "TheoremCandidatePacket",
        "status": "draft",
        "lineage_id": "lin-demo",
        "revision": 1,
        "origin_run_id": "run-demo",
        "created_at": now,
        "updated_at": now,
        "authority": "proposal",
        "representation_class": "translator",
        "representation_depth": "scalar",
        "packet_version": "v1",
        "packet_hash": "pending",
        "symbolic_origin_refs": [{"ref": "user:demo"}],
        "formal_target": {"target_kind": "lean_goal", "summary": "1 = 1"},
        "bridge_claim": "Demo equality target.",
        "novelty_defense": {"summary": "Fixture only."},
        "repo_anchor_refs": [],
        "candidate_dependencies": [],
        "admissibility_state": "admissible_for_probe",
        "cost_class": "low",
        "promotion_allowed": False,
    }


def fake_verified(goal: str, imports: list[str], max_iterations: int, **kwargs) -> dict:
    return {
        "schema": "hermes_leanstral_autoproof_loop.v1",
        "status": "verified",
        "authority": "proposal_with_lean_evidence",
        "promotion_allowed": False,
        "goal": goal,
        "imports": imports,
        "verified_tactic": "rfl",
        "iterations": [{"iteration": 1, "candidate": "rfl", "lean_ok": True, "lean_status": "success", "lean_stdout": ""}],
        "autoproof_trace": {
            "kind": "AutoproofTracePacket",
            "authority": "proposal",
            "promotion_allowed": False,
            "target": {"goal": goal, "imports": imports},
            "budgets": {"max_iterations": max_iterations},
            "result": {"status": "verified", "emitted_packet_kind": "TheoremCandidatePacket"},
            "attempts": [
                {
                    "attempt_index": 1,
                    "mode": "tactic",
                    "candidate_text": "rfl",
                    "lean_result": {"accepted": True, "status": "success"},
                    "strategy": "initial_tactic",
                    "changed_strategy": False,
                    "error_signature": "",
                }
            ],
            "frontier": {"next_recommended_bee": "none"},
        },
    }


def fake_failed(goal: str, imports: list[str], max_iterations: int, **kwargs) -> dict:
    return {
        "schema": "hermes_leanstral_autoproof_loop.v1",
        "status": "failed",
        "authority": "proposal_with_lean_evidence",
        "promotion_allowed": False,
        "goal": goal,
        "imports": imports,
        "verified_tactic": "",
        "iterations": [
            {"iteration": 1, "candidate": "simp", "lean_ok": False, "lean_status": "error", "lean_stdout": "unsolved goals"},
            {"iteration": 2, "candidate": "omega", "lean_ok": False, "lean_status": "error", "lean_stdout": "unknown tactic"},
        ],
        "autoproof_trace": {
            "kind": "AutoproofTracePacket",
            "authority": "proposal",
            "promotion_allowed": False,
            "target": {"goal": goal, "imports": imports},
            "budgets": {"max_iterations": max_iterations},
            "result": {"status": "failed", "emitted_packet_kind": "ResiduePacket"},
            "attempts": [
                {
                    "attempt_index": 1,
                    "mode": "tactic",
                    "candidate_text": "simp",
                    "lean_result": {"accepted": False, "status": "error"},
                    "strategy": "initial_tactic",
                    "changed_strategy": False,
                    "error_signature": "lean_error:unsolved_goals",
                },
                {
                    "attempt_index": 2,
                    "mode": "repair",
                    "candidate_text": "omega",
                    "lean_result": {"accepted": False, "status": "error"},
                    "strategy": "lean_feedback_repair",
                    "changed_strategy": True,
                    "error_signature": "lean_error:unknown_tactic",
                },
            ],
            "frontier": {
                "last_error_signature": "lean_error:unknown_tactic",
                "next_recommended_bee": "RetrieverBee",
            },
        },
    }


def test_worker_emits_probe_ready_candidate_and_bee_result(tmp_path: Path) -> None:
    store = tmp_path / "store.jsonl"
    append_packet(store, seed_packet())
    task = base_task(tmp_path)

    result = worker.run_worker(task, store_path=store, worker_id="hermes-leanstral-test", autoproof_fn=fake_verified)

    records = read_store(store)
    output = records[-1]
    assert result["status"] == "done"
    assert result["assigned_role"] == "HermesLeanstralBee"
    assert result["authority_claimed"] == "proposal"
    assert result["promotion_allowed"] is False
    assert result["emitted_packet_kinds"] == ["TheoremCandidatePacket"]
    assert output["kind"] == "TheoremCandidatePacket"
    assert output["status"] == "probe_ready"
    assert output["authority"] == "proposal"
    assert output["promotion_allowed"] is False
    assert output["formal_target"]["candidate_shape"] == "by rfl"
    assert output["leanstral_autoproof"]["verified_tactic"] == "rfl"
    assert output["autoproof_trace"]["kind"] == "AutoproofTracePacket"
    assert output["autoproof_trace"]["authority"] == "proposal"
    assert output["autoproof_trace"]["promotion_allowed"] is False
    assert output["autoproof_trace_ref"] == {"packet_id": "autoproof_trace_leanstral_demo", "embedded": True}


def test_worker_emits_residue_after_exhausting_retries(tmp_path: Path) -> None:
    store = tmp_path / "store.jsonl"
    append_packet(store, seed_packet())
    task = base_task(tmp_path)

    result = worker.run_worker(task, store_path=store, worker_id="hermes-leanstral-test", autoproof_fn=fake_failed)

    output = read_store(store)[-1]
    assert result["status"] == "done"
    assert result["emitted_packet_kinds"] == ["ResiduePacket"]
    assert result["authority_claimed"] == "proposal"
    assert output["kind"] == "ResiduePacket"
    assert output["failure_class"] == "proof_obstruction"
    assert output["stage"] == "formal_probe"
    assert "2 attempts" in output["recovery_hint"]
    assert output["leanstral_autoproof"]["status"] == "failed"
    assert output["autoproof_trace"]["result"]["emitted_packet_kind"] == "ResiduePacket"
    assert output["autoproof_trace"]["frontier"]["next_recommended_bee"] == "RetrieverBee"
    assert output["autoproof_trace_ref"] == {"packet_id": "autoproof_trace_leanstral_demo", "embedded": True}


@pytest.mark.parametrize(
    "forbidden_kind",
    [
        "ExecutionIntentPacket",
        "LeanVerificationPacket",
        "BuildPacket",
        "AuditPacket",
        "PromotionDecisionPacket",
    ],
)
def test_worker_rejects_each_authority_gate_output_in_task_contract(tmp_path: Path, forbidden_kind: str) -> None:
    store = tmp_path / "store.jsonl"
    append_packet(store, seed_packet())
    task = base_task(tmp_path)
    task["allowed_output_kinds"] = [forbidden_kind]

    with pytest.raises(RunnerError, match="authority-gate packets"):
        worker.run_worker(task, store_path=store, worker_id="hermes-leanstral-test", autoproof_fn=fake_verified)


def test_worker_rejects_authority_ceiling_above_proposal(tmp_path: Path) -> None:
    store = tmp_path / "store.jsonl"
    append_packet(store, seed_packet())
    task = base_task(tmp_path)
    task["authority_ceiling"] = "lean_checked"

    with pytest.raises(RunnerError, match="authority_ceiling must be proposal"):
        worker.run_worker(task, store_path=store, worker_id="hermes-leanstral-test", autoproof_fn=fake_verified)


def test_worker_success_never_claims_lean_checked_authority(tmp_path: Path) -> None:
    store = tmp_path / "store.jsonl"
    append_packet(store, seed_packet())
    task = base_task(tmp_path)

    result = worker.run_worker(task, store_path=store, worker_id="hermes-leanstral-test", autoproof_fn=fake_verified)
    output = read_store(store)[-1]

    assert result["authority_claimed"] == "proposal"
    assert result["authority_claimed"] != "lean_checked"
    assert output["authority"] == "proposal"
    assert output["kind"] == "TheoremCandidatePacket"
    assert output["kind"] != "LeanVerificationPacket"
    assert output["leanstral_autoproof"]["authority"] == "proposal_with_lean_evidence"
    assert output["promotion_allowed"] is False


def test_worker_dry_run_appends_nothing(tmp_path: Path) -> None:
    store = tmp_path / "store.jsonl"
    append_packet(store, seed_packet())
    task = base_task(tmp_path)
    task["dry_run"] = True

    result = worker.run_worker(task, store_path=store, worker_id="hermes-leanstral-test", autoproof_fn=fake_verified)

    records = read_store(store)
    assert len(records) == 1
    assert records[0]["id"] == "seed-demo"
    assert result["status"] == "done"
    assert result["telemetry"]["dry_run"] is True
    assert result["emitted_packet_kinds"] == ["TheoremCandidatePacket"]
    assert result["promotion_allowed"] is False


def test_worker_requires_all_authority_gate_kinds_to_be_forbidden(tmp_path: Path) -> None:
    store = tmp_path / "store.jsonl"
    append_packet(store, seed_packet())
    for gate_kind in sorted(worker.AUTHORITY_GATE_KINDS):
        task = base_task(tmp_path)
        task["task_id"] = f"leanstral_missing_forbidden_{gate_kind}"
        task["id"] = f"bee_task_missing_forbidden_{gate_kind}"
        task["forbidden_output_kinds"] = [kind for kind in task["forbidden_output_kinds"] if kind != gate_kind]

        try:
            worker.run_worker(task, store_path=store, worker_id="hermes-leanstral-test", autoproof_fn=fake_verified)
        except Exception as exc:
            assert "must explicitly forbid authority-gate packets" in str(exc)
            assert gate_kind in str(exc)
        else:  # pragma: no cover
            raise AssertionError(f"expected missing forbidden gate rejection for {gate_kind}")
