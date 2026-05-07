from __future__ import annotations

from copy import deepcopy
from pathlib import Path

from tools.infra.hive_local_packet_store import append_packet
from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
from tools.infra.hive_bee_runner import ROLE_POLICY, RunnerError, run_task
from tools.infra.hive_motherbee import discover_tasks

BASE = {
    "status": "active",
    "lineage_id": "lineage_autoproof_trace_demo",
    "revision": 1,
    "origin_run_id": "run_autoproof_trace_demo",
    "created_at": "2026-05-07T00:00:00Z",
    "updated_at": "2026-05-07T00:00:00Z",
}

FORBIDDEN_AUTHORITY = [
    "ExecutionIntentPacket",
    "LeanVerificationPacket",
    "BuildPacket",
    "AuditPacket",
    "PromotionDecisionPacket",
]


def _errors(packet: dict) -> list[str]:
    return validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], build_store())


def repair_attempt(**updates: object) -> dict:
    packet = {
        **BASE,
        "id": "repair_attempt_demo_1",
        "kind": "RepairAttemptPacket",
        "authority": "proposal",
        "authority_origin": "bounded_autoproof_attempt",
        "promotion_allowed": False,
        "target": {
            "target_packet_id": "candidate_demo",
            "file": "lean/InfoGeometry/Demo.lean",
            "module": "InfoGeometry.Demo",
            "theorem": "demo_theorem",
            "goal_hash": "sha256:" + "a" * 64,
        },
        "episode": {
            "episode_id": "autoproof_episode_demo",
            "task_id": "bee_task_demo",
            "assigned_role": "HermesLeanstralBee",
            "attempt_index": 1,
            "max_iterations": 3,
        },
        "candidate": {
            "candidate_kind": "tactic",
            "candidate_text": "rfl",
            "strategy": "direct_simplification",
            "changed_strategy_from_previous": False,
            "prompt_mode": "tactic",
        },
        "lean_probe": {
            "probe_kind": "lean_interact_wrapper",
            "accepted": True,
            "status": "success",
            "goal_before": "⊢ 1 = 1",
            "goal_after": "",
            "stdout_excerpt": "",
            "stderr_excerpt": "",
            "error_signature": "",
            "diagnostics": [],
        },
        "retrieval_context": {
            "retrieved_lemmas": [],
            "owner_refs": [],
            "source_refs": [],
        },
        "loop_control": {
            "same_error_repeat_count": 0,
            "same_candidate_repeat_count": 0,
            "degeneracy_detected": False,
            "next_action_hint": "emit_candidate",
        },
        "forbidden_uses": [
            "proof",
            "promotion",
            "authority_gate_bypass",
            "LeanVerificationPacket",
        ],
    }
    packet.update(updates)
    return packet


def autoproof_trace(**updates: object) -> dict:
    packet = {
        **BASE,
        "id": "autoproof_trace_demo",
        "kind": "AutoproofTracePacket",
        "authority": "proposal",
        "authority_origin": "bounded_autoproof_episode",
        "promotion_allowed": False,
        "producer": {
            "bee": "HermesLeanstralBee",
            "worker_id": "hermes-leanstral-bee-local-001",
            "model": "leanstral-gguf",
            "endpoint": "local",
            "task_id": "bee_task_demo",
        },
        "target": {
            "target_packet_id": "candidate_demo",
            "file": "lean/InfoGeometry/Demo.lean",
            "module": "InfoGeometry.Demo",
            "theorem": "demo_theorem",
            "owner_refs": [],
        },
        "budgets": {
            "max_iterations": 3,
            "lean_timeout": 60,
            "max_same_error_repeats": 2,
            "max_same_candidate_repeats": 1,
        },
        "result": {
            "status": "success",
            "emitted_packet_kind": "TheoremCandidatePacket",
            "verified_by_local_probe": True,
            "official_lean_verification_packet": None,
        },
        "attempt_packet_ids": ["repair_attempt_demo_1"],
        "frontier": {
            "last_goal_state": "",
            "last_error_signature": "",
            "failed_strategies": [],
            "missing_lemmas": [],
            "promising_lemmas": [],
            "next_recommended_bee": "HermesLeanstralBee",
            "new_information_needed": "",
        },
        "forbidden_authority": FORBIDDEN_AUTHORITY,
    }
    packet.update(updates)
    return packet


def seed_candidate(packet_id: str = "candidate_demo") -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "TheoremCandidatePacket",
        "authority": "proposal",
        "promotion_allowed": False,
        "packet_version": "v1",
        "packet_hash": "pending",
        "status": "probe_ready",
        "symbolic_origin_refs": [{"ref": "seed_demo"}],
        "representation_class": "translator",
        "representation_depth": "scalar",
        "formal_target": {"target_kind": "theorem", "summary": "1 = 1", "candidate_shape": "example : 1 = 1 := by rfl"},
        "bridge_claim": "demo probe",
        "novelty_defense": {"summary": "synthetic test candidate"},
        "repo_anchor_refs": [{"ref": "lean/InfoGeometry/Demo.lean"}],
        "candidate_dependencies": [],
        "admissibility_state": "admissible_for_probe",
        "cost_class": "low",
        "formal_probe": True,
        "lean_goal": "example : 1 = 1 := by rfl",
        "lean_imports": ["Init"],
    }


def leanstral_task(store: Path, allowed: list[str] | None = None) -> dict:
    return {
        **BASE,
        "id": "bee_task_demo",
        "kind": "BeeTask",
        "status": "pending",
        "task_id": "bee_task_demo",
        "assigned_role": "HermesLeanstralBee",
        "task_kind": "leanstral.autoproof",
        "target_packet_id": "candidate_demo",
        "input_packet_ids": ["candidate_demo"],
        "context_refs": ["candidate_demo"],
        "repulsion_field": [],
        "allowed_output_kinds": allowed
        or ["RepairAttemptPacket", "AutoproofTracePacket", "TheoremCandidatePacket", "ResiduePacket"],
        "forbidden_output_kinds": FORBIDDEN_AUTHORITY,
        "authority_ceiling": "proposal",
        "instruction": "Run bounded proof-proposal recurrence and emit attempt/episode trace sidecars.",
        "priority": 30,
        "store_path": str(store),
        "dry_run": False,
        "timeout_seconds": 180,
    }


def test_repair_attempt_packet_validates_as_proposal_attempt_evidence() -> None:
    assert _errors(repair_attempt()) == []


def test_repair_attempt_packet_rejects_promotion_and_lean_checked_authority() -> None:
    promoted = repair_attempt(promotion_allowed=True)
    lean_checked = repair_attempt(authority="lean_checked")

    assert any("False was expected" in error for error in _errors(promoted))
    assert any("'proposal' was expected" in error for error in _errors(lean_checked))


def test_repair_attempt_packet_requires_forbidden_lean_verification_use() -> None:
    packet = repair_attempt(forbidden_uses=["proof", "promotion"])

    assert any("does not contain items matching" in error for error in _errors(packet))


def test_autoproof_trace_packet_validates_episode_aggregate_with_attempt_refs() -> None:
    assert _errors(autoproof_trace()) == []


def test_autoproof_trace_packet_rejects_missing_attempt_refs_and_promotion_allowed() -> None:
    packet = autoproof_trace(attempt_packet_ids=[], promotion_allowed=True)

    errors = _errors(packet)
    assert any("at least 1 items" in error or "should be non-empty" in error or "should not be empty" in error for error in errors)
    assert any("False was expected" in error for error in errors)


def test_autoproof_trace_packet_requires_forbidden_authority_gate_list() -> None:
    packet = autoproof_trace(forbidden_authority=["PromotionDecisionPacket"])

    errors = _errors(packet)
    assert any("ExecutionIntentPacket" in error or "does not contain items matching" in error for error in errors)


def test_hermes_leanstral_policy_allows_attempt_and_trace_packets_but_not_gate_packets() -> None:
    allowed = set(ROLE_POLICY["HermesLeanstralBee"]["allowed_output_kinds"])

    assert {"RepairAttemptPacket", "AutoproofTracePacket", "TheoremCandidatePacket", "ResiduePacket"} <= allowed
    assert not ({"LeanVerificationPacket", "BuildPacket", "AuditPacket", "PromotionDecisionPacket"} & allowed)


def test_motherbee_leanstral_task_allows_trace_sidecars(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    records = [seed_candidate()]
    tasks = discover_tasks(records, store_path=store, dry_run_task=True)
    leanstral_tasks = [task for task in tasks if task["assigned_role"] == "HermesLeanstralBee"]

    assert len(leanstral_tasks) == 1
    assert leanstral_tasks[0]["allowed_output_kinds"] == [
        "RepairAttemptPacket",
        "AutoproofTracePacket",
        "TheoremCandidatePacket",
        "ResiduePacket",
    ]


def test_runner_accepts_hermes_leanstral_attempt_trace_and_candidate_outputs(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, seed_candidate())
    candidate = seed_candidate(packet_id="candidate_output")
    candidate["status"] = "draft"
    task = leanstral_task(store)
    outputs = [repair_attempt(), autoproof_trace(), candidate]

    result = run_task(task, output_packets=outputs, store_path=store, worker_id="hermes-leanstral-bee-local-001")

    assert result["emitted_packet_kinds"] == ["RepairAttemptPacket", "AutoproofTracePacket", "TheoremCandidatePacket"]
    assert result["authority_claimed"] == "proposal"


def test_runner_still_rejects_lean_verification_from_hermes_leanstral(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, seed_candidate())
    task = leanstral_task(store, allowed=["RepairAttemptPacket", "AutoproofTracePacket", "LeanVerificationPacket"])
    bad_output = deepcopy(repair_attempt())
    bad_output.update({"id": "lean_verification_bad", "kind": "LeanVerificationPacket", "authority": "lean_checked"})

    try:
        run_task(task, output_packets=[bad_output], store_path=store, worker_id="hermes-leanstral-bee-local-001")
    except RunnerError as exc:
        assert "not allowed by role policy" in str(exc) or "forbidden" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("HermesLeanstralBee accepted LeanVerificationPacket")
