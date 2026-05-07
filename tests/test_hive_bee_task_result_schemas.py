from __future__ import annotations

from copy import deepcopy

from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

BASE = {
    "status": "pending",
    "lineage_id": "lineage_bee_demo",
    "revision": 1,
    "origin_run_id": "run_bee_demo",
    "created_at": "2026-05-07T00:00:00Z",
    "updated_at": "2026-05-07T00:00:00Z",
}

AUTHORITY_ORDER = {
    "navigation": 0,
    "semantic": 1,
    "proposal": 2,
    "execution_intent": 3,
    "lean_checked": 4,
    "build_checked": 5,
    "audit_checked": 6,
    "promoted": 7,
}

AUTHORITY_BY_KIND = {
    "SourceObservationPacket": "navigation",
    "SymbolicMotifPacket": "semantic",
    "SocraticQuestionPacket": "semantic",
    "SymbolicSeed": "semantic",
    "FormulationVariant": "semantic",
    "ResonanceCluster": "semantic",
    "PauliCritique": "semantic",
    "InvariantDraft": "semantic",
    "TheoremCandidatePacket": "proposal",
    "TranslationPacket": "proposal",
    "RetrievalHypothesisPacket": "proposal",
    "ResiduePacket": "semantic",
    "ExecutionIntentPacket": "execution_intent",
    "LeanVerificationPacket": "lean_checked",
    "BuildPacket": "build_checked",
    "AuditPacket": "audit_checked",
    "PromotionDecisionPacket": "promoted",
    "AutoproofTracePacket": "proposal",
}


def _errors(packet: dict) -> list[str]:
    store = build_store()
    return validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], store)


def bee_task(**updates: object) -> dict:
    task = {
        **BASE,
        "id": "bee_task_demo",
        "kind": "BeeTask",
        "task_id": "task_demo",
        "status": "pending",
        "assigned_role": "SocratesBee",
        "task_kind": "socratic.question",
        "target_packet_id": "candidate_demo",
        "input_packet_ids": ["candidate_demo"],
        "context_refs": [
            "source_demo",
            {
                "ref": "docs/hive_beehive_swarm_implementation_plan.md",
                "kind": "repo_file",
                "role": "architecture_context",
            },
        ],
        "repulsion_field": ["sha256:" + "a" * 64, "pauli_blocker_demo"],
        "allowed_output_kinds": ["SocraticQuestionPacket", "ResiduePacket"],
        "forbidden_output_kinds": [
            "ExecutionIntentPacket",
            "LeanVerificationPacket",
            "BuildPacket",
            "AuditPacket",
            "PromotionDecisionPacket",
        ],
        "authority_ceiling": "semantic",
        "instruction": "Identify missing hypotheses without raising authority.",
        "priority": 1,
        "store_path": "artifacts/hive/local/packets.jsonl",
        "dry_run": True,
        "timeout_seconds": 60,
    }
    task.update(updates)
    return task


def bee_result(**updates: object) -> dict:
    result = {
        **BASE,
        "id": "bee_result_demo",
        "kind": "BeeResult",
        "task_id": "task_demo",
        "status": "done",
        "worker_id": "socratesbee-local-001",
        "assigned_role": "SocratesBee",
        "input_packet_ids": ["candidate_demo"],
        "output_packet_ids": ["question_demo"],
        "output_packet_hashes": ["sha256:" + "b" * 64],
        "emitted_packet_kinds": ["SocraticQuestionPacket"],
        "artifact_paths": [],
        "commands_run": [],
        "errors": [],
        "authority_claimed": "semantic",
        "promotion_allowed": False,
        "telemetry": {
            "compute_duration_ms": 1450,
            "tokens_consumed": 840,
            "despair_metric": 0.12,
            "phase_similarity_delta": -0.05,
            "semantic_novelty": 0.41,
        },
    }
    result.update(updates)
    return result


def _contract_errors(task: dict, result: dict) -> list[str]:
    errors: list[str] = []
    allowed = set(task.get("allowed_output_kinds", []))
    forbidden = set(task.get("forbidden_output_kinds", []))
    emitted = set(result.get("emitted_packet_kinds", []))
    ceiling = str(task.get("authority_ceiling", ""))
    claimed = str(result.get("authority_claimed", ""))

    if emitted - allowed:
        errors.append("result emitted kind outside task allowed_output_kinds")
    if emitted & forbidden:
        errors.append("result emitted forbidden output kind")
    if AUTHORITY_ORDER.get(claimed, 999) > AUTHORITY_ORDER.get(ceiling, -1):
        errors.append("result authority_claimed exceeds task authority_ceiling")
    for kind in emitted:
        kind_authority = AUTHORITY_BY_KIND.get(kind)
        if kind_authority and AUTHORITY_ORDER[kind_authority] > AUTHORITY_ORDER.get(ceiling, -1):
            errors.append(f"emitted packet kind exceeds authority ceiling: {kind}")
    return errors


def test_bee_task_schema_validates_ephemeral_dispatch_without_authority_field() -> None:
    task = bee_task()

    assert "authority" not in task
    assert _errors(task) == []


def test_bee_task_requires_promotion_decision_in_forbidden_outputs() -> None:
    task = bee_task()
    task["forbidden_output_kinds"] = ["ExecutionIntentPacket", "LeanVerificationPacket"]

    assert any("does not contain items matching" in error for error in _errors(task))


def test_bee_task_repulsion_field_accepts_packet_hashes_and_blocker_ids() -> None:
    task = bee_task(repulsion_field=["sha256:" + "c" * 64, "complex_owner_shadow_gap"])

    assert _errors(task) == []


def test_bee_result_schema_validates_worker_return_receipt() -> None:
    result = bee_result()

    assert _errors(result) == []


def test_autoproof_trace_packet_schema_is_proposal_only_repair_journal() -> None:
    trace = {
        "kind": "AutoproofTracePacket",
        "authority": "proposal",
        "promotion_allowed": False,
        "target": {"goal": "1 = 1", "imports": ["Init"], "context_present": False},
        "budgets": {"max_iterations": 3, "max_repeated_error": 2},
        "result": {"status": "failed", "emitted_packet_kind": "ResiduePacket"},
        "attempts": [
            {
                "attempt_index": 1,
                "mode": "tactic",
                "goal_before": "⊢ 1 = 1",
                "goal_after": "",
                "candidate_text": "exact 0",
                "lean_result": {"accepted": False, "status": "failure", "feedback": "type mismatch"},
                "error_signature": "lean_error:type_mismatch",
                "strategy": "initial_tactic",
                "changed_strategy": False,
                "retrieved_lemmas": [],
            }
        ],
        "frontier": {
            "last_error_signature": "lean_error:type_mismatch",
            "next_recommended_bee": "SocratesBee",
            "new_information_needed": "weaken theorem shape",
        },
    }

    assert _errors(trace) == []


def test_autoproof_trace_packet_rejects_authority_inflation() -> None:
    trace = {
        "kind": "AutoproofTracePacket",
        "authority": "lean_checked",
        "promotion_allowed": False,
        "target": {"goal": "1 = 1", "imports": ["Init"]},
        "budgets": {"max_iterations": 1},
        "result": {"status": "verified", "emitted_packet_kind": "TheoremCandidatePacket"},
        "attempts": [],
        "frontier": {"next_recommended_bee": "none"},
    }

    assert any("'proposal' was expected" in error for error in _errors(trace))


def test_bee_result_rejects_promotion_allowed_true() -> None:
    result = bee_result(promotion_allowed=True)

    assert any("False was expected" in error for error in _errors(result))


def test_bee_result_rejects_malformed_packet_hash() -> None:
    result = bee_result(output_packet_hashes=["not-a-hash"])

    assert any("should match pattern" in error for error in _errors(result))


def test_task_result_contract_accepts_semantic_socrates_result() -> None:
    task = bee_task()
    result = bee_result()

    assert _contract_errors(task, result) == []


def test_task_result_contract_rejects_forbidden_authority_output() -> None:
    task = bee_task()
    result = bee_result(
        emitted_packet_kinds=["LeanVerificationPacket"],
        output_packet_ids=["lean_verification_demo"],
        authority_claimed="lean_checked",
    )

    errors = _contract_errors(task, result)
    assert "result emitted kind outside task allowed_output_kinds" in errors
    assert "result emitted forbidden output kind" in errors
    assert "result authority_claimed exceeds task authority_ceiling" in errors
    assert "emitted packet kind exceeds authority ceiling: LeanVerificationPacket" in errors


def test_task_result_contract_rejects_allowed_but_too_high_authority_kind() -> None:
    task = bee_task(
        allowed_output_kinds=["SocraticQuestionPacket", "ExecutionIntentPacket"],
        forbidden_output_kinds=["LeanVerificationPacket", "BuildPacket", "AuditPacket", "PromotionDecisionPacket"],
    )
    result = bee_result(
        emitted_packet_kinds=["ExecutionIntentPacket"],
        output_packet_ids=["exec_intent_demo"],
        authority_claimed="execution_intent",
    )

    assert "result authority_claimed exceeds task authority_ceiling" in _contract_errors(task, result)
    assert "emitted packet kind exceeds authority ceiling: ExecutionIntentPacket" in _contract_errors(task, result)


def test_invalid_assigned_role_fails_closed() -> None:
    task = bee_task(assigned_role="OmnipotentBee")

    assert any("should be one of" in error for error in _errors(task))
