from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.infra.hive_bee_runner import (
    RunnerError,
    run_task,
    validate_result_contract,
)
from tools.infra.hive_local_packet_store import append_packet, packet_hash, read_store

SCRIPT = Path("tools/infra/hive_bee_runner.py")

BASE = {
    "lineage_id": "lineage_runner_demo",
    "revision": 1,
    "origin_run_id": "run_runner_demo",
    "created_at": "2026-05-07T00:00:00Z",
    "updated_at": "2026-05-07T00:00:00Z",
}


def source_packet(packet_id: str) -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "SourceObservationPacket",
        "status": "captured",
        "authority": "navigation",
        "authority_origin": "source_observation",
        "epistemic_layer": "raw_source",
        "cognitive_function": "sensation",
        "jung_function": "sensation",
        "jung_attitude": "extraverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "source_type": "repo_file",
        "source_uri": f"docs/demo/{packet_id}.md",
        "capture_method": "test_fixture",
        "content_hash": f"sha256:{packet_id}",
        "summary": f"Observed source {packet_id}.",
        "allowed_uses": ["citation", "retrieval", "source_grounding"],
        "forbidden_uses": ["proof", "promotion", "authority_gate_bypass"],
    }


def socratic_packet(packet_id: str, parent: str = "src_input") -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "SocraticQuestionPacket",
        "status": "open",
        "authority": "semantic",
        "authority_origin": "socratic_interrogation",
        "epistemic_layer": "cognitive_process",
        "cognitive_function": "thinking",
        "jung_function": "thinking",
        "jung_attitude": "introverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "representation_class": "shadow",
        "representation_depth": "categorical",
        "parent_refs": [parent],
        "question": "What missing hypothesis blocks this route?",
        "question_type": "hidden_hypothesis",
        "target_packet_ids": [parent],
        "allowed_uses": ["critique", "hypothesis_extraction", "candidate_refinement"],
        "forbidden_uses": ["proof", "promotion", "verification_claim", "theorem_status_rewrite"],
    }


def execution_intent_packet(packet_id: str, parent: str = "src_input") -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "ExecutionIntentPacket",
        "status": "probe_ready",
        "authority": "execution_intent",
        "packet_version": "v1",
        "packet_hash": f"sha256:{packet_id}:intent",
        "target_refs": [{"ref": parent}],
        "intended_actions": ["formalize_candidate", "gather_dependencies"],
        "required_tools": ["lean"],
        "required_gates": ["lean_checked", "build_checked", "audit_checked"],
        "mutation_scope": "none",
        "execution_allowed": False,
        "authority_origin": "lean_wrapper",
        "epistemic_layer": "common_unconscious",
        "cognitive_function": "thinking",
        "jung_function": "thinking",
        "jung_attitude": "introverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "representation_class": "translator",
        "representation_depth": "categorical",
        "allowed_uses": ["retrieval", "formalization", "intent_routing"],
        "forbidden_uses": ["proof", "promotion", "authority_gate_bypass"],
    }


def lean_verification_packet(packet_id: str, intent_id: str = "exec_intent") -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "LeanVerificationPacket",
        "status": "passed",
        "authority": "lean_checked",
        "authority_origin": "lean_wrapper",
        "packet_version": "v1",
        "packet_hash": f"sha256:{packet_id}:leanv",
        "execution_intent_ref": {"ref": intent_id},
        "execution_allowed": True,
        "verification_key": f"verification-key-{packet_id}",
        "kernel_summary": "all goals solved",
        "verification_outcome": "passed",
        "proof_status": "verified",
        "representation_class": "owner",
        "representation_depth": "scalar",
        "epistemic_layer": "lean_topology",
        "cognitive_function": "thinking",
        "jung_function": "thinking",
        "jung_attitude": "introverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "allowed_uses": ["verification"],
        "forbidden_uses": ["revision", "promotion", "authority_gate_bypass"],
    }


def build_packet(packet_id: str, verification_id: str = "lv_input") -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "BuildPacket",
        "status": "executed",
        "authority": "build_checked",
        "authority_origin": "build_gate",
        "packet_version": "v1",
        "packet_hash": f"sha256:{packet_id}:build",
        "lean_verification_ref": {"ref": verification_id},
        "build_key": f"build-key-{packet_id}",
        "build_command": "lake build",
        "build_exit_code": 0,
        "build_success": True,
        "representation_class": "coherence",
        "representation_depth": "scalar",
        "epistemic_layer": "packet_lineage",
        "cognitive_function": "thinking",
        "jung_function": "thinking",
        "jung_attitude": "introverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "allowed_uses": ["build_verification"],
        "forbidden_uses": ["proof", "promotion", "authority_gate_bypass"],
    }


def residue_packet(packet_id: str, parent: str = "src_input") -> dict:
    return {
        **BASE,
        "id": packet_id,
        "kind": "ResiduePacket",
        "status": "active",
        "authority": "proposal",
        "authority_origin": "socratic_interrogation",
        "packet_version": "v1",
        "packet_hash": f"sha256:{packet_id}:residue",
        "failure_refs": [{"ref": parent}],
        "failure_class": "build_failure",
        "stage": "packet_legalization",
        "recovery_hint": "reroute to retrieval",
        "return_route": "retrieval",
        "representation_class": "shadow",
        "representation_depth": "categorical",
        "epistemic_layer": "cognitive_process",
        "cognitive_function": "intuition",
        "jung_function": "intuition",
        "jung_attitude": "introverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "allowed_uses": ["failure_analysis", "reroute"],
        "forbidden_uses": ["proof", "promotion", "authority_gate_bypass"],
    }


def build_bee_task(
    *,
    input_packet_id: str = "lv_input",
    dry_run: bool = False,
    authority_ceiling: str = "build_checked",
) -> dict:
    task = {
        **BASE,
        "id": "bee_task_build_runner_demo",
        "kind": "BeeTask",
        "task_id": "task_build_runner_demo",
        "status": "pending",
        "assigned_role": "BuildBee",
        "task_kind": "build.verify",
        "target_packet_id": input_packet_id,
        "input_packet_ids": [input_packet_id],
        "context_refs": [input_packet_id],
        "repulsion_field": ["pauli_blocker_demo"],
        "allowed_output_kinds": ["BuildPacket", "ResiduePacket"],
        "forbidden_output_kinds": ["ExecutionIntentPacket", "LeanVerificationPacket", "AuditPacket", "PromotionDecisionPacket"],
        "authority_ceiling": authority_ceiling,
        "instruction": "Compile and summarize build artifacts for the Lean verification.",
        "priority": 2,
        "store_path": "unused-in-direct-test.jsonl",
        "dry_run": dry_run,
    }
    return task


def bee_task(*, dry_run: bool = False, allowed_output_kinds: list[str] | None = None, forbidden_output_kinds: list[str] | None = None, authority_ceiling: str = "semantic") -> dict:
    return {
        **BASE,
        "id": "bee_task_runner_demo",
        "kind": "BeeTask",
        "task_id": "task_runner_demo",
        "status": "pending",
        "assigned_role": "SocratesBee",
        "task_kind": "socratic.question",
        "target_packet_id": "src_input",
        "input_packet_ids": ["src_input"],
        "context_refs": ["src_input"],
        "repulsion_field": ["pauli_blocker_demo"],
        "allowed_output_kinds": allowed_output_kinds or ["SocraticQuestionPacket", "ResiduePacket"],
        "forbidden_output_kinds": forbidden_output_kinds
        or ["ExecutionIntentPacket", "LeanVerificationPacket", "BuildPacket", "AuditPacket", "PromotionDecisionPacket"],
        "authority_ceiling": authority_ceiling,
        "instruction": "Generate one Socratic question from the source packet.",
        "priority": 1,
        "store_path": "unused-in-direct-test.jsonl",
        "dry_run": dry_run,
    }


def write_json(tmp_path: Path, name: str, data: dict) -> Path:
    path = tmp_path / name
    path.write_text(json.dumps(data, sort_keys=True), encoding="utf-8")
    return path


def run_cli(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def test_runner_appends_schema_validated_allowed_output_and_returns_bee_result(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    output = socratic_packet("question_output")

    result = run_task(bee_task(), store_path=store, output_packets=[output], worker_id="socratesbee-test")

    assert result["kind"] == "BeeResult"
    assert result["status"] == "done"
    assert result["output_packet_ids"] == ["question_output"]
    assert result["output_packet_hashes"] == [packet_hash(output)]
    assert result["authority_claimed"] == "semantic"
    assert output["pipeline_state"] == "proposed"
    records = read_store(store)
    assert [record["id"] for record in records] == ["src_input", "question_output"]


def test_runner_dry_run_validates_but_writes_no_output_packet(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    output = socratic_packet("question_dry_run")

    result = run_task(bee_task(dry_run=True), store_path=store, output_packets=[output], worker_id="socratesbee-test")

    assert result["telemetry"]["dry_run"] is True
    assert result["output_packet_ids"] == ["question_dry_run"]
    assert [record["id"] for record in read_store(store)] == ["src_input"]


def test_runner_rejects_missing_input_packet(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"

    try:
        run_task(bee_task(), store_path=store, output_packets=[socratic_packet("question")], worker_id="socratesbee-test")
    except RunnerError as exc:
        assert "missing input packets" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected missing input rejection")


def test_runner_rejects_invalid_output_before_append(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    invalid = socratic_packet("bad_question")
    invalid.pop("question")

    try:
        run_task(bee_task(), store_path=store, output_packets=[invalid], worker_id="socratesbee-test")
    except Exception as exc:  # noqa: BLE001 - StoreError through validation boundary
        assert "failed schema validation" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected invalid output rejection")
    assert [record["id"] for record in read_store(store)] == ["src_input"]


def test_runner_rejects_pipeline_regression_from_checked_to_proposed(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, lean_verification_packet("lv_input", intent_id="src_input"))
    task = bee_task()
    task["input_packet_ids"] = ["lv_input"]
    task["target_packet_id"] = "lv_input"
    task["context_refs"] = ["lv_input"]

    try:
        run_task(task, store_path=store, output_packets=[socratic_packet("question_regression")], worker_id="socratesbee-test")
    except RunnerError as exc:
        assert "invalid pipeline transition" in str(exc)
        assert "checked -> proposed" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected checked→proposed transition rejection")


def test_runner_allows_blocked_branch_from_idle_via_residue_packet(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    output = residue_packet("residue_output", parent="src_input")
    blocked_task = bee_task(authority_ceiling="proposal")
    blocked_task["assigned_role"] = "RetrieverBee"
    blocked_task["task_kind"] = "retrieval.context"

    result = run_task(blocked_task, store_path=store, output_packets=[output], worker_id="retrieverbee-test")

    assert result["output_packet_ids"] == ["residue_output"]
    assert result["authority_claimed"] == "proposal"
    assert output["pipeline_state"] == "blocked"
    records = read_store(store)
    assert [record["id"] for record in records] == ["src_input", "residue_output"]


def test_runner_accepts_checked_to_audited_progression(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, lean_verification_packet("lv_input", intent_id="src_input"))
    output = build_packet("build_output", verification_id="lv_input")

    result = run_task(
        build_bee_task(input_packet_id="lv_input"),
        store_path=store,
        output_packets=[output],
        worker_id="buildbee-test",
    )

    assert result["output_packet_ids"] == ["build_output"]
    assert output["pipeline_state"] == "audited"
    assert [record["id"] for record in read_store(store)] == ["lv_input", "build_output"]


def test_runner_rejects_forbidden_output_kind(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))

    try:
        run_task(bee_task(), store_path=store, output_packets=[execution_intent_packet("exec_jump")], worker_id="socratesbee-test")
    except RunnerError as exc:
        assert "output kind not allowed" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected forbidden output rejection")
    assert [record["id"] for record in read_store(store)] == ["src_input"]


def test_runner_rejects_allowed_kind_above_authority_ceiling(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    task = bee_task(
        allowed_output_kinds=["SocraticQuestionPacket", "ExecutionIntentPacket"],
        forbidden_output_kinds=["LeanVerificationPacket", "BuildPacket", "AuditPacket", "PromotionDecisionPacket"],
        authority_ceiling="semantic",
    )

    try:
        run_task(task, store_path=store, output_packets=[execution_intent_packet("exec_too_high")], worker_id="socratesbee-test")
    except RunnerError as exc:
        assert "not allowed by role policy" in str(exc) or "exceeds BeeTask ceiling" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected authority ceiling rejection")


def test_cli_writes_bee_result_and_appends_output(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    task_path = write_json(tmp_path, "task.json", {**bee_task(), "store_path": str(store)})
    output_path = write_json(tmp_path, "question.json", socratic_packet("question_cli"))
    result_path = tmp_path / "result.json"

    result = run_cli(
        "run",
        "--task",
        str(task_path),
        "--emit-packet",
        str(output_path),
        "--worker-id",
        "socratesbee-cli",
        "--result",
        str(result_path),
    )

    assert result.returncode == 0, result.stderr
    written = json.loads(result_path.read_text(encoding="utf-8"))
    assert written["output_packet_ids"] == ["question_cli"]
    assert [record["id"] for record in read_store(store)] == ["src_input", "question_cli"]


def test_cli_dry_run_writes_no_output_packet(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    task_path = write_json(tmp_path, "task.json", {**bee_task(), "store_path": str(store)})
    output_path = write_json(tmp_path, "question.json", socratic_packet("question_cli_dry"))

    result = run_cli(
        "run",
        "--task",
        str(task_path),
        "--emit-packet",
        str(output_path),
        "--worker-id",
        "socratesbee-cli",
        "--dry-run",
    )

    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout)["telemetry"]["dry_run"] is True
    assert [record["id"] for record in read_store(store)] == ["src_input"]


def test_runner_rejects_role_task_kind_mismatch(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    task = bee_task()
    task["assigned_role"] = "LeanBee"
    task["task_kind"] = "socratic.question"

    try:
        run_task(task, store_path=store, output_packets=[socratic_packet("question_role")], worker_id="leanbee-test")
    except RunnerError as exc:
        assert "not compatible with assigned_role" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected role/task-kind mismatch rejection")


def test_result_contract_rejects_hash_mismatch() -> None:
    task = bee_task()
    output = socratic_packet("question_contract")
    result = {
        **BASE,
        "id": "bee_result_contract",
        "kind": "BeeResult",
        "task_id": task["task_id"],
        "status": "done",
        "worker_id": "socratesbee-contract",
        "assigned_role": task["assigned_role"],
        "input_packet_ids": task["input_packet_ids"],
        "output_packet_ids": [output["id"]],
        "output_packet_hashes": ["sha256:" + "0" * 64],
        "emitted_packet_kinds": [output["kind"]],
        "authority_claimed": "semantic",
        "promotion_allowed": False,
        "telemetry": {},
    }

    try:
        validate_result_contract(task, result, [output])
    except RunnerError as exc:
        assert "output_packet_hashes do not match" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected result hash mismatch rejection")


def test_result_contract_rejects_promotion_allowed_true() -> None:
    task = bee_task()
    output = socratic_packet("question_contract_promotion")
    result = {
        **BASE,
        "id": "bee_result_contract_promotion",
        "kind": "BeeResult",
        "task_id": task["task_id"],
        "status": "done",
        "worker_id": "socratesbee-contract",
        "assigned_role": task["assigned_role"],
        "input_packet_ids": task["input_packet_ids"],
        "output_packet_ids": [output["id"]],
        "output_packet_hashes": [packet_hash(output)],
        "emitted_packet_kinds": [output["kind"]],
        "authority_claimed": "semantic",
        "promotion_allowed": True,
        "telemetry": {},
    }

    try:
        validate_result_contract(task, result, [output])
    except RunnerError as exc:
        assert "promotion_allowed must be false" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected promotion_allowed rejection")


def test_runner_rejects_output_outside_role_policy_even_when_task_allows_it(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, execution_intent_packet("src_input"))
    task = bee_task(allowed_output_kinds=["SocraticQuestionPacket", "SourceObservationPacket"])
    output = source_packet("source_not_socrates")
    output["pipeline_state"] = "checked"

    try:
        run_task(task, store_path=store, output_packets=[output], worker_id="socratesbee-test")
    except RunnerError as exc:
        assert "not allowed by role policy" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected role-policy output rejection")


def test_runner_rejects_leanbee_without_execution_intent_input(tmp_path: Path) -> None:
    store = tmp_path / "packets.jsonl"
    append_packet(store, source_packet("src_input"))
    task = bee_task(
        allowed_output_kinds=["LeanVerificationPacket"],
        forbidden_output_kinds=["BuildPacket", "AuditPacket", "PromotionDecisionPacket"],
        authority_ceiling="lean_checked",
    )
    task["assigned_role"] = "LeanBee"
    task["task_kind"] = "lean.verify"

    try:
        run_task(task, store_path=store, output_packets=[], worker_id="leanbee-test")
    except RunnerError as exc:
        assert "requires input kinds" in str(exc)
        assert "ExecutionIntentPacket" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected missing ExecutionIntentPacket rejection")
