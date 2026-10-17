from pathlib import Path
import sys


REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.infra import hive_swarm


def sample_swarm_config() -> hive_swarm.SwarmConfig:
    bee = hive_swarm.hive_bee.BeeConfig(
        hive_endpoint="http://127.0.0.1:8540",
        hive_database="hive_live",
        hive_username="root",
        hive_password="alexandria_root",
        queue_name="proof-search",
        worker_id="swarm-test",
        lease_seconds=600,
        gravity_base_url="http://127.0.0.1:8530",
        gravity_database="infogeometry",
        gravity_top_k=4,
        model_base_url="http://127.0.0.1:30002/v1",
        model_name="deepseek-prover-v2-7b-q8_0.gguf",
        api_key="test-key",
        backend_kind="local_openai_compatible",
        backend_identity="http://127.0.0.1:30002/v1",
        subscription_backed=False,
        backend_capability="proof_tactic_proposal",
        hermes_role="hive_proof_bee",
        allow_direct_provider_api=False,
        timeout=30,
        tactic_override=None,
    )
    return hive_swarm.SwarmConfig(
        bee=bee,
        generator_override="TACTIC: rfl\nRATIONALE: trivial reflexive goal",
        critic_override="VERDICT: approve\nTACTIC: rfl\nREASON: the tactic exactly closes the reflexive goal",
    )


def sample_goal() -> dict:
    return {
        "_key": "goal_123",
        "target_pretty": "1 = 1",
        "canonical_shape": "1 = 1",
        "module": "Demo",
        "entity_key": "Demo:0",
        "imports": ["Init"],
        "lean_context": "",
        "max_attempts": 2,
    }


def sample_task() -> dict:
    return {"_key": "task_123", "goal_key": "goal_123", "claim_count": 1, "queue_name": "proof-search"}


def test_parse_critic_decision() -> None:
    critic = hive_swarm.parse_critic_decision("VERDICT: revise\nTACTIC: simp\nREASON: simplify first")
    rejected = hive_swarm.parse_critic_decision("VERDICT: reject\nTACTIC: exact rfl\nREASON: this is wrong")
    nonschema = hive_swarm.parse_critic_decision("### Lean4 Proof Sketch\n```lean4\ntheorem bad : True := by trivial\n```")

    assert critic.verdict == "revise"
    assert critic.tactic == "simp"
    assert rejected.verdict == "reject"
    assert rejected.tactic == ""
    assert nonschema.verdict == "reject"
    assert nonschema.tactic == ""
    assert nonschema.reason == "non-schema critic output"
def test_run_one_success_leaves_qms_acceptance_pending(monkeypatch, tmp_path: Path) -> None:
    config = sample_swarm_config()
    task = sample_task()
    goal = sample_goal()
    goal_updates = []
    roles = []

    monkeypatch.setattr(hive_swarm, "ARTIFACT_DIR", tmp_path)
    monkeypatch.setattr(hive_swarm.hive_bee, "fetch_claimed_task_and_goal", lambda cfg: (task, goal))
    monkeypatch.setattr(
        hive_swarm.hive_bee,
        "run_gravity_retrieval",
        lambda cfg, goal_doc, task_key: ({"items": [{"id": "Demo.foo"}], "graph_source": "arango", "graph_mode": "faithful"}, tmp_path / "gravity.json", None),
    )
    monkeypatch.setattr(hive_swarm.hive_bee, "get_proof_state", lambda *args, **kwargs: {"status": "ok", "proof_state": "⊢ 1 = 1"})
    monkeypatch.setattr(hive_swarm.hive_bee, "apply_tactic", lambda *args, **kwargs: {"status": "success", "lean": {"ok": True}})
    monkeypatch.setattr(
        hive_swarm.hive_bee,
        "fossilize_success",
        lambda cfg, attempt: {
            "task": {"status": "completed"},
            "goal": {
                "status": "closed",
                "qms_acceptance_status": "pending_external_audit",
                "qms_a_a_required": True,
                "qms_qa_a_required": True,
            },
            "fossil": {"_key": "f1"},
        },
    )
    original_call_role_model = hive_swarm.call_role_model
    monkeypatch.setattr(
        hive_swarm,
        "call_role_model",
        lambda cfg, role, *args, **kwargs: roles.append(role) or original_call_role_model(cfg, role, *args, **kwargs),
    )
    monkeypatch.setattr(
        hive_swarm.queue_tool,
        "update_goal_status",
        lambda *args, **kwargs: goal_updates.append(kwargs) or {"ok": True},
    )

    result = hive_swarm.run_one(config)

    assert result["status"] == "proof_fossilized_qms_pending"
    assert result["generator_tactic"] == "rfl"
    assert result["critic"]["verdict"] == "approve"
    assert roles == ["generator", "critic"]
    assert result["qms_review_status"] == "pending_external_audit"
    assert goal_updates[-1]["status"] == "closed"
    assert result["goal"]["qms_acceptance_status"] == "pending_external_audit"
    assert "qms_acceptance_status" not in goal_updates[-1]["extra_fields"]
    assert "auditor_verdict" not in goal_updates[-1]["extra_fields"]
    import json
    artifact = json.loads(Path(result["artifact"]).read_text(encoding="utf-8"))
    assert artifact["proof_fossil_key"] == "f1"
    assert artifact["qms_review"]["status"] == "pending_external_audit"
    assert artifact["qms_review"]["a_a_required"] is True
    assert "auditor" not in artifact


def test_run_one_critic_rejection_requeues(monkeypatch, tmp_path: Path) -> None:
    config = sample_swarm_config()
    config = hive_swarm.SwarmConfig(
        bee=config.bee,
        generator_override=config.generator_override,
        critic_override="VERDICT: reject\nTACTIC: \nREASON: tactic family is unsafe here",
    )
    task = sample_task()
    goal = sample_goal()
    events = []

    monkeypatch.setattr(hive_swarm, "ARTIFACT_DIR", tmp_path)
    monkeypatch.setattr(hive_swarm.hive_bee, "fetch_claimed_task_and_goal", lambda cfg: (task, goal))
    monkeypatch.setattr(
        hive_swarm.hive_bee,
        "run_gravity_retrieval",
        lambda cfg, goal_doc, task_key: ({"items": [{"id": "Demo.foo"}], "graph_source": "arango", "graph_mode": "faithful"}, tmp_path / "gravity.json", None),
    )
    monkeypatch.setattr(hive_swarm.hive_bee, "get_proof_state", lambda *args, **kwargs: {"status": "ok", "proof_state": "⊢ 1 = 1"})
    monkeypatch.setattr(hive_swarm.queue_tool, "import_rows", lambda *args, **kwargs: None)
    monkeypatch.setattr(hive_swarm.queue_tool, "requeue_task", lambda *args, **kwargs: events.append(("requeue", kwargs)) or {"status": "pending"})
    monkeypatch.setattr(hive_swarm.queue_tool, "update_goal_status", lambda *args, **kwargs: events.append(("goal", kwargs)) or {"ok": True})

    result = hive_swarm.run_one(config)

    assert result["status"] == "critic_rejected"
    assert any(name == "requeue" for name, _ in events)
    assert result["critic"]["verdict"] == "reject"
    assert result["qms_review_status"] == "not_run"
    assert "auditor" not in result


def test_run_one_lean_failure_does_not_fossilize_or_accept(monkeypatch, tmp_path: Path) -> None:
    config = sample_swarm_config()
    task = sample_task()
    goal = sample_goal()
    events = []

    monkeypatch.setattr(hive_swarm, "ARTIFACT_DIR", tmp_path)
    monkeypatch.setattr(hive_swarm.hive_bee, "fetch_claimed_task_and_goal", lambda cfg: (task, goal))
    monkeypatch.setattr(
        hive_swarm.hive_bee,
        "run_gravity_retrieval",
        lambda cfg, goal_doc, task_key: ({"items": [], "graph_source": "arango", "graph_mode": "faithful"}, tmp_path / "gravity.json", None),
    )
    monkeypatch.setattr(hive_swarm.hive_bee, "get_proof_state", lambda *args, **kwargs: {"status": "ok", "proof_state": "⊢ 1 = 2"})
    monkeypatch.setattr(hive_swarm.hive_bee, "apply_tactic", lambda *args, **kwargs: {"status": "error", "lean": {"ok": False}})
    monkeypatch.setattr(hive_swarm.hive_bee, "fossilize_success", lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError("must not fossilize")))
    monkeypatch.setattr(hive_swarm.hive_bee, "record_deadend", lambda *args, **kwargs: {"_key": "deadend-1"})
    monkeypatch.setattr(hive_swarm.queue_tool, "import_rows", lambda *args, **kwargs: None)
    monkeypatch.setattr(hive_swarm.queue_tool, "requeue_task", lambda *args, **kwargs: events.append(("requeue", kwargs)) or {"status": "pending"})
    monkeypatch.setattr(hive_swarm.queue_tool, "update_goal_status", lambda *args, **kwargs: events.append(("goal", kwargs)) or {"ok": True})

    result = hive_swarm.run_one(config)

    assert result["status"] == "requeued"
    assert result["qms_review_status"] == "not_run"
    assert all("auditor_verdict" not in item[1].get("extra_fields", {}) for item in events if item[0] == "goal")
