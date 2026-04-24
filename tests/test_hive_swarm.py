from pathlib import Path
import sys


REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.infra import hive_swarm


def sample_swarm_config() -> hive_swarm.SwarmConfig:
    bee = hive_swarm.hive_bee.BeeConfig(
        hive_endpoint="http://127.0.0.1:8530",
        hive_database="hive_live",
        hive_username="root",
        hive_password="alexandria_root",
        queue_name="proof-search",
        worker_id="swarm-test",
        lease_seconds=600,
        gravity_base_url="http://127.0.0.1:8529",
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
        auditor_override="VERDICT: pass\nPROMOTION_ALLOWED: no\nNOTES: Lean remains the proof authority. The trust boundary stayed intact.",
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


def test_parse_critic_decision_and_auditor_report() -> None:
    critic = hive_swarm.parse_critic_decision("VERDICT: revise\nTACTIC: simp\nREASON: simplify first")
    rejected = hive_swarm.parse_critic_decision("VERDICT: reject\nTACTIC: exact rfl\nREASON: this is wrong")
    nonschema = hive_swarm.parse_critic_decision("### Lean4 Proof Sketch\n```lean4\ntheorem bad : True := by trivial\n```")
    auditor = hive_swarm.parse_auditor_report("VERDICT: conditional_pass\nPROMOTION_ALLOWED: no\nNOTES: Keep Lean as authority.")

    assert critic.verdict == "revise"
    assert critic.tactic == "simp"
    assert rejected.verdict == "reject"
    assert rejected.tactic == ""
    assert nonschema.verdict == "reject"
    assert nonschema.tactic == ""
    assert nonschema.reason == "non-schema critic output"
    assert auditor.verdict == "conditional_pass"
    assert auditor.promotion_allowed == "no"


def test_run_one_success_with_all_roles(monkeypatch, tmp_path: Path) -> None:
    config = sample_swarm_config()
    task = sample_task()
    goal = sample_goal()

    monkeypatch.setattr(hive_swarm, "ARTIFACT_DIR", tmp_path)
    monkeypatch.setattr(hive_swarm.hive_bee, "fetch_claimed_task_and_goal", lambda cfg: (task, goal))
    monkeypatch.setattr(
        hive_swarm.hive_bee,
        "run_gravity_retrieval",
        lambda cfg, goal_doc, task_key: ({"items": [{"id": "Demo.foo"}], "graph_source": "arango", "graph_mode": "faithful"}, tmp_path / "gravity.json", None),
    )
    monkeypatch.setattr(hive_swarm.hive_bee, "get_proof_state", lambda *args, **kwargs: {"status": "ok", "proof_state": "⊢ 1 = 1"})
    monkeypatch.setattr(hive_swarm.hive_bee, "apply_tactic", lambda *args, **kwargs: {"status": "success", "lean": {"ok": True}})
    monkeypatch.setattr(hive_swarm.hive_bee, "fossilize_success", lambda cfg, attempt: {"task": {"status": "completed"}, "goal": {"status": "closed"}, "fossil": {"_key": "f1"}})
    monkeypatch.setattr(hive_swarm.queue_tool, "update_goal_status", lambda *args, **kwargs: {"ok": True})

    result = hive_swarm.run_one(config)

    assert result["status"] == "fossilized"
    assert result["generator_tactic"] == "rfl"
    assert result["critic"]["verdict"] == "approve"
    assert result["auditor"]["verdict"] == "pass"


def test_run_one_critic_rejection_requeues(monkeypatch, tmp_path: Path) -> None:
    config = sample_swarm_config()
    config = hive_swarm.SwarmConfig(
        bee=config.bee,
        generator_override=config.generator_override,
        critic_override="VERDICT: reject\nTACTIC: \nREASON: tactic family is unsafe here",
        auditor_override=config.auditor_override,
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
