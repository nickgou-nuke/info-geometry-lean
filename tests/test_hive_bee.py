import json
from pathlib import Path
import sys


REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.infra import hive_bee


def sample_config() -> hive_bee.BeeConfig:
    return hive_bee.BeeConfig(
        hive_endpoint="http://127.0.0.1:8530",
        hive_database="hive_live",
        hive_username="root",
        hive_password="alexandria_root",
        queue_name="proof-search",
        worker_id="test-bee",
        lease_seconds=600,
        gravity_base_url="http://127.0.0.1:8529",
        gravity_database="infogeometry",
        gravity_top_k=4,
        model_base_url="http://127.0.0.1:30002/v1",
        model_name="deepseek-prover-v2-7b-q8_0.gguf",
        api_key="test-key",
        timeout=30,
        tactic_override=None,
    )


def sample_goal() -> dict:
    return {
        "_key": "goal_123",
        "goal_hash_shape": "abc123",
        "target_pretty": "1 = 1",
        "canonical_shape": "Eq 1 1",
        "module": "Demo",
        "entity_key": "Demo:0",
        "imports": ["Init"],
        "lean_context": "",
        "max_attempts": 2,
    }


def sample_task() -> dict:
    return {
        "_key": "task_123",
        "goal_key": "goal_123",
        "claim_count": 1,
        "queue_name": "proof-search",
    }


def test_extract_tactic_supports_label_and_fenced_blocks() -> None:
    assert hive_bee.extract_tactic("TACTIC: exact rfl\nRATIONALE: trivial") == "exact rfl"
    assert hive_bee.extract_tactic("```lean\nrfl\n```") == "rfl"


def test_generated_theorem_source_indexes_verified_fossil() -> None:
    theorem_name, source = hive_bee.generated_theorem_source(sample_goal(), sample_task(), "rfl")

    assert theorem_name == "hive_Demo_task_123"
    assert "import Init" in source
    assert "import InfoGeometry.Meta.HiveLogos" in source
    assert "theorem hive_Demo_task_123 : 1 = 1 := by" in source
    assert "  rfl" in source
    assert "#hive_index_decl hive_Demo_task_123" in source


def test_build_deadend_doc_captures_recirculation_memory() -> None:
    doc = hive_bee.build_deadend_doc(
        sample_goal(),
        sample_task(),
        worker_id="bee-a",
        tactic="exact 0",
        failure_kind="lean_verification_failure",
        verification={"lean": {"stdout": "", "stderr": "error: mismatch"}},
        gravity_path=Path("/tmp/gravity.json"),
        elapsed_wall_s=1.25,
        lean_latency_s=0.75,
    )

    assert doc["failure_kind"] == "lean_verification_failure"
    assert doc["attempted_tactic_family"] == "exact"
    assert doc["retry_policy"]["max_attempts"] == 2
    assert doc["metabolic_cost"]["lean_verification_latency_s"] == 0.75
    assert doc["state_taxonomy"] == ["retrieved", "proposed", "checked", "deadend"]


def test_run_one_success_fossilizes(monkeypatch) -> None:
    config = sample_config()
    events: list[tuple[str, dict]] = []
    task = sample_task()
    goal = sample_goal()

    monkeypatch.setattr(hive_bee, "fetch_claimed_task_and_goal", lambda cfg: (task, goal))
    monkeypatch.setattr(
        hive_bee,
        "run_gravity_retrieval",
        lambda cfg, goal_doc, task_key: ({"items": [{"id": "Demo.foo"}], "graph_source": "arango"}, Path("/tmp/gravity.json"), None),
    )
    monkeypatch.setattr(hive_bee, "get_proof_state", lambda *args, **kwargs: {"status": "ok", "proof_state": "⊢ 1 = 1"})
    monkeypatch.setattr(hive_bee, "propose_tactic", lambda *args, **kwargs: "rfl")
    monkeypatch.setattr(hive_bee, "apply_tactic", lambda *args, **kwargs: {"status": "success", "lean": {"ok": True, "stdout": "", "stderr": ""}})
    monkeypatch.setattr(hive_bee, "fossilize_success", lambda cfg, attempt: {"fossil": {"_key": "fossil_1"}})
    monkeypatch.setattr(hive_bee.queue_tool, "update_goal_status", lambda *args, **kwargs: events.append(("goal_status", kwargs)) or {"ok": True})

    result = hive_bee.run_one(config)

    assert result["status"] == "fossilized"
    assert result["tactic"] == "rfl"
    assert any(item[0] == "goal_status" and item[1]["status"] == "retrieved" for item in events)
    assert any(item[0] == "goal_status" and item[1]["status"] == "checked" for item in events)


def test_run_one_failure_requeues_before_max_attempts(monkeypatch) -> None:
    config = sample_config()
    task = sample_task()
    goal = sample_goal()
    calls: list[tuple[str, dict]] = []

    monkeypatch.setattr(hive_bee, "fetch_claimed_task_and_goal", lambda cfg: (task, goal))
    monkeypatch.setattr(
        hive_bee,
        "run_gravity_retrieval",
        lambda cfg, goal_doc, task_key: ({"items": [{"id": "Demo.foo"}], "graph_source": "arango"}, Path("/tmp/gravity.json"), None),
    )
    monkeypatch.setattr(hive_bee, "get_proof_state", lambda *args, **kwargs: {"status": "ok", "proof_state": "⊢ 1 = 1"})
    monkeypatch.setattr(hive_bee, "propose_tactic", lambda *args, **kwargs: "exact 0")
    monkeypatch.setattr(hive_bee, "apply_tactic", lambda *args, **kwargs: {"status": "failure", "lean": {"ok": False, "stdout": "", "stderr": "error: bad tactic"}})
    monkeypatch.setattr(hive_bee, "record_deadend", lambda cfg, attempt, failure_kind: {"deadend": {"_key": "dead_1"}})
    monkeypatch.setattr(hive_bee.queue_tool, "requeue_task", lambda *args, **kwargs: calls.append(("requeue", kwargs)) or {"status": "pending"})
    monkeypatch.setattr(hive_bee.queue_tool, "update_goal_status", lambda *args, **kwargs: calls.append(("goal_status", kwargs)) or {"ok": True})

    result = hive_bee.run_one(config)

    assert result["status"] == "requeued"
    assert any(name == "requeue" for name, _ in calls)
    assert any(name == "goal_status" and payload["status"] == "requeued" for name, payload in calls)
