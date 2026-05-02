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


def sample_attempt() -> hive_bee.BeeAttempt:
    return hive_bee.BeeAttempt(
        task=sample_task(),
        goal=sample_goal(),
        proof_state={"status": "ok", "proof_state": "⊢ 1 = 1"},
        gravity_context={
            "items": [
                {
                    "id": "Demo.owner",
                    "module": "Demo",
                    "score": 1.0,
                    "faithful_witness": {"scc_key": "scc_1", "raw_doc_id": "raw_1"},
                }
            ],
            "graph_source": "arango",
        },
        gravity_path=Path("/tmp/gravity.json"),
        proposed_tactic="rfl",
        verification={"status": "success", "lean": {"stdout": "ok", "stderr": ""}},
        elapsed_wall_s=1.5,
        lean_latency_s=0.25,
    )


def test_extract_tactic_supports_label_and_fenced_blocks() -> None:
    assert hive_bee.extract_tactic("TACTIC: exact rfl\nRATIONALE: trivial") == "exact rfl"
    assert hive_bee.extract_tactic("```lean\nrfl\n```") == "rfl"
    assert hive_bee.extract_tactic("```lean4\nrfl\n```") == "rfl"
    assert hive_bee.extract_tactic("### Lean4 tactic proof\nTACTIC: rfl\nRATIONALE: trivial") == "rfl"
    assert hive_bee.extract_tactic("### Lean4 tactic proof\nRATIONALE: bad\n") == ""
    assert hive_bee.extract_tactic("```lean4\ntheorem t : 1 = 1 := by\n  rfl\n```") == "rfl"
    assert hive_bee.extract_tactic("TACTIC: theorem t : 1 = 1 := by exact rfl") == "exact rfl"


def test_generated_theorem_source_indexes_verified_fossil() -> None:
    theorem_name, source = hive_bee.generated_theorem_source(sample_goal(), sample_task(), "rfl")

    assert theorem_name == "hive_Demo_task_123"
    assert "import Init" in source
    assert "import InfoGeometry.Meta.HiveLogos" in source
    assert "theorem hive_Demo_task_123 : 1 = 1 := by" in source
    assert "  rfl" in source
    assert "#hive_index_decl hive_Demo_task_123" in source


def test_build_deadend_doc_captures_recirculation_memory() -> None:
    gravity_context = {
        "items": [
            {
                "id": "InfoGeometry.Canonical.Demo.foo",
                "module": "InfoGeometry.Canonical.Demo",
                "score": 321.0,
                "faithful_witness": {"scc_key": "scc_demo", "raw_doc_id": "raw_demo"},
            }
        ]
    }
    doc = hive_bee.build_deadend_doc(
        sample_goal(),
        sample_task(),
        worker_id="bee-a",
        tactic="exact 0",
        failure_kind="lean_verification_failure",
        verification={"lean": {"stdout": "", "stderr": "error: unknown constant InfoGeometry.Canonical.Demo.foo"}},
        gravity_path=Path("/tmp/gravity.json"),
        elapsed_wall_s=1.25,
        lean_latency_s=0.75,
        gravity_context=gravity_context,
    )

    assert doc["failure_kind"] == "lean_verification_failure"
    assert doc["attempted_tactic_family"] == "exact"
    assert doc["retry_policy"]["max_attempts"] == 2
    assert doc["metabolic_cost"]["lean_verification_latency_s"] == 0.75
    assert doc["state_taxonomy"] == ["retrieved", "proposed", "checked", "deadend"]
    assert doc["blocked_by_dependency"]["candidate_id"] == "InfoGeometry.Canonical.Demo.foo"


def test_build_replay_packet_contains_required_audit_fields() -> None:
    attempt = hive_bee.BeeAttempt(
        task=sample_task(),
        goal=sample_goal(),
        proof_state={"proof_state": "⊢ 1 = 1"},
        gravity_context={"items": [{"id": "Demo.foo", "module": "Demo", "score": 10.0, "faithful_witness": {"scc_key": "scc1", "raw_doc_id": "raw1"}}]},
        gravity_path=Path("/tmp/gravity.json"),
        proposed_tactic="rfl",
        verification={"status": "success", "lean": {"stdout": "trace", "stderr": ""}},
        elapsed_wall_s=2.0,
        lean_latency_s=0.5,
    )
    packet = hive_bee.build_replay_packet(
        attempt,
        worker_id="bee-a",
        fossil_doc={"_key": "fossil_1", "created_at": "2026-01-01T00:00:00Z"},
        theorem_name="hive_Demo_task_123",
        theorem_source="theorem hive_Demo_task_123 : 1 = 1 := by\n  rfl\n",
        generated_lean_output="HIVE_JSON ...",
    )

    assert packet["generated_theorem_name"] == "hive_Demo_task_123"
    assert packet["goal_key"] == "goal_123"
    assert packet["task_key"] == "task_123"
    assert packet["fossil_key"] == "fossil_1"
    assert packet["gravity_neighbors"][0]["id"] == "Demo.foo"
    assert packet["proof_state_before"] == "⊢ 1 = 1"
    assert packet["tactic_trace"][0]["tactic"] == "rfl"
    assert packet["lean_output"]["generated_theorem_check"] == "HIVE_JSON ..."


def test_build_replay_packet_captures_declaration_indexed_fossil_context() -> None:
    fossil_doc = {
        "_key": "fossil_1",
        "created_at": "2026-04-22T00:00:00Z",
    }
    packet = hive_bee.build_replay_packet(
        sample_attempt(),
        worker_id="bee-a",
        fossil_doc=fossil_doc,
        theorem_name="hive_Demo_task_123",
        theorem_source="theorem hive_Demo_task_123 : 1 = 1 := by\n  rfl\n#hive_index_decl hive_Demo_task_123\n",
        generated_lean_output='HIVE_JSON {"artifactKind":"DiamondFossil"}',
    )

    assert packet["schema"] == "info_geometry.hive_replay_packet.v1"
    assert packet["goal_key"] == "goal_123"
    assert packet["task_key"] == "task_123"
    assert packet["fossil_key"] == "fossil_1"
    assert packet["generated_theorem_name"] == "hive_Demo_task_123"
    assert "#hive_index_decl hive_Demo_task_123" in packet["theorem_source"]
    assert packet["gravity_neighbors"][0]["scc_key"] == "scc_1"
    assert packet["proof_state_before"] == "⊢ 1 = 1"
    assert packet["tactic_trace"][0]["tactic"] == "rfl"
    assert packet["lean_output"]["generated_theorem_check"].startswith("HIVE_JSON")
    assert packet["metabolic_cost"]["gravity_neighbors_count"] == 1
    assert "created_at" in packet["timestamps"]


def test_fossilize_success_persists_replay_packet(monkeypatch, tmp_path) -> None:
    config = sample_config()
    attempt = sample_attempt()
    imports: list[tuple[str, list[dict]]] = []

    record = {
        "artifact_kind": "DiamondFossil",
        "space": "logos",
        "entity_key": "hive.Demo.task_123",
        "canonical_shape": "1 = 1",
        "packet_sha256": "abc",
        "shape_sha256": "shape",
        "source": "hive-bee:hive_Demo_task_123",
        "line_number": 1,
        "packet_index": 0,
        "packet": {
            "artifactKind": "DiamondFossil",
            "constName": "hive.Demo.task_123",
            "declarationKind": "theorem",
            "kernelStatus": "verified",
            "conclusionPretty": "1 = 1",
            "fullTypePretty": "1 = 1",
            "axiomsUsed": [],
        },
    }

    monkeypatch.setattr(
        hive_bee,
        "run_generated_theorem_capture",
        lambda *args, **kwargs: (
            "hive_Demo_task_123",
            "theorem hive_Demo_task_123 : 1 = 1 := by\n  rfl\n#hive_index_decl hive_Demo_task_123\n",
            'HIVE_JSON {"artifactKind":"DiamondFossil"}',
            [record],
        ),
    )
    monkeypatch.setattr(hive_bee, "write_replay_packet_artifact", lambda packet: tmp_path / "replay.json")
    monkeypatch.setattr(
        hive_bee.queue_tool,
        "import_rows",
        lambda endpoint, database, username, password, collection, rows: imports.append((collection, rows)),
    )
    monkeypatch.setattr(hive_bee.queue_tool, "update_goal_status", lambda *args, **kwargs: {"status": kwargs["status"]})
    monkeypatch.setattr(hive_bee.queue_tool, "complete_task", lambda *args, **kwargs: {"status": "done"})

    result = hive_bee.fossilize_success(config, attempt)

    assert result["generated_theorem_name"] == "hive_Demo_task_123"
    assert result["replay_packet"]["schema"] == "info_geometry.hive_replay_packet.v1"
    assert any(collection == "hive_replay_packets" for collection, _ in imports)
    replay_rows = [rows for collection, rows in imports if collection == "hive_replay_packets"][0]
    assert replay_rows[0]["fossil_key"] == result["fossil"]["_key"]
    assert "#hive_index_decl hive_Demo_task_123" in replay_rows[0]["theorem_source"]


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


def test_run_retrieval_dispatches_to_leansearch(monkeypatch) -> None:
    config = sample_config()
    config = hive_bee.BeeConfig(**{**config.__dict__, "retrieval_strategy": "leansearch"})
    goal = sample_goal()
    monkeypatch.setattr(
        hive_bee,
        "run_leansearch_retrieval",
        lambda cfg, goal_doc, task_key: ({"graph_source": "leansearch", "items": []}, Path("/tmp/ls.json"), None),
    )

    payload, path, err = hive_bee.run_retrieval(config, goal, "task_1")

    assert err is None
    assert payload is not None
    assert payload["graph_source"] == "leansearch"
    assert str(path).endswith("ls.json")


def test_emit_attempt_packets_marks_leansearch_source_lane(monkeypatch) -> None:
    config = sample_config()
    imports: list[dict] = []

    def fake_emit_packet(cfg, packet, task_key=None, dependencies=None):
        imports.append(packet)
        return {"packet": {**packet, "packet_key": f"p-{len(imports)}"}}

    monkeypatch.setattr(hive_bee, "emit_packet", fake_emit_packet)

    out = hive_bee.emit_attempt_packets(
        config,
        goal=sample_goal(),
        task=sample_task(),
        gravity_context={"graph_source": "leansearch", "items": []},
        gravity_path=Path("/tmp/leansearch.json"),
        proof_state={"proof_state": "⊢ 1 = 1"},
        tactic="rfl",
        verification=None,
        emit_proposal=False,
    )

    assert out["retrieval"]["source_lane"] == "leansearch"


def test_run_retrieval_hybrid_merges_and_dedupes(monkeypatch) -> None:
    config = sample_config()
    config = hive_bee.BeeConfig(**{**config.__dict__, "retrieval_strategy": "hybrid"})
    goal = sample_goal()

    monkeypatch.setattr(
        hive_bee,
        "run_gravity_retrieval",
        lambda cfg, goal_doc, task_key: (
            {"graph_source": "arango", "edge_count": 3, "items": [{"id": "A.B"}, {"id": "C.D"}]},
            Path("/tmp/gravity.json"),
            None,
        ),
    )
    monkeypatch.setattr(
        hive_bee,
        "run_leansearch_retrieval",
        lambda cfg, goal_doc, task_key: (
            {"graph_source": "leansearch", "items": [{"id": "C.D"}, {"id": "E.F"}]},
            Path("/tmp/leansearch.json"),
            None,
        ),
    )

    payload, path, err = hive_bee.run_retrieval(config, goal, "task_hybrid")

    assert err is None
    assert payload is not None
    assert payload["graph_source"] == "hybrid"
    assert payload["node_count"] == 3
    assert [item["id"] for item in payload["items"]] == ["A.B", "C.D", "E.F"]
    assert payload["components"]["gravity"]["ok"] is True
    assert payload["components"]["leansearch"]["ok"] is True
    assert str(path).endswith("-hybrid.json")


def test_emit_attempt_packets_marks_hybrid_source_lane(monkeypatch) -> None:
    config = sample_config()
    imports: list[dict] = []

    def fake_emit_packet(cfg, packet, task_key=None, dependencies=None):
        imports.append(packet)
        return {"packet": {**packet, "packet_key": f"p-{len(imports)}"}}

    monkeypatch.setattr(hive_bee, "emit_packet", fake_emit_packet)

    out = hive_bee.emit_attempt_packets(
        config,
        goal=sample_goal(),
        task=sample_task(),
        gravity_context={"graph_source": "hybrid", "items": []},
        gravity_path=Path("/tmp/hybrid.json"),
        proof_state={"proof_state": "⊢ 1 = 1"},
        tactic="rfl",
        verification=None,
        emit_proposal=False,
    )

    assert out["retrieval"]["source_lane"] == "hybrid"
