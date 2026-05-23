import json
from pathlib import Path
import sys


REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.infra import hive_arango_queue as queue_tool


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text("".join(json.dumps(record, ensure_ascii=False) + "\n" for record in records), encoding="utf-8")


def test_build_goal_task_and_event_docs_from_infotree_record(tmp_path: Path) -> None:
    record = {
        "schema": "info_geometry.hive_memory.v1",
        "source": "unit-test",
        "line_number": 2,
        "packet_index": 0,
        "artifact_kind": "InfoTreeArtifact",
        "space": "infotree",
        "entity_key": "Demo:0",
        "canonical_shape": "(forall (bvar 0) (bvar 1))",
        "packet_sha256": "a" * 64,
        "shape_sha256": "b" * 64,
        "packet": {
            "module": "Demo",
            "goalIndex": 0,
            "targetPretty": "P → P",
            "normalizationPolicy": "instantiateMVars+whnf(default)",
            "fvarPolicy": "used-fvars-in-local-context-order",
        },
    }

    event_doc = queue_tool.build_event_doc(record)
    goal_doc = queue_tool.build_goal_doc(record, queue_name="proof-search")
    task_doc = queue_tool.build_task_doc(goal_doc, queue_name="proof-search", priority=0.9)
    task_edge = queue_tool.build_task_edge(task_doc, goal_doc)
    event_edge = queue_tool.build_event_edge(event_doc, "hive_goals", goal_doc["_key"])

    assert event_doc["artifact_kind"] == "InfoTreeArtifact"
    assert goal_doc["goal_hash_shape"] == "b" * 64
    assert goal_doc["target_pretty"] == "P → P"
    assert task_doc["goal_key"] == goal_doc["_key"]
    assert task_doc["status"] == "pending"
    assert task_doc["priority"] == 0.9
    assert task_edge["_from"] == f"hive_tasks/{task_doc['_key']}"
    assert task_edge["_to"] == f"hive_goals/{goal_doc['_key']}"
    assert event_edge["_to"] == f"hive_goals/{goal_doc['_key']}"


def test_build_fossil_doc_from_verified_logos_record() -> None:
    record = {
        "schema": "info_geometry.hive_memory.v1",
        "source": "unit-test",
        "line_number": 4,
        "packet_index": 1,
        "artifact_kind": "DiamondFossil",
        "space": "logos",
        "entity_key": "And.intro",
        "canonical_shape": "(app (app (const And) (bvar 1)) (bvar 0))",
        "packet_sha256": "c" * 64,
        "shape_sha256": "d" * 64,
        "packet": {
            "constName": "And.intro",
            "declarationKind": "constructor",
            "kernelStatus": "verified",
            "conclusionPretty": "And _uniq.18 _uniq.19",
            "fullTypePretty": "forall {a : Prop} {b : Prop}, a -> b -> And a b",
            "axiomsUsed": [],
        },
    }

    fossil_doc = queue_tool.build_fossil_doc(record)

    assert fossil_doc["const_name"] == "And.intro"
    assert fossil_doc["conclusion_hash_shape"] == "d" * 64
    assert fossil_doc["kernel_status"] == "verified"
    assert fossil_doc["artifact_kind"] == "DiamondFossil"


def test_seed_payloads_routes_goals_and_fossils_into_queue_collections(tmp_path: Path) -> None:
    records = [
        {
            "schema": "info_geometry.hive_memory.v1",
            "source": "unit-test",
            "line_number": 2,
            "packet_index": 0,
            "artifact_kind": "InfoTreeArtifact",
            "space": "infotree",
            "entity_key": "Demo:0",
            "canonical_shape": "(forall (bvar 0) (bvar 1))",
            "packet_sha256": "a" * 64,
            "shape_sha256": "b" * 64,
            "packet": {
                "module": "Demo",
                "goalIndex": 0,
                "targetPretty": "P → P",
                "normalizationPolicy": "instantiateMVars+whnf(default)",
                "fvarPolicy": "used-fvars-in-local-context-order",
            },
        },
        {
            "schema": "info_geometry.hive_memory.v1",
            "source": "unit-test",
            "line_number": 3,
            "packet_index": 1,
            "artifact_kind": "DiamondFossil",
            "space": "logos",
            "entity_key": "And.intro",
            "canonical_shape": "(app (app (const And) (bvar 1)) (bvar 0))",
            "packet_sha256": "c" * 64,
            "shape_sha256": "d" * 64,
            "packet": {
                "constName": "And.intro",
                "declarationKind": "constructor",
                "kernelStatus": "verified",
                "conclusionPretty": "And _uniq.18 _uniq.19",
                "fullTypePretty": "forall {a : Prop} {b : Prop}, a -> b -> And a b",
                "axiomsUsed": [],
            },
        },
    ]
    input_path = tmp_path / "latest.jsonl"
    write_jsonl(input_path, records)

    payloads = queue_tool.seed_payloads(input_path, queue_name="proof-search", priority=0.75)

    assert len(payloads["hive_events"]) == 2
    assert len(payloads["hive_goals"]) == 1
    assert len(payloads["hive_tasks"]) == 1
    assert len(payloads["hive_task_for_goal"]) == 1
    assert len(payloads["hive_fossils"]) == 1
    assert len(payloads["hive_event_about"]) == 2
    assert payloads["hive_tasks"][0]["priority"] == 0.75


def test_schema_specs_include_queue_and_truth_collections() -> None:
    collections = {spec.name for spec in queue_tool.COLLECTIONS}
    indexes = {(spec.collection, spec.name) for spec in queue_tool.INDEXES}

    assert "hive_goals" in collections
    assert "hive_fossils" in collections
    assert "hive_tasks" in collections
    assert "hive_workers" in collections
    assert "hive_task_for_goal" in collections
    assert ("hive_tasks", "task_queue_status_priority_idx") in indexes
    assert ("hive_events", "event_packet_sha_idx") in indexes


def test_enqueue_leantrail_goal_sets_task_kind(monkeypatch) -> None:
    inserted: list[tuple[str, dict]] = []

    def fake_import_rows(endpoint, database, username, password, collection, docs):
        for doc in docs:
            inserted.append((collection, doc))
        return {"collection": collection, "imported": len(docs)}

    monkeypatch.setattr(queue_tool, "import_rows", fake_import_rows)

    result = queue_tool.enqueue_leantrail_goal(
        "http://127.0.0.1:8530",
        "hive_live",
        "root",
        "alexandria_root",
        queue_name="proof-search",
        goal_hash_shape="goal_hash",
        canonical_shape="⊢ theorem_goal",
        target_pretty="Demo.theorem_goal",
        module="Demo.Module",
        goal_index=0,
        priority=0.5,
    )

    assert "goal" in result
    assert "task" in result
    assert result["task"]["task_kind"] == "proof.search.leantrail"
    task_docs = [doc for coll, doc in inserted if coll == "hive_tasks"]
    assert task_docs
    assert task_docs[0]["task_kind"] == "proof.search.leantrail"
