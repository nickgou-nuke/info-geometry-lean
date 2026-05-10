"""Tests for tools/infra/hive_packet_validate.py — schema validation pipeline."""
from __future__ import annotations

import json
import sys
import subprocess
from pathlib import Path

import pytest

from tools.infra.hive_packet_validate import (
    SCHEMA_BY_KIND,
    build_store,
    format_error,
    validate_packet,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
TOOL = REPO_ROOT / "tools" / "infra" / "hive_packet_validate.py"
SCHEMA_DIR = REPO_ROOT / "tools" / "schema" / "hive"


# ---------------------------------------------------------------------------
# Minimal valid envelope for any packet kind
# ---------------------------------------------------------------------------

_ENVELOPE = {
    "id": "test-001",
    "lineage_id": "lin-001",
    "revision": 1,
    "origin_run_id": "run-001",
    "created_at": "2026-01-01T00:00:00+00:00",
    "updated_at": "2026-01-01T00:00:00+00:00",
}


# ---------------------------------------------------------------------------
# build_store
# ---------------------------------------------------------------------------

def test_build_store_contains_all_registered_schema_names() -> None:
    store = build_store()
    for kind, schema_path in SCHEMA_BY_KIND.items():
        assert schema_path.name in store or schema_path.name.replace(".schema.json", "") in store or any(
            kind in k for k in store
        ), f"schema for {kind} not found in store"


def test_build_store_keys_are_strings() -> None:
    store = build_store()
    for k in store:
        assert isinstance(k, str)


def test_build_store_values_are_dicts() -> None:
    store = build_store()
    for v in store.values():
        assert isinstance(v, dict)


# ---------------------------------------------------------------------------
# SCHEMA_BY_KIND coverage
# ---------------------------------------------------------------------------

def test_all_registered_schema_files_exist() -> None:
    for kind, schema_path in SCHEMA_BY_KIND.items():
        assert schema_path.exists(), f"schema file missing for kind={kind}: {schema_path}"


def test_chatgpt_audit_packet_registered() -> None:
    assert "ChatGPTSocraticAuditPacket" in SCHEMA_BY_KIND


def test_promotion_decision_packet_registered() -> None:
    assert "PromotionDecisionPacket" in SCHEMA_BY_KIND


# ---------------------------------------------------------------------------
# validate_packet — BeeTask (known complete schema)
# ---------------------------------------------------------------------------

def _minimal_bee_task() -> dict:
    return {
        **_ENVELOPE,
        "kind": "BeeTask",
        "status": "pending",
        "task_id": "bt-001",
        "assigned_role": "SocratesBee",
        "task_kind": "socratic.question",
        "input_packet_ids": ["p-001"],
        "allowed_output_kinds": ["BeeResult"],
        "forbidden_output_kinds": ["PromotionDecisionPacket"],
        "authority_ceiling": "proposal",
        "instruction": "Prove the theorem.",
        "dry_run": False,
    }


def test_validate_bee_task_valid() -> None:
    store = build_store()
    errors = validate_packet(
        _minimal_bee_task(),
        SCHEMA_BY_KIND["BeeTask"],
        store,
    )
    assert errors == []


def test_validate_bee_task_missing_required_field() -> None:
    store = build_store()
    packet = _minimal_bee_task()
    del packet["instruction"]
    errors = validate_packet(packet, SCHEMA_BY_KIND["BeeTask"], store)
    assert len(errors) > 0
    assert any("instruction" in e for e in errors)


def test_validate_envelope_missing_id() -> None:
    store = build_store()
    packet = _minimal_bee_task()
    del packet["id"]
    errors = validate_packet(packet, SCHEMA_BY_KIND["BeeTask"], store)
    assert len(errors) > 0


# ---------------------------------------------------------------------------
# format_error
# ---------------------------------------------------------------------------

def test_format_error_includes_message() -> None:
    from jsonschema.exceptions import ValidationError
    err = ValidationError("field is required", absolute_path=["body", "content"])
    result = format_error(err)
    assert "field is required" in result
    assert "body" in result


def test_format_error_top_level_no_path_prefix() -> None:
    from jsonschema.exceptions import ValidationError
    err = ValidationError("top-level error", absolute_path=[])
    result = format_error(err)
    assert result == "top-level error"


# ---------------------------------------------------------------------------
# CLI — subprocess tests
# ---------------------------------------------------------------------------

def test_cli_validate_valid_packet(tmp_path: Path) -> None:
    packet_path = tmp_path / "valid.json"
    packet_path.write_text(json.dumps(_minimal_bee_task()), encoding="utf-8")
    result = subprocess.run(
        [sys.executable, str(TOOL), "validate", "--packet", str(packet_path)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0
    assert "VALID" in result.stdout


def test_cli_validate_invalid_packet_exits_1(tmp_path: Path) -> None:
    packet = _minimal_bee_task()
    del packet["task_id"]
    packet_path = tmp_path / "invalid.json"
    packet_path.write_text(json.dumps(packet), encoding="utf-8")
    result = subprocess.run(
        [sys.executable, str(TOOL), "validate", "--packet", str(packet_path)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1
    assert "INVALID" in result.stdout


def test_cli_validate_missing_packet_exits_2(tmp_path: Path) -> None:
    result = subprocess.run(
        [sys.executable, str(TOOL), "validate", "--packet", str(tmp_path / "no_file.json")],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2


def test_cli_validate_unknown_kind_exits_2(tmp_path: Path) -> None:
    packet = {**_ENVELOPE, "kind": "UnknownKindXYZ123"}
    packet_path = tmp_path / "unknown.json"
    packet_path.write_text(json.dumps(packet), encoding="utf-8")
    result = subprocess.run(
        [sys.executable, str(TOOL), "validate", "--packet", str(packet_path)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2
    assert "unsupported" in result.stderr.lower() or "missing kind" in result.stderr.lower()


def test_cli_validate_explicit_schema(tmp_path: Path) -> None:
    packet_path = tmp_path / "packet.json"
    packet_path.write_text(json.dumps(_minimal_bee_task()), encoding="utf-8")
    schema_path = SCHEMA_BY_KIND["BeeTask"]
    result = subprocess.run(
        [
            sys.executable, str(TOOL), "validate",
            "--packet", str(packet_path),
            "--schema", str(schema_path),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0
