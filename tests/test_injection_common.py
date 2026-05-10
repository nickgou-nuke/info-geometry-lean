"""Tests for tools/infra/injection_common.py — packet workflow primitives."""
from __future__ import annotations

import json
import os
from datetime import datetime, timezone
from pathlib import Path

import pytest

from tools.infra.injection_common import (
    LANES,
    STATUSES,
    TRANSITION_GRAPH,
    PacketLockBusyError,
    check_transition_allowed,
    enforce_translation_gate,
    enforce_external_analogy_translation_gate,
    enforce_gated_gate,
    injections_root,
    packet_authority_tier,
    packet_prompt_hash,
    resolve_packet,
    status_for_lane,
    utc_now,
    write_json_atomic,
)


# ---------------------------------------------------------------------------
# utc_now
# ---------------------------------------------------------------------------

def test_utc_now_is_iso_format() -> None:
    ts = utc_now()
    # Must parse as ISO datetime
    dt = datetime.fromisoformat(ts)
    assert dt.tzinfo is not None


def test_utc_now_seconds_precision() -> None:
    ts = utc_now()
    # microseconds should be stripped
    assert "." not in ts.split("T")[1]


# ---------------------------------------------------------------------------
# status_for_lane
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("lane, expected", [
    ("raw", "raw"),
    ("distilled", "distilled"),
    ("translated", "translated"),
    ("gated", "gated"),
    ("accepted", "accepted"),
    ("rejected", "rejected"),
    ("archive", "archived"),
])
def test_status_for_lane(lane: str, expected: str) -> None:
    assert status_for_lane(lane) == expected


# ---------------------------------------------------------------------------
# check_transition_allowed
# ---------------------------------------------------------------------------

def test_check_transition_raw_to_distilled_ok() -> None:
    check_transition_allowed("raw", "distilled")  # no exception


def test_check_transition_raw_to_accepted_raises() -> None:
    with pytest.raises(ValueError, match="transition"):
        check_transition_allowed("raw", "accepted")


def test_check_transition_accepted_to_archive_ok() -> None:
    check_transition_allowed("accepted", "archive")


def test_check_transition_archive_raises_for_any_target() -> None:
    with pytest.raises(ValueError):
        check_transition_allowed("archive", "raw")


def test_all_valid_transitions_do_not_raise() -> None:
    for src, targets in TRANSITION_GRAPH.items():
        for dst in targets:
            check_transition_allowed(src, dst)


# ---------------------------------------------------------------------------
# write_json_atomic
# ---------------------------------------------------------------------------

def test_write_json_atomic_creates_file(tmp_path: Path) -> None:
    p = tmp_path / "out.json"
    payload = {"key": "value", "num": 42}
    write_json_atomic(p, payload)
    assert p.exists()
    data = json.loads(p.read_text())
    assert data == payload


def test_write_json_atomic_creates_parent_dirs(tmp_path: Path) -> None:
    p = tmp_path / "deep" / "nested" / "out.json"
    write_json_atomic(p, {"x": 1})
    assert p.exists()


def test_write_json_atomic_overwrites_existing(tmp_path: Path) -> None:
    p = tmp_path / "file.json"
    write_json_atomic(p, {"first": True})
    write_json_atomic(p, {"second": True})
    data = json.loads(p.read_text())
    assert data == {"second": True}


# ---------------------------------------------------------------------------
# resolve_packet
# ---------------------------------------------------------------------------

def test_resolve_packet_direct_path(tmp_path: Path) -> None:
    p = tmp_path / "packet.json"
    p.write_text("{}", encoding="utf-8")
    result = resolve_packet(tmp_path, str(p))
    assert result == p


def test_resolve_packet_by_id_in_lane(tmp_path: Path) -> None:
    injections = tmp_path / "injections"
    raw_dir = injections / "raw"
    raw_dir.mkdir(parents=True)
    packet_file = raw_dir / "EXT-001.json"
    packet_file.write_text("{}", encoding="utf-8")
    result = resolve_packet(injections, "EXT-001")
    assert result == packet_file


def test_resolve_packet_raises_when_not_found(tmp_path: Path) -> None:
    with pytest.raises(FileNotFoundError):
        resolve_packet(tmp_path / "injections", "NO_SUCH_PACKET")


# ---------------------------------------------------------------------------
# packet_prompt_hash
# ---------------------------------------------------------------------------

def test_packet_prompt_hash_stable() -> None:
    packet = {"packet_id": "p1", "raw_text": "Prove X → Y", "kind": "BeeTask"}
    h1 = packet_prompt_hash(packet)
    h2 = packet_prompt_hash(packet)
    assert h1 == h2
    assert len(h1) == 64  # SHA-256 hex


def test_packet_prompt_hash_differs_for_different_prompts() -> None:
    p1 = {"packet_id": "p1", "raw_text": "Prove X → Y"}
    p2 = {"packet_id": "p1", "raw_text": "Prove Y → X"}
    assert packet_prompt_hash(p1) != packet_prompt_hash(p2)


def test_packet_prompt_hash_empty_packet() -> None:
    h = packet_prompt_hash({})
    assert isinstance(h, str)
    assert len(h) == 64


# ---------------------------------------------------------------------------
# packet_authority_tier
# ---------------------------------------------------------------------------

def test_packet_authority_tier_repo_native() -> None:
    packet = {"authority_tier": "repo_native"}
    assert packet_authority_tier(packet) == "repo_native"


def test_packet_authority_tier_external_analogy() -> None:
    packet = {"authority_tier": "external_analogy"}
    assert packet_authority_tier(packet) == "external_analogy"


def test_packet_authority_tier_default() -> None:
    # Missing field → defaults to some value without raising
    tier = packet_authority_tier({})
    assert isinstance(tier, str)


# ---------------------------------------------------------------------------
# enforce_translation_gate
# ---------------------------------------------------------------------------

def test_enforce_translation_gate_passes_when_translated() -> None:
    packet = {
        "status": "translated",
        "repo_mapping": {
            "owner_files": ["lean/InfoGeometry/Canonical/Drazin.lean"],
            "symbols": ["InfoGeometry.Canonical.Drazin.IsDrazinInverse"],
            "target_theorems": ["InfoGeometry.Canonical.Drazin.unique"],
        },
        "distilled_claim": "Drazin inverse is unique.",
        "raw_text": "The Drazin inverse satisfies uniqueness.",
    }
    enforce_translation_gate(packet)  # no exception


def test_enforce_translation_gate_raises_when_no_translation() -> None:
    packet = {"status": "translated"}
    with pytest.raises((ValueError, KeyError, TypeError)):
        enforce_translation_gate(packet)


# ---------------------------------------------------------------------------
# enforce_gated_gate
# ---------------------------------------------------------------------------

def test_enforce_gated_gate_passes_with_review() -> None:
    packet = {
        "status": "gated",
        "reviewer": "pauli_auditor",
        "gate_decision": "pass",
        "gate_rationale": "Checks out.",
        "repo_mapping": {
            "owner_files": ["lean/InfoGeometry/Canonical/Drazin.lean"],
            "symbols": ["InfoGeometry.Canonical.Drazin.IsDrazinInverse"],
            "target_theorems": ["InfoGeometry.Canonical.Drazin.unique"],
        },
        "verification_plan": {
            "build_targets": ["InfoGeometry.Canonical.Drazin"],
        },
        "distilled_claim": "Drazin inverse is unique.",
        "raw_text": "The Drazin inverse satisfies uniqueness.",
    }
    enforce_gated_gate(packet)  # no exception


# ---------------------------------------------------------------------------
# PacketLockBusyError
# ---------------------------------------------------------------------------

def test_packet_lock_busy_error_message_contains_path() -> None:
    err = PacketLockBusyError(Path("/tmp/locks/EXT-001.lock"))
    assert "EXT-001" in str(err)


def test_packet_lock_busy_error_with_metadata() -> None:
    err = PacketLockBusyError(
        Path("/tmp/locks/EXT-002.lock"),
        metadata={"owner": "test_agent", "pid": 12345},
    )
    assert "test_agent" in str(err)
    assert "12345" in str(err)


# ---------------------------------------------------------------------------
# LANES / STATUSES constants
# ---------------------------------------------------------------------------

def test_lanes_contains_all_workflow_stages() -> None:
    for stage in ("raw", "distilled", "translated", "gated", "accepted", "rejected", "archive"):
        assert stage in LANES


def test_statuses_contains_all_valid_statuses() -> None:
    for s in ("raw", "distilled", "translated", "gated", "accepted", "rejected", "archived"):
        assert s in STATUSES
