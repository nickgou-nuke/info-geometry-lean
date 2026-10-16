#!/usr/bin/env python3
"""Pantograph Epistemic Swarm bridge tool.

Connects candidate theorem/tactic generators to an interactive Lean 4 Pantograph
REPL process, persists every request, response, state, and goal transition into
ArangoDB collections (pantograph_sessions, pantograph_requests, pantograph_responses,
pantograph_states), and emits validated SocraticQuestionPackets containing exact
Lean goal states when tactics or elaborations fail.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import select
import subprocess
import sys
import time
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    _SRC = Path(__file__).resolve().parents[2] / "src"
    if str(_SRC) not in sys.path:
        sys.path.insert(0, str(_SRC))

from tools.infra.arango_env import (  # noqa: E402
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import (  # noqa: E402
    ArangoTarget,
    db_url,
    request_json,
)
from tools.infra.hive_packet_validate import (  # noqa: E402
    SCHEMA_BY_KIND,
    build_store,
    validate_packet,
)
from tools.infra.pantograph_arango_stream import (  # noqa: E402
    PantographStore,
    arango_key,
    canonical_json,
    digest,
    parse_request,
    read_response,
)
from tools.infra.pantograph_environment import (  # noqa: E402
    build_environment_manifest,
)


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

@dataclass
class CandidatePacket:
    """Normalized candidate packet ingested by the swarm."""
    packet_id: str
    kind: str
    formal_target: str
    tactics: list[str] = field(default_factory=list)
    module: str = "Init"
    raw_packet: dict[str, Any] = field(default_factory=dict)

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> CandidatePacket:
        pkt_id = str(data.get("id") or data.get("taskId") or f"cand-{uuid.uuid4().hex[:8]}")
        kind = str(data.get("kind") or "TheoremCandidatePacket")
        
        # Formal target resolution
        formal_target = ""
        ft_obj = data.get("formal_target")
        if isinstance(ft_obj, dict):
            formal_target = str(
                ft_obj.get("target_expression")
                or ft_obj.get("lean_statement")
                or ft_obj.get("claim")
                or ft_obj.get("target")
                or ""
            )
        elif isinstance(ft_obj, str):
            formal_target = ft_obj
        if not formal_target:
            formal_target = str(data.get("expr") or data.get("claim") or data.get("statement") or data.get("target") or "")

        # Tactics resolution
        tactics_raw = (
            data.get("candidate_tactics")
            or data.get("tactics")
            or data.get("proof")
            or data.get("steps")
            or []
        )
        if isinstance(tactics_raw, str):
            tactics = [line.strip() for line in tactics_raw.splitlines() if line.strip()]
        elif isinstance(tactics_raw, list):
            tactics = [str(t).strip() for t in tactics_raw if str(t).strip()]
        else:
            tactics = []

        module = str(data.get("module") or "Init")
        return cls(
            packet_id=pkt_id,
            kind=kind,
            formal_target=formal_target,
            tactics=tactics,
            module=module,
            raw_packet=data,
        )


@dataclass
class CandidateResult:
    """Outcome of processing a candidate through the swarm."""
    packet_id: str
    formal_target: str
    status: str  # "proved", "tactic_failure", "elaboration_failure", "open_goals", "error"
    final_state_id: Optional[int] = None
    remaining_goals: list[dict[str, Any]] = field(default_factory=list)
    socratic_packet: Optional[dict[str, Any]] = None
    executed_tactics: list[str] = field(default_factory=list)
    error_message: Optional[str] = None


# ---------------------------------------------------------------------------
# Socratic Question Packet Builder
# ---------------------------------------------------------------------------

def extract_goal_state_from_messages(messages: list[dict[str, Any]]) -> str:
    """Extract goal state representation (e.g., turnstile and hypotheses) from diagnostics."""
    for msg in messages:
        data = str(msg.get("data", ""))
        if "⊢" in data:
            lines = data.splitlines()
            goal_lines = []
            capturing = False
            for line in lines:
                if ":" in line or "⊢" in line:
                    capturing = True
                if capturing:
                    goal_lines.append(line)
            if goal_lines:
                return "\n".join(goal_lines).strip()
            return data.strip()
    return ""


def format_goal_ast(goal_obj: dict[str, Any]) -> str:
    """Pretty format a Pantograph Goal JSON object into standard Lean syntax."""
    vars_list = goal_obj.get("vars", [])
    hyp_lines: list[str] = []
    for var in vars_list:
        name = var.get("userName") or var.get("name") or "?"
        type_pp = ""
        type_info = var.get("type", {})
        if isinstance(type_info, dict):
            type_pp = type_info.get("pp", "")
        hyp_lines.append(f"{name} : {type_pp}")
    
    target_pp = ""
    target_info = goal_obj.get("target", {})
    if isinstance(target_info, dict):
        target_pp = target_info.get("pp", "")
    
    if hyp_lines:
        return "\n".join(hyp_lines) + f"\n⊢ {target_pp}"
    return f"⊢ {target_pp}"


# ---------------------------------------------------------------------------
# Typed Socratic Failure Taxonomy (Tier 3.2) & Alpha-Normalization (Tier 1.1)
# ---------------------------------------------------------------------------

DIAGNOSTIC_MISSING_LEMMA = "MISSING_LEMMA"
DIAGNOSTIC_TYPE_MISMATCH = "TYPE_MISMATCH"
DIAGNOSTIC_INSUFFICIENT_HYPOTHESIS = "INSUFFICIENT_HYPOTHESIS"
DIAGNOSTIC_UNFOLDING_BLOCKED = "UNFOLDING_BLOCKED"
DIAGNOSTIC_TIMEOUT = "TIMEOUT"

COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE = "INSUFFICIENT_CARRIER_STRUCTURE"
COGNITIVE_MODE_TYPE_MISMATCH = "TYPE_MISMATCH"
COGNITIVE_MODE_MISSING_LEMMA = "MISSING_LEMMA"
COGNITIVE_MODE_TIMEOUT = "TIMEOUT_NONTERMINATION"
COGNITIVE_MODE_UNFOLDING_BLOCKED = "UNFOLDING_BLOCKED"
COGNITIVE_MODE_INSUFFICIENT_HYPOTHESIS = "INSUFFICIENT_HYPOTHESIS"

DEFAULT_SUGGESTED_ACTIONS: dict[str, list[str]] = {
    COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE: [
        "EXTRACT_LEMMAS",
        "WEAKEN_TARGET",
        "SUBSTITUTE_MODEL",
    ],
    COGNITIVE_MODE_TYPE_MISMATCH: [
        "CAST_EQUALITY",
        "COERCE_TYPES",
        "REWRITE_DEF",
    ],
    COGNITIVE_MODE_MISSING_LEMMA: [
        "EXTRACT_LEMMAS",
        "IMPORT_MATHLIB_MODULE",
        "SEARCH_LEANSEARCH",
    ],
    COGNITIVE_MODE_TIMEOUT: [
        "SIMPLIFY_TACTIC",
        "PROVIDE_INTERMEDIATE_STEPS",
        "BOUND_MAX_HEURISTICS",
    ],
    COGNITIVE_MODE_UNFOLDING_BLOCKED: [
        "TRANSPARENCY_UNFOLD",
        "INTRODUCE_BRIDGE_LEMMA",
    ],
    COGNITIVE_MODE_INSUFFICIENT_HYPOTHESIS: [
        "EXTRACT_LEMMAS",
        "WEAKEN_TARGET",
        "SUBSTITUTE_MODEL",
    ],
}


def infer_cognitive_mode_and_actions(
    error_msg: str,
    diagnostic_kind: str,
    tactic: Optional[str] = None,
) -> tuple[str, list[str], str]:
    """Derive cognitive_mode, suggested_actions, and lean_error_code from diagnostic context."""
    lowered = error_msg.lower()

    # 1. Timeout / non-termination
    if "timeout" in lowered or (tactic and tactic.strip() in ("timeout", "loop", "sleep")):
        mode = COGNITIVE_MODE_TIMEOUT
        code = "LEAN_TIMEOUT"
        actions = list(DEFAULT_SUGGESTED_ACTIONS[COGNITIVE_MODE_TIMEOUT])
        return mode, actions, code

    # 2. Insufficient Carrier / Typeclass synthesis failure
    carrier_indicators = (
        "failed to synthesize",
        "typeclass",
        "carrier",
        "metricspace",
        "topologicalspace",
        "innerproductspace",
        "normedaddcommgroup",
        "hilbert",
        "cstar",
        "algebra",
        "ring",
        "field",
    )
    if any(ind in lowered for ind in carrier_indicators):
        mode = COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE
        code = "LEAN_FAILED_TO_SYNTHESIZE_INSTANCE" if "failed to synthesize" in lowered else "LEAN_INSUFFICIENT_CARRIER"
        actions = list(DEFAULT_SUGGESTED_ACTIONS[COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE])
        return mode, actions, code

    # 3. Type Mismatch
    if diagnostic_kind == DIAGNOSTIC_TYPE_MISMATCH or "type mismatch" in lowered or "not definitionally equal" in lowered:
        mode = COGNITIVE_MODE_TYPE_MISMATCH
        code = "LEAN_TYPE_MISMATCH"
        actions = list(DEFAULT_SUGGESTED_ACTIONS[COGNITIVE_MODE_TYPE_MISMATCH])
        return mode, actions, code

    # 4. Missing Lemma / Constant
    if diagnostic_kind == DIAGNOSTIC_MISSING_LEMMA or "unknown identifier" in lowered or "unknown constant" in lowered:
        mode = COGNITIVE_MODE_MISSING_LEMMA
        code = "LEAN_UNKNOWN_IDENTIFIER"
        actions = list(DEFAULT_SUGGESTED_ACTIONS[COGNITIVE_MODE_MISSING_LEMMA])
        return mode, actions, code

    # 5. Unfolding Blocked
    if diagnostic_kind == DIAGNOSTIC_UNFOLDING_BLOCKED or "cannot unfold" in lowered:
        mode = COGNITIVE_MODE_UNFOLDING_BLOCKED
        code = "LEAN_CANNOT_UNFOLD"
        actions = list(DEFAULT_SUGGESTED_ACTIONS[COGNITIVE_MODE_UNFOLDING_BLOCKED])
        return mode, actions, code

    # 6. Default / Insufficient Hypothesis
    mode = COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE
    code = "LEAN_TACTIC_FAILED"
    actions = list(DEFAULT_SUGGESTED_ACTIONS[COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE])
    return mode, actions, code


def extract_typed_diagnostic(error_msg: str, exact_goal_state: str = "") -> tuple[str, dict[str, Any]]:
    """Extract a strongly typed failure diagnostic schema from compiler output."""
    lowered = error_msg.lower()

    # 0. TIMEOUT
    if "timeout" in lowered:
        return DIAGNOSTIC_TIMEOUT, {
            "kind": DIAGNOSTIC_TIMEOUT,
            "raw_error": error_msg[:500],
        }

    # 1. TYPE_MISMATCH
    if "type mismatch" in lowered or "is not definitionally equal to" in lowered or "has type" in lowered:
        expected = ""
        inferred = ""
        m_def = re.search(
            r"The left-hand side\s*\n\s*(.*?)\s*\nis not definitionally equal to the right-hand side\s*\n\s*(.*?)\s*(\n|$)",
            error_msg,
            re.DOTALL,
        )
        if m_def:
            inferred = m_def.group(1).strip()
            expected = m_def.group(2).strip()
        else:
            m_type = re.search(
                r"has type\s*\n\s*(.*?)\s*\nbut is expected to have type\s*\n\s*(.*?)\s*(\n|$)",
                error_msg,
                re.DOTALL,
            )
            if m_type:
                inferred = m_type.group(1).strip()
                expected = m_type.group(2).strip()
        return DIAGNOSTIC_TYPE_MISMATCH, {
            "kind": DIAGNOSTIC_TYPE_MISMATCH,
            "expected": expected,
            "inferred": inferred,
            "raw_error": error_msg[:500],
        }

    # 2. MISSING_LEMMA
    if "unknown identifier" in lowered or "not found" in lowered or "unknown constant" in lowered or "failed to synthesize instance" in lowered:
        missing_ident = ""
        m_id = re.search(r"unknown identifier '([^']+)'", error_msg)
        if not m_id:
            m_id = re.search(r"unknown constant '([^']+)'", error_msg)
        if m_id:
            missing_ident = m_id.group(1)
        return DIAGNOSTIC_MISSING_LEMMA, {
            "kind": DIAGNOSTIC_MISSING_LEMMA,
            "missing_identifier": missing_ident,
            "raw_error": error_msg[:500],
        }

    # 3. UNFOLDING_BLOCKED
    if "cannot unfold" in lowered or "opaque" in lowered or "maximum recursion depth" in lowered or "deterministic timeout" in lowered:
        opaque_const = ""
        m_op = re.search(r"cannot unfold '([^']+)'", error_msg)
        if m_op:
            opaque_const = m_op.group(1)
        return DIAGNOSTIC_UNFOLDING_BLOCKED, {
            "kind": DIAGNOSTIC_UNFOLDING_BLOCKED,
            "opaque_constant": opaque_const,
            "raw_error": error_msg[:500],
        }

    # 4. INSUFFICIENT_HYPOTHESIS / FALSIFICATION
    return DIAGNOSTIC_INSUFFICIENT_HYPOTHESIS, {
        "kind": DIAGNOSTIC_INSUFFICIENT_HYPOTHESIS,
        "goal_state": exact_goal_state,
        "raw_error": error_msg[:500],
    }


def normalize_goal_alpha(goal_text: str) -> str:
    """Normalize a goal state string to an alpha-invariant canonical form.

    Replaces named local hypotheses with canonical de Bruijn placeholders (#0, #1, ...),
    strips redundant whitespace, and alphabetically sorts independent hypotheses to
    guarantee permutation invariance across equivalence classes.
    """
    lines = [line.strip() for line in goal_text.splitlines() if line.strip()]
    hypotheses: list[str] = []
    target = ""
    for line in lines:
        if line.startswith("⊢"):
            target = line[1:].strip()
        elif ":" in line:
            hypotheses.append(line)
        elif not target:
            target = line

    var_map: dict[str, str] = {}
    counter = 0
    for hyp in hypotheses:
        name_part, _, _ = hyp.partition(":")
        name = name_part.strip()
        if name and name not in var_map:
            var_map[name] = f"#{counter}"
            counter += 1

    def replace_vars(text: str) -> str:
        res = text
        for var_name, var_sub in sorted(var_map.items(), key=lambda x: -len(x[0])):
            res = re.sub(rf"\b{re.escape(var_name)}\b", var_sub, res)
        return " ".join(res.split())

    normalized_hyps: list[str] = []
    for hyp in hypotheses:
        _, _, type_part = hyp.partition(":")
        normalized_hyps.append(replace_vars(type_part.strip()))

    normalized_hyps.sort()
    norm_target = replace_vars(target)
    return " & ".join(normalized_hyps) + " ⊢ " + norm_target


def compute_subgoal_hash(goal_text: str) -> str:
    """Compute 256-bit SHA256 digest of alpha-normalized goal state."""
    norm = normalize_goal_alpha(goal_text)
    return hashlib.sha256(norm.encode("utf-8")).hexdigest()


def classify_question_type(error_msg: str, is_elaboration: bool = False) -> str:
    """Classify the failure into standard Hive question_type enum."""
    if is_elaboration:
        return "definition_pressure"
    lowered = error_msg.lower()
    if "expected the goal to be a binary relation" in lowered or "not definitionally equal" in lowered:
        return "counterexample_pressure"
    if "unknown identifier" in lowered or "missing" in lowered or "unresolved" in lowered:
        return "hidden_hypothesis"
    if "type mismatch" in lowered or "failed to synthesize" in lowered:
        return "admissibility_pressure"
    if "tactic" in lowered and "failed" in lowered:
        return "falsification_pressure"
    return "other"


def build_socratic_packet(
    candidate_id: str,
    session_id: str,
    formal_target: str,
    question: str,
    question_type: str,
    exact_goal_state: str,
    failed_tactic: Optional[str] = None,
    error_message: str = "",
    state_id: Optional[int] = None,
    request_key: Optional[str] = None,
    response_key: Optional[str] = None,
    diagnostic_kind: Optional[str] = None,
    diagnostic_payload: Optional[dict[str, Any]] = None,
    parent_goal_hash: Optional[str] = None,
    tactic_attempted: Optional[str] = None,
    lean_error_code: Optional[str] = None,
    cognitive_mode: Optional[str] = None,
    suggested_actions: Optional[list[str]] = None,
) -> dict[str, Any]:
    """Construct a fully schema-compliant SocraticQuestionPacket with enriched lifecycle metadata."""
    now = datetime.now(timezone.utc).isoformat()
    if diagnostic_kind is None or diagnostic_payload is None:
        d_kind, d_payload = extract_typed_diagnostic(error_message, exact_goal_state)
        diagnostic_kind = diagnostic_kind or d_kind
        diagnostic_payload = diagnostic_payload or d_payload

    if parent_goal_hash is None:
        parent_goal_hash = compute_subgoal_hash(exact_goal_state or formal_target)
    if tactic_attempted is None:
        tactic_attempted = failed_tactic

    inferred_mode, inferred_actions, inferred_code = infer_cognitive_mode_and_actions(
        error_msg=error_message,
        diagnostic_kind=diagnostic_kind,
        tactic=tactic_attempted,
    )
    if cognitive_mode is None:
        cognitive_mode = inferred_mode
    if suggested_actions is None:
        suggested_actions = inferred_actions
    if lean_error_code is None:
        lean_error_code = inferred_code

    packet = {
        "id": f"socratic:{candidate_id}:{uuid.uuid4().hex[:8]}",
        "kind": "SocraticQuestionPacket",
        "status": "open",
        "lineage_id": candidate_id,
        "revision": 1,
        "origin_run_id": session_id,
        "created_at": now,
        "updated_at": now,
        "authority": "semantic",
        "epistemic_layer": "cognitive_process",
        "authority_origin": "socratic_interrogation",
        "cognitive_function": "thinking",
        "jung_function": "thinking",
        "promotion_allowed": False,
        "representation_class": "translator",
        "representation_depth": "categorical",
        "question": question,
        "question_type": question_type,
        "target_packet_ids": [candidate_id],
        "missing_hypotheses": [],
        "allowed_uses": ["candidate_refinement"],
        "forbidden_uses": ["proof"],
        # Extended context for creative generation
        "formal_target": formal_target,
        "exact_goal_state": exact_goal_state,
        "failed_tactic": failed_tactic,
        "error_message": error_message,
        "pantograph_state_id": state_id,
        "session_id": session_id,
        "request_key": request_key,
        "response_key": response_key,
        # Tier 3.2 Typed Socratic diagnostic
        "diagnostic_kind": diagnostic_kind,
        "diagnostic_payload": diagnostic_payload,
        "subgoal_hash": parent_goal_hash,
        # Swarm lifecycle & epistemic enrichment
        "parent_goal_hash": parent_goal_hash,
        "tactic_attempted": tactic_attempted,
        "lean_error_code": lean_error_code,
        "cognitive_mode": cognitive_mode,
        "suggested_actions": suggested_actions,
    }
    return packet


# ---------------------------------------------------------------------------
# Epistemic Swarm Arango Store
# ---------------------------------------------------------------------------

class EpistemicSwarmStore(PantographStore):
    """Extends PantographStore with SocraticQuestion persistence and collection support."""

    def ensure_collections(self) -> None:
        super().ensure_collections()
        # Ensure collections for socratic questions and subgoal cache
        existing = request_json(
            "GET", self.url("/_api/collection"),
            username=self.target.username, password=self.target.password,
        )
        names = {row.get("name") for row in existing.get("result", [])} if isinstance(existing, dict) else set()
        for coll_name in ("pantograph_socratic_questions", "pantograph_subgoal_cache"):
            if coll_name not in names:
                try:
                    request_json(
                        "POST", self.url("/_api/collection"),
                        username=self.target.username, password=self.target.password,
                        payload={"name": coll_name, "type": 2, "waitForSync": True},
                    )
                except RuntimeError:
                    pass

    def record_socratic_question(self, packet: dict[str, Any]) -> str:
        key = arango_key("psq", packet["id"])
        doc = dict(packet)
        doc["_key"] = key
        self.insert_immutable("pantograph_socratic_questions", doc)
        self.session_event("socratic_question_emitted", {
            "packetId": packet["id"],
            "targetPacketId": packet["target_packet_ids"][0] if packet.get("target_packet_ids") else None,
            "questionType": packet.get("question_type"),
            "failedTactic": packet.get("failed_tactic"),
        })
        return key

    def record_subgoal_cache(
        self,
        subgoal_hash: str,
        formal_target: str,
        tactics: list[str],
        session_id: str,
    ) -> str:
        """Cache proven tactic sequence indexed by alpha-invariant subgoal hash."""
        key = arango_key("psc", subgoal_hash)
        doc = {
            "_key": key,
            "subgoalHash": subgoal_hash,
            "formalTarget": formal_target,
            "tactics": tactics,
            "sessionId": session_id,
            "cachedAt": datetime.now(timezone.utc).isoformat(),
        }
        self.insert_immutable("pantograph_subgoal_cache", doc)
        self.session_event("subgoal_cached", {"subgoalHash": subgoal_hash, "formalTarget": formal_target})
        return key

    def lookup_subgoal_cache(self, subgoal_hash: str) -> Optional[dict[str, Any]]:
        """Look up previously proven tactics for an alpha-equivalent goal state."""
        key = arango_key("psc", subgoal_hash)
        url = self.url(f"/_api/document/pantograph_subgoal_cache/{key}")
        try:
            doc = request_json(
                "GET", url,
                username=self.target.username, password=self.target.password,
            )
            if isinstance(doc, dict) and doc.get("subgoalHash") == subgoal_hash:
                return doc
        except RuntimeError:
            pass
        return None

    def start(self, command: list[str], pantograph_version: str, source_snapshot: Optional[Path], ttl_seconds: int = 180) -> None:
        super().start(command, pantograph_version, source_snapshot)
        self.heartbeat_session(self.session_id, ttl_seconds=ttl_seconds)

    def heartbeat_session(self, session_id: Optional[str] = None, ttl_seconds: int = 180) -> dict[str, Any]:
        """Update session lease timestamp, prolonging its TTL by ttl_seconds."""
        sid = session_id or self.session_id
        skey = arango_key("ps", sid)
        now = datetime.now(timezone.utc)
        expires_at = (now + timedelta(seconds=ttl_seconds)).isoformat()
        now_iso = now.isoformat()
        patch_payload = {
            "lastHeartbeatAt": now_iso,
            "leaseExpiresAt": expires_at,
            "ttlSeconds": ttl_seconds,
            "status": "active",
        }
        try:
            request_json(
                "PATCH", self.url(f"/_api/document/pantograph_sessions/{skey}"),
                username=self.target.username, password=self.target.password,
                payload=patch_payload,
            )
        except Exception:
            pass
        self.session_event("session_heartbeat", {
            "sessionId": sid,
            "leaseExpiresAt": expires_at,
            "ttlSeconds": ttl_seconds,
        })
        return {
            "_key": skey,
            "sessionId": sid,
            **patch_payload,
        }

    def check_expired_sessions(
        self,
        ttl_seconds: int = 180,
        reference_time: Optional[datetime] = None,
    ) -> list[dict[str, Any]]:
        """Identify deadlocked/expired Pantograph sessions whose lease TTL has lapsed."""
        ref_dt = reference_time or datetime.now(timezone.utc)
        ref_iso = ref_dt.isoformat()
        query = """
        FOR s IN pantograph_sessions
          LET exp = s.leaseExpiresAt != null ? s.leaseExpiresAt : DATE_ISO8601(DATE_ADD(s.lastHeartbeatAt != null ? s.lastHeartbeatAt : s.startedAt, @ttl, "second"))
          FILTER exp <= @now && s.status != "expired" && s.status != "closed" && s.status != "deadlocked"
          RETURN MERGE(s, { calculatedExpiry: exp, isDeadlocked: true })
        """.strip()
        try:
            return query_all_rows(self.target, query, {"now": ref_iso, "ttl": ttl_seconds})
        except Exception:
            return []

    def reap_deadlocked_sessions(
        self,
        ttl_seconds: int = 180,
        reference_time: Optional[datetime] = None,
    ) -> list[dict[str, Any]]:
        """Mark deadlocked/expired Pantograph sessions as deadlocked."""
        deadlocked = self.check_expired_sessions(ttl_seconds, reference_time)
        reaped: list[dict[str, Any]] = []
        now_iso = datetime.now(timezone.utc).isoformat()
        for s in deadlocked:
            skey = s.get("_key")
            if skey:
                try:
                    request_json(
                        "PATCH", self.url(f"/_api/document/pantograph_sessions/{skey}"),
                        username=self.target.username, password=self.target.password,
                        payload={"status": "deadlocked", "deadlockedAt": now_iso},
                    )
                    reaped.append(dict(s, status="deadlocked", deadlockedAt=now_iso))
                except Exception:
                    pass
        return reaped

    def is_session_expired(
        self,
        session_id: Optional[str] = None,
        ttl_seconds: int = 180,
        reference_time: Optional[datetime] = None,
    ) -> bool:
        """Check if a specific session has expired or deadlocked."""
        sid = session_id or self.session_id
        skey = arango_key("ps", sid)
        ref_dt = reference_time or datetime.now(timezone.utc)
        try:
            doc = request_json(
                "GET", self.url(f"/_api/document/pantograph_sessions/{skey}"),
                username=self.target.username, password=self.target.password,
            )
            if not isinstance(doc, dict):
                return False
            if doc.get("status") in ("expired", "deadlocked"):
                return True
            lease_exp_str = doc.get("leaseExpiresAt")
            if lease_exp_str:
                return datetime.fromisoformat(lease_exp_str) <= ref_dt
            base_str = doc.get("lastHeartbeatAt") or doc.get("startedAt")
            if base_str:
                return (datetime.fromisoformat(base_str) + timedelta(seconds=ttl_seconds)) <= ref_dt
        except Exception:
            pass
        return False


class MockEpistemicSwarmStore:
    """Hermetic in-memory store for dry-run verification without network or ArangoDB."""

    def __init__(self, session_id: str):
        self.session_id = session_id
        self.session_key = arango_key("ps", session_id)
        self.collections: dict[str, dict[str, Any]] = {
            "pantograph_sessions": {},
            "pantograph_requests": {},
            "pantograph_responses": {},
            "pantograph_states": {},
            "pantograph_goal_summaries": {},
            "pantograph_state_transitions": {},
            "pantograph_revision_events": {},
            "pantograph_revision_edges": {},
            "pantograph_event_occurrences": {},
            "pantograph_session_events": {},
            "pantograph_socratic_questions": {},
            "pantograph_subgoal_cache": {},
        }
        self.seq = 0
        self.last_event_key = f"rev_{session_id}_root"

    def record_socratic_question(self, packet: dict[str, Any]) -> str:
        key = arango_key("psq", packet["id"])
        doc = dict(packet)
        doc["_key"] = key
        self.collections["pantograph_socratic_questions"][key] = doc
        return key

    def record_subgoal_cache(
        self,
        subgoal_hash: str,
        formal_target: str,
        tactics: list[str],
        session_id: str,
    ) -> str:
        key = arango_key("psc", subgoal_hash)
        doc = {
            "_key": key,
            "subgoalHash": subgoal_hash,
            "formalTarget": formal_target,
            "tactics": tactics,
            "sessionId": session_id,
            "cachedAt": datetime.now(timezone.utc).isoformat(),
        }
        self.collections["pantograph_subgoal_cache"][key] = doc
        return key

    def lookup_subgoal_cache(self, subgoal_hash: str) -> Optional[dict[str, Any]]:
        key = arango_key("psc", subgoal_hash)
        return self.collections["pantograph_subgoal_cache"].get(key)

    def ensure_collections(self) -> None:
        pass

    def start(self, command: list[str], pantograph_version: str, source_snapshot: Optional[Path], ttl_seconds: int = 180) -> None:
        now = datetime.now(timezone.utc)
        now_iso = now.isoformat()
        expires_at = (now + timedelta(seconds=ttl_seconds)).isoformat()
        self.collections["pantograph_sessions"][self.session_key] = {
            "_key": self.session_key,
            "sessionId": self.session_id,
            "command": command,
            "pantographVersion": pantograph_version,
            "startedAt": now_iso,
            "lastHeartbeatAt": now_iso,
            "leaseExpiresAt": expires_at,
            "ttlSeconds": ttl_seconds,
            "status": "active",
        }

    def heartbeat_session(self, session_id: Optional[str] = None, ttl_seconds: int = 180) -> dict[str, Any]:
        sid = session_id or self.session_id
        skey = arango_key("ps", sid)
        now = datetime.now(timezone.utc)
        expires_at = (now + timedelta(seconds=ttl_seconds)).isoformat()
        now_iso = now.isoformat()
        sess_doc = self.collections["pantograph_sessions"].setdefault(skey, {
            "_key": skey,
            "sessionId": sid,
            "startedAt": now_iso,
        })
        sess_doc.update({
            "lastHeartbeatAt": now_iso,
            "leaseExpiresAt": expires_at,
            "ttlSeconds": ttl_seconds,
            "status": "active",
        })
        self.session_event("session_heartbeat", {
            "sessionId": sid,
            "leaseExpiresAt": expires_at,
            "ttlSeconds": ttl_seconds,
        })
        return dict(sess_doc)

    def check_expired_sessions(
        self,
        ttl_seconds: int = 180,
        reference_time: Optional[datetime] = None,
    ) -> list[dict[str, Any]]:
        ref_dt = reference_time or datetime.now(timezone.utc)
        expired = []
        for skey, sess in self.collections["pantograph_sessions"].items():
            if sess.get("status") in ("expired", "closed", "deadlocked"):
                continue
            lease_exp_str = sess.get("leaseExpiresAt")
            if lease_exp_str:
                exp_dt = datetime.fromisoformat(lease_exp_str)
            else:
                base_str = sess.get("lastHeartbeatAt") or sess.get("startedAt")
                if base_str:
                    exp_dt = datetime.fromisoformat(base_str) + timedelta(seconds=ttl_seconds)
                else:
                    exp_dt = ref_dt
            if exp_dt <= ref_dt:
                expired.append(dict(sess, calculatedExpiry=exp_dt.isoformat(), isDeadlocked=True))
        return expired

    def reap_deadlocked_sessions(
        self,
        ttl_seconds: int = 180,
        reference_time: Optional[datetime] = None,
    ) -> list[dict[str, Any]]:
        deadlocked = self.check_expired_sessions(ttl_seconds, reference_time)
        reaped = []
        now_iso = datetime.now(timezone.utc).isoformat()
        for s in deadlocked:
            skey = s.get("_key")
            if skey and skey in self.collections["pantograph_sessions"]:
                self.collections["pantograph_sessions"][skey]["status"] = "deadlocked"
                self.collections["pantograph_sessions"][skey]["deadlockedAt"] = now_iso
                reaped.append(dict(self.collections["pantograph_sessions"][skey]))
        return reaped

    def is_session_expired(
        self,
        session_id: Optional[str] = None,
        ttl_seconds: int = 180,
        reference_time: Optional[datetime] = None,
    ) -> bool:
        sid = session_id or self.session_id
        skey = arango_key("ps", sid)
        sess = self.collections["pantograph_sessions"].get(skey)
        if not sess:
            return False
        if sess.get("status") in ("expired", "deadlocked"):
            return True
        ref_dt = reference_time or datetime.now(timezone.utc)
        lease_exp_str = sess.get("leaseExpiresAt")
        if lease_exp_str:
            return datetime.fromisoformat(lease_exp_str) <= ref_dt
        base_str = sess.get("lastHeartbeatAt") or sess.get("startedAt")
        if base_str:
            return (datetime.fromisoformat(base_str) + timedelta(seconds=ttl_seconds)) <= ref_dt
        return False

    def record_request(self, seq: int, raw: str, command: str, payload: dict[str, Any]) -> str:
        key = arango_key("prq", f"{self.session_id}:{seq}")
        self.collections["pantograph_requests"][key] = {
            "_key": key,
            "sessionId": self.session_id,
            "sequence": seq,
            "command": command,
            "payload": payload,
            "rawLine": raw,
        }
        return key

    def record_response(
        self,
        seq: int,
        request_key: str,
        raw: str,
        result: Any,
        command: str,
        payload: dict[str, Any],
    ) -> None:
        key = arango_key("prs", f"{self.session_id}:{seq}")
        self.collections["pantograph_responses"][key] = {
            "_key": key,
            "sessionId": self.session_id,
            "requestKey": request_key,
            "sequence": seq,
            "response": result,
            "rawLine": raw,
        }
        # Record states if present
        if isinstance(result, dict):
            children = []
            if command == "goal.start" and "stateId" in result:
                children.append(result["stateId"])
            elif command == "goal.tactic":
                next_id = result.get("nextStateId", result.get("nextStateId?"))
                if next_id is not None:
                    children.append(next_id)
            for child in children:
                skey = arango_key("pst", f"{self.session_id}:{child}")
                self.collections["pantograph_states"][skey] = {
                    "_key": skey,
                    "sessionId": self.session_id,
                    "stateId": child,
                    "goals": result.get("goals"),
                }

    def record_socratic_question(self, packet: dict[str, Any]) -> str:
        key = arango_key("psq", packet["id"])
        doc = dict(packet)
        doc["_key"] = key
        self.collections["pantograph_socratic_questions"][key] = doc
        return key

    def session_event(self, kind: str, data: dict[str, Any]) -> None:
        key = arango_key("pse", f"{self.session_id}:{kind}:{len(self.collections['pantograph_session_events'])}")
        self.collections["pantograph_session_events"][key] = {
            "_key": key,
            "kind": kind,
            "data": data,
        }


# ---------------------------------------------------------------------------
# Pantograph REPL Sessions
# ---------------------------------------------------------------------------

class PantographReplSession:
    """Interactive subprocess wrapper around Pantograph REPL binary."""

    def __init__(
        self,
        command: list[str],
        store: Any,
        cwd: Path,
        step_timeout: float = 15.0,
    ):
        self.command = command
        self.store = store
        self.cwd = cwd
        self.step_timeout = float(step_timeout)
        self.process: Optional[subprocess.Popen] = None
        self.seq = 0

    def start(self) -> None:
        self.process = subprocess.Popen(
            self.command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=self.cwd,
            text=True,
            bufsize=1,
        )
        assert self.process.stdout is not None
        greeting = self.process.stdout.readline().strip()
        if greeting != "ready.":
            stderr_out = ""
            if self.process.stderr:
                stderr_out = self.process.stderr.read()
            raise RuntimeError(f"Unexpected Pantograph greeting: {greeting!r}. Stderr: {stderr_out}")

    @staticmethod
    def read_response_with_timeout(stdout: Any, timeout: float) -> str:
        """Read one JSON value with strict timeout, accepting compact and pretty-printed responses."""
        start_time = time.monotonic()
        chunks: list[str] = []
        while True:
            elapsed = time.monotonic() - start_time
            remaining = timeout - elapsed
            if remaining <= 0:
                raise TimeoutError(f"Pantograph REPL response read timed out after {timeout:.1f}s")

            has_data = True
            if hasattr(stdout, "fileno"):
                try:
                    r, _, _ = select.select([stdout], [], [], max(0.01, remaining))
                    has_data = bool(r)
                except (io.UnsupportedOperation, ValueError):
                    has_data = True
            if not has_data:
                raise TimeoutError(f"Pantograph REPL response read timed out after {timeout:.1f}s")

            line = stdout.readline()
            if line == "":
                raise EOFError("Pantograph exited before returning a response")
            chunks.append(line)
            candidate = "".join(chunks).strip()
            try:
                json.loads(candidate)
                return candidate
            except json.JSONDecodeError:
                continue

    def execute_command(self, cmd: str, payload: dict[str, Any], timeout: Optional[float] = None) -> tuple[dict[str, Any], str, str]:
        if self.process is None or self.process.stdin is None or self.process.stdout is None:
            raise RuntimeError("Pantograph process is not running")

        effective_timeout = float(timeout) if timeout is not None else self.step_timeout
        self.seq += 1
        raw_request = canonical_json({"cmd": cmd, "payload": payload})
        req_key = self.store.record_request(self.seq, raw_request, cmd, payload)

        self.process.stdin.write(raw_request + "\n")
        self.process.stdin.flush()

        try:
            resp_raw = self.read_response_with_timeout(self.process.stdout, effective_timeout)
            resp_json = json.loads(resp_raw)
        except TimeoutError:
            # Process isolation: terminate hung REPL process to prevent runaway loops
            err_msg = f"Pantograph REPL tactic step timed out after {effective_timeout:.1f}s (process isolated)"
            self.close()
            try:
                self.start()
            except Exception:
                pass
            resp_json = {
                "error": "timeout",
                "desc": err_msg,
                "messages": [{
                    "severity": "error",
                    "caption": "timeout",
                    "data": f"TimeoutError: {err_msg}",
                }],
            }
            resp_raw = canonical_json(resp_json)

        self.store.record_response(self.seq, req_key, resp_raw, resp_json, cmd, payload)
        resp_key = arango_key("prs", f"{self.store.session_id}:{self.seq}")
        return resp_json, req_key, resp_key

    def close(self) -> None:
        if self.process is not None:
            if self.process.stdin:
                try:
                    self.process.stdin.close()
                except Exception:
                    pass
            self.process.terminate()
            try:
                self.process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                self.process.kill()
            self.process = None


class MockPantographReplSession:
    """In-memory mock REPL simulating Pantograph for dry-run verification."""

    def __init__(self, store: Any, step_timeout: float = 15.0):
        self.store = store
        self.step_timeout = float(step_timeout)
        self.seq = 0
        self.current_goal: Optional[str] = None
        self.state_counter = 0
        self.simulate_timeout: bool = False

    def start(self) -> None:
        pass

    def execute_command(self, cmd: str, payload: dict[str, Any], timeout: Optional[float] = None) -> tuple[dict[str, Any], str, str]:
        effective_timeout = float(timeout) if timeout is not None else self.step_timeout
        self.seq += 1
        raw_request = canonical_json({"cmd": cmd, "payload": payload})
        req_key = self.store.record_request(self.seq, raw_request, cmd, payload)

        resp_json: dict[str, Any]
        tactic_str = str(payload.get("tactic", "")).strip()
        if self.simulate_timeout or (cmd == "goal.tactic" and tactic_str in ("timeout", "loop", "sleep")):
            err_msg = f"Pantograph REPL tactic step timed out after {effective_timeout:.1f}s (process isolated)"
            resp_json = {
                "error": "timeout",
                "desc": err_msg,
                "messages": [{
                    "severity": "error",
                    "caption": "timeout",
                    "data": f"TimeoutError: {err_msg}",
                }],
            }
        elif cmd == "goal.start":
            expr = str(payload.get("expr", ""))
            self.current_goal = expr
            if "+ =" in expr or "syntax_error" in expr:
                resp_json = {
                    "error": "parse",
                    "desc": "<stdin>:1:4: expected term",
                }
            else:
                self.state_counter = 0
                resp_json = {
                    "root": f"_uniq.{self.seq}",
                    "stateId": self.state_counter,
                }
        elif cmd == "goal.tactic":
            tactic = tactic_str
            if tactic == "rfl":
                if self.current_goal in ("1 + 1 = 2", "x = x", "n = n"):
                    self.state_counter += 1
                    resp_json = {
                        "nextStateId": self.state_counter,
                        "goals": [],
                        "hasSorry": False,
                        "hasUnsafe": False,
                        "messages": [],
                    }
                else:
                    # Realistic reflexivity failure message
                    resp_json = {
                        "hasSorry": False,
                        "hasUnsafe": False,
                        "messages": [{
                            "severity": "error",
                            "caption": "",
                            "data": (
                                "Tactic `rfl` failed: The left-hand side\n"
                                "  n + 1\n"
                                "is not definitionally equal to the right-hand side\n"
                                "  1 + n\n\n"
                                "n : Nat\n"
                                "⊢ n + 1 = 1 + n"
                            ),
                        }],
                    }
            elif tactic == "intro n":
                self.state_counter += 1
                resp_json = {
                    "nextStateId": self.state_counter,
                    "goals": [{
                        "fragment": "tactic",
                        "name": f"_uniq.goal.{self.state_counter}",
                        "target": {"pp": "n + 1 = 1 + n"},
                        "vars": [{"userName": "n", "type": {"pp": "Nat"}}],
                    }],
                    "hasSorry": False,
                    "hasUnsafe": False,
                    "messages": [],
                }
            else:
                resp_json = {
                    "hasSorry": False,
                    "hasUnsafe": False,
                    "messages": [{
                        "severity": "error",
                        "caption": "",
                        "data": f"unknown tactic: {tactic}",
                    }],
                }
        else:
            resp_json = {"error": "unsupported_command", "desc": cmd}

        resp_raw = canonical_json(resp_json)
        self.store.record_response(self.seq, req_key, resp_raw, resp_json, cmd, payload)
        resp_key = arango_key("prs", f"{self.store.session_id}:{self.seq}")
        return resp_json, req_key, resp_key

    def close(self) -> None:
        pass


# ---------------------------------------------------------------------------
# Swarm Engine & Interactive Loop
# ---------------------------------------------------------------------------

class EpistemicSwarmEngine:
    """Coordinates candidate ingestion, Lean interaction, and Socratic generation."""

    def __init__(self, repl: Any, store: Any, step_timeout: float = 15.0):
        self.repl = repl
        self.store = store
        self.step_timeout = float(step_timeout)

    def process_candidate(self, candidate: CandidatePacket) -> CandidateResult:
        # Heartbeat active session at start of candidate processing
        if hasattr(self.store, "heartbeat_session"):
            self.store.heartbeat_session(self.store.session_id)

        executed_tactics: list[str] = []

        # 1. Start the goal for the formal target
        start_payload = {"expr": candidate.formal_target}
        resp, req_key, resp_key = self.repl.execute_command("goal.start", start_payload, timeout=self.step_timeout)

        # Check for elaboration / syntax error
        if "error" in resp or "parseError" in resp:
            err_desc = resp.get("desc") or resp.get("error") or "Failed to parse/elaborate formal target"
            qtype = classify_question_type(str(err_desc), is_elaboration=True)
            question = (
                f"Elaboration failed for formal target '{candidate.formal_target}': {err_desc}. "
                "How should the theorem signature, binder types, or notation be reformulated?"
            )
            socratic_pkt = build_socratic_packet(
                candidate_id=candidate.packet_id,
                session_id=self.store.session_id,
                formal_target=candidate.formal_target,
                question=question,
                question_type=qtype,
                exact_goal_state=f"ELABORATION_ERROR: {err_desc}",
                failed_tactic=None,
                error_message=str(err_desc),
                state_id=None,
                request_key=req_key,
                response_key=resp_key,
                parent_goal_hash=compute_subgoal_hash(candidate.formal_target),
                tactic_attempted=None,
                lean_error_code="LEAN_PARSE_ERROR" if "parse" in str(err_desc).lower() else "LEAN_ELABORATION_FAILED",
                cognitive_mode="DEFINITION_PRESSURE" if qtype == "definition_pressure" else "INSUFFICIENT_CARRIER_STRUCTURE",
                suggested_actions=["REFORMULATE_SIGNATURE", "IMPORT_MATHLIB_MODULE", "WEAKEN_TARGET"],
            )
            self.store.record_socratic_question(socratic_pkt)
            return CandidateResult(
                packet_id=candidate.packet_id,
                formal_target=candidate.formal_target,
                status="elaboration_failure",
                socratic_packet=socratic_pkt,
                error_message=str(err_desc),
            )

        current_state_id = resp.get("stateId", 0)
        current_goal_state_str = f"⊢ {candidate.formal_target}"
        last_goals: list[dict[str, Any]] = []

        # 1.5. Subgoal Cache Check (Tier 1.1 Alpha-Invariant Memoization)
        subgoal_hash = compute_subgoal_hash(candidate.formal_target)
        cached_entry = self.store.lookup_subgoal_cache(subgoal_hash)
        if cached_entry and cached_entry.get("tactics"):
            cached_tactics = [str(t) for t in cached_entry["tactics"]]
            cache_replay_ok = True
            cache_state_id = current_state_id
            cache_executed: list[str] = []
            for t_cached in cached_tactics:
                payload = {"stateId": cache_state_id, "tactic": t_cached}
                c_resp, _, _ = self.repl.execute_command("goal.tactic", payload, timeout=self.step_timeout)
                cache_executed.append(t_cached)
                c_msgs = c_resp.get("messages", [])
                if "error" in c_resp or any(m.get("severity") == "error" for m in c_msgs):
                    cache_replay_ok = False
                    break
                cache_state_id = c_resp.get("nextStateId", c_resp.get("nextStateId?", cache_state_id))
                c_goals = c_resp.get("goals", c_resp.get("goals?", []))
                if isinstance(c_goals, list) and len(c_goals) == 0:
                    return CandidateResult(
                        packet_id=candidate.packet_id,
                        formal_target=candidate.formal_target,
                        status="proved_via_subgoal_cache",
                        final_state_id=cache_state_id,
                        remaining_goals=[],
                        executed_tactics=cache_executed,
                    )

        # 2. Sequentially execute candidate tactics
        for tactic in candidate.tactics:
            # Heartbeat lease before tactic step
            if hasattr(self.store, "heartbeat_session"):
                self.store.heartbeat_session(self.store.session_id)

            tactic_payload = {"stateId": current_state_id, "tactic": tactic}
            tresp, treq_key, tresp_key = self.repl.execute_command("goal.tactic", tactic_payload, timeout=self.step_timeout)
            executed_tactics.append(tactic)

            # Check for tactic failure
            messages = tresp.get("messages", [])
            has_error = (
                "error" in tresp
                or "parseError" in tresp
                or tresp.get("nextStateId") is None and tresp.get("nextStateId?") is None
                or any(m.get("severity") == "error" for m in messages)
            )

            if has_error:
                error_lines = [m.get("data", "") for m in messages if m.get("severity") == "error"]
                error_text = "\n".join(error_lines) if error_lines else str(tresp.get("desc") or "Tactic failed")

                # Extract exact Lean goal state from messages or fall back to previous goal state
                extracted_goal = extract_goal_state_from_messages(messages)
                exact_goal = extracted_goal if extracted_goal else current_goal_state_str

                qtype = classify_question_type(error_text, is_elaboration=False)
                diag_kind, diag_payload = extract_typed_diagnostic(error_text, exact_goal)

                question = (
                    f"Tactic '{tactic}' failed with {diag_kind} on goal state:\n{exact_goal}\n"
                    f"Compiler diagnostic: {error_text}\n"
                    "What lemma, intermediate assertion, or hypothesis is needed to bypass this obstruction?"
                )
                parent_hash = compute_subgoal_hash(exact_goal)
                socratic_pkt = build_socratic_packet(
                    candidate_id=candidate.packet_id,
                    session_id=self.store.session_id,
                    formal_target=candidate.formal_target,
                    question=question,
                    question_type=qtype,
                    exact_goal_state=exact_goal,
                    failed_tactic=tactic,
                    error_message=error_text,
                    state_id=current_state_id,
                    request_key=treq_key,
                    response_key=tresp_key,
                    diagnostic_kind=diag_kind,
                    diagnostic_payload=diag_payload,
                    parent_goal_hash=parent_hash,
                    tactic_attempted=tactic,
                )
                self.store.record_socratic_question(socratic_pkt)
                return CandidateResult(
                    packet_id=candidate.packet_id,
                    formal_target=candidate.formal_target,
                    status="tactic_failure",
                    final_state_id=current_state_id,
                    remaining_goals=last_goals,
                    socratic_packet=socratic_pkt,
                    executed_tactics=executed_tactics,
                    error_message=error_text,
                )

            # Tactic succeeded: update state
            current_state_id = tresp.get("nextStateId", tresp.get("nextStateId?", current_state_id))
            goals = tresp.get("goals", tresp.get("goals?", []))
            last_goals = goals if isinstance(goals, list) else []
            if last_goals:
                current_goal_state_str = "\n---\n".join(format_goal_ast(g) for g in last_goals)
            else:
                current_goal_state_str = "No open goals"

            # Check if all goals were closed
            if isinstance(goals, list) and len(goals) == 0:
                # Memoize proven goal in subgoal cache (Tier 1.1)
                self.store.record_subgoal_cache(
                    subgoal_hash=subgoal_hash,
                    formal_target=candidate.formal_target,
                    tactics=executed_tactics,
                    session_id=self.store.session_id,
                )
                return CandidateResult(
                    packet_id=candidate.packet_id,
                    formal_target=candidate.formal_target,
                    status="proved",
                    final_state_id=current_state_id,
                    remaining_goals=[],
                    executed_tactics=executed_tactics,
                )

        # Tactics finished but goals remain open
        return CandidateResult(
            packet_id=candidate.packet_id,
            formal_target=candidate.formal_target,
            status="open_goals",
            final_state_id=current_state_id,
            remaining_goals=last_goals,
            executed_tactics=executed_tactics,
        )


# ---------------------------------------------------------------------------
# Self-Test / Dry-Run Verification
# ---------------------------------------------------------------------------

def run_dry_run_verification() -> bool:
    """Hermetic self-test checking end-to-end functionality without external services."""
    print("=== [PANTOGRAPH EPISTEMIC SWARM DRY-RUN SELF-TEST] ===")
    session_id = f"dry-run-session-{uuid.uuid4().hex[:8]}"
    store = MockEpistemicSwarmStore(session_id)
    store.start(["repl", "Init"], "dry-run-v1", None)
    repl = MockPantographReplSession(store)
    repl.start()
    engine = EpistemicSwarmEngine(repl, store)

    schema_store = build_store()
    socratic_schema = SCHEMA_BY_KIND["SocraticQuestionPacket"]

    # Scenario 1: Proved Candidate
    cand1 = CandidatePacket(
        packet_id="cand-dry-1",
        kind="TheoremCandidatePacket",
        formal_target="1 + 1 = 2",
        tactics=["rfl"],
    )
    res1 = engine.process_candidate(cand1)
    assert res1.status == "proved", f"Expected proved, got {res1.status}"
    assert res1.socratic_packet is None
    print("  [PASS] Scenario 1: Successful candidate proved (1 + 1 = 2 by rfl)")

    # Scenario 2: Tactic Failure Candidate
    cand2 = CandidatePacket(
        packet_id="cand-dry-2",
        kind="TheoremCandidatePacket",
        formal_target="forall (n : Nat), n + 1 = 1 + n",
        tactics=["rfl"],
    )
    res2 = engine.process_candidate(cand2)
    assert res2.status == "tactic_failure", f"Expected tactic_failure, got {res2.status}"
    assert res2.socratic_packet is not None
    assert "⊢ n + 1 = 1 + n" in res2.socratic_packet["exact_goal_state"]
    assert res2.socratic_packet["diagnostic_kind"] == DIAGNOSTIC_TYPE_MISMATCH
    assert res2.socratic_packet["diagnostic_payload"]["kind"] == DIAGNOSTIC_TYPE_MISMATCH
    assert res2.socratic_packet["tactic_attempted"] == "rfl"
    assert res2.socratic_packet["cognitive_mode"] == COGNITIVE_MODE_TYPE_MISMATCH
    assert res2.socratic_packet["lean_error_code"] == "LEAN_TYPE_MISMATCH"
    assert res2.socratic_packet["suggested_actions"] == ["CAST_EQUALITY", "COERCE_TYPES", "REWRITE_DEF"]
    assert len(res2.socratic_packet["parent_goal_hash"]) == 64
    # Schema check
    validation_errs = validate_packet(res2.socratic_packet, socratic_schema, schema_store)
    assert not validation_errs, f"Socratic packet schema violation: {validation_errs}"
    print("  [PASS] Scenario 2: Tactic failure generated valid SocraticQuestionPacket with typed diagnostic and enriched metadata")

    # Scenario 3: Elaboration Failure Candidate
    cand3 = CandidatePacket(
        packet_id="cand-dry-3",
        kind="TheoremCandidatePacket",
        formal_target="1 + = 2",
        tactics=["rfl"],
    )
    res3 = engine.process_candidate(cand3)
    assert res3.status == "elaboration_failure", f"Expected elaboration_failure, got {res3.status}"
    assert res3.socratic_packet is not None
    assert res3.socratic_packet["question_type"] == "definition_pressure"
    assert res3.socratic_packet["parent_goal_hash"] is not None
    assert res3.socratic_packet["suggested_actions"] is not None
    validation_errs = validate_packet(res3.socratic_packet, socratic_schema, schema_store)
    assert not validation_errs, f"Socratic packet schema violation: {validation_errs}"
    print("  [PASS] Scenario 3: Elaboration failure generated valid SocraticQuestionPacket")

    # Scenario 4: Subgoal Memoization Cache Hit (Tier 1.1)
    cand4 = CandidatePacket(
        packet_id="cand-dry-4",
        kind="TheoremCandidatePacket",
        formal_target="1 + 1 = 2",
        tactics=[],
    )
    res4 = engine.process_candidate(cand4)
    assert res4.status == "proved_via_subgoal_cache", f"Expected proved_via_subgoal_cache, got {res4.status}"
    assert res4.executed_tactics == ["rfl"]
    print("  [PASS] Scenario 4: Subgoal memoization cache hit proved identical target with 0 LLM queries")

    # Scenario 5: Process Isolation / Tactic Step Timeout
    cand5 = CandidatePacket(
        packet_id="cand-dry-5",
        kind="TheoremCandidatePacket",
        formal_target="forall (k : Nat), k + 0 = k",
        tactics=["timeout"],
    )
    res5 = engine.process_candidate(cand5)
    assert res5.status == "tactic_failure", f"Expected tactic_failure, got {res5.status}"
    assert res5.socratic_packet is not None
    assert res5.socratic_packet["cognitive_mode"] == COGNITIVE_MODE_TIMEOUT
    assert res5.socratic_packet["lean_error_code"] == "LEAN_TIMEOUT"
    assert "timeout" in (res5.error_message or "").lower()
    assert res5.socratic_packet["suggested_actions"] == ["SIMPLIFY_TACTIC", "PROVIDE_INTERMEDIATE_STEPS", "BOUND_MAX_HEURISTICS"]
    validation_errs5 = validate_packet(res5.socratic_packet, socratic_schema, schema_store)
    assert not validation_errs5, f"Timeout Socratic packet schema violation: {validation_errs5}"
    print("  [PASS] Scenario 5: Process isolation handled tactic step timeout gracefully with error packet")

    # Scenario 6: Lease Heartbeat & TTL Deadlock Management
    hb = store.heartbeat_session(session_id, ttl_seconds=180)
    assert hb["status"] == "active"
    assert hb["sessionId"] == session_id
    assert store.collections["pantograph_sessions"][store.session_key]["status"] == "active"

    now_dt = datetime.now(timezone.utc)
    assert not store.is_session_expired(session_id, ttl_seconds=180, reference_time=now_dt)

    future_dt = now_dt + timedelta(seconds=200)
    assert store.is_session_expired(session_id, ttl_seconds=180, reference_time=future_dt)
    expired = store.check_expired_sessions(ttl_seconds=180, reference_time=future_dt)
    assert len(expired) == 1
    assert expired[0]["sessionId"] == session_id
    reaped = store.reap_deadlocked_sessions(ttl_seconds=180, reference_time=future_dt)
    assert len(reaped) == 1
    assert store.collections["pantograph_sessions"][store.session_key]["status"] == "deadlocked"
    print("  [PASS] Scenario 6: Session lease heartbeat and TTL deadlock management verified")

    # Verify collection records
    assert len(store.collections["pantograph_sessions"]) == 1
    assert len(store.collections["pantograph_requests"]) >= 4
    assert len(store.collections["pantograph_responses"]) >= 4
    assert len(store.collections["pantograph_states"]) >= 1
    assert len(store.collections["pantograph_socratic_questions"]) == 3
    assert len(store.collections["pantograph_subgoal_cache"]) >= 1
    print("  [PASS] Collections recorded: sessions, requests, responses, states, socratic_questions, subgoal_cache")

    repl.close()
    print("=== [DRY-RUN / SELF-TEST COMPLETED SUCCESSFULLY] ===\n")
    return True


def run_live_verification(
    target: ArangoTarget,
    repl_bin: Path,
    project_root: Path,
    modules: list[str],
    use_lake_env: bool = False,
) -> bool:
    """End-to-end verification against live ArangoDB and the real Pantograph binary."""
    print("=== [PANTOGRAPH EPISTEMIC SWARM LIVE VERIFICATION] ===")
    session_id = f"live-verify-{uuid.uuid4().hex[:8]}"
    build_fingerprint = digest(canonical_json({"session": session_id}))

    store = EpistemicSwarmStore(target, session_id, build_fingerprint)
    store.ensure_collections()

    command: list[str] = []
    if use_lake_env:
        command = ["lake", "env", str(repl_bin)] + modules
    else:
        command = [str(repl_bin)] + modules

    store.start(command, "live-v1", None)
    repl = PantographReplSession(command, store, cwd=project_root)
    repl.start()
    engine = EpistemicSwarmEngine(repl, store)

    schema_store = build_store()
    socratic_schema = SCHEMA_BY_KIND["SocraticQuestionPacket"]

    # 1. Proved
    cand1 = CandidatePacket("cand-live-1", "TheoremCandidatePacket", "1 + 1 = 2", ["rfl"])
    res1 = engine.process_candidate(cand1)
    assert res1.status == "proved", f"Live proved failed: {res1.status}"
    print("  [PASS] Live Scenario 1: Proved 1 + 1 = 2")

    # 2. Tactic Failure
    cand2 = CandidatePacket("cand-live-2", "TheoremCandidatePacket", "forall (n : Nat), n + 1 = 1 + n", ["rfl"])
    res2 = engine.process_candidate(cand2)
    assert res2.status == "tactic_failure", f"Live tactic failure failed: {res2.status}"
    assert res2.socratic_packet is not None
    errs = validate_packet(res2.socratic_packet, socratic_schema, schema_store)
    assert not errs, f"Socratic schema errors: {errs}"
    print("  [PASS] Live Scenario 2: SocraticQuestionPacket generated on tactic failure")

    # 3. Elaboration Failure
    cand3 = CandidatePacket("cand-live-3", "TheoremCandidatePacket", "1 + = 2", ["rfl"])
    res3 = engine.process_candidate(cand3)
    assert res3.status == "elaboration_failure", f"Live elab failure failed: {res3.status}"
    assert res3.socratic_packet is not None
    errs = validate_packet(res3.socratic_packet, socratic_schema, schema_store)
    assert not errs, f"Socratic schema errors: {errs}"
    print("  [PASS] Live Scenario 3: SocraticQuestionPacket generated on elaboration failure")

    repl.close()

    # Query counts from ArangoDB
    for coll in ["pantograph_sessions", "pantograph_requests", "pantograph_responses", "pantograph_states"]:
        count_res = request_json("GET", db_url(target, f"/_api/collection/{coll}/count"), username=target.username, password=target.password)
        print(f"  [DB CHECK] {coll}: {count_res.get('count')} documents")

    print("=== [LIVE VERIFICATION COMPLETED SUCCESSFULLY] ===\n")
    return True


# ---------------------------------------------------------------------------
# CLI & Entry Point
# ---------------------------------------------------------------------------

def parse_args() -> argparse.Namespace:
    project_root = Path(__file__).resolve().parents[2]
    load_repo_arango_env(project_root)

    parser = argparse.ArgumentParser(
        description="Pantograph Epistemic Swarm: interactive bridge between creative generators and Lean 4."
    )
    parser.add_argument(
        "--dry-run", "--self-test",
        action="store_true",
        help="Run hermetic self-test suite without external ArangoDB or Pantograph dependencies.",
    )
    parser.add_argument(
        "--live-test",
        action="store_true",
        help="Run live self-test against local ArangoDB (port 8530) and the built Pantograph REPL binary.",
    )
    parser.add_argument(
        "--packet-json",
        type=str,
        help="Single raw/creative candidate packet as JSON string.",
    )
    parser.add_argument(
        "--packet-file",
        type=Path,
        help="Path to JSON file containing a candidate packet.",
    )
    parser.add_argument(
        "--packet-jsonl",
        type=Path,
        help="Path to JSONL file containing candidate packets to process in a stream.",
    )
    parser.add_argument(
        "--interactive",
        action="store_true",
        help="Run interactive loop on stdin/stdout.",
    )
    parser.add_argument(
        "--repl-bin",
        type=Path,
        default=project_root / "external_refs" / "Pantograph" / ".lake" / "build" / "bin" / "repl",
        help="Path to Pantograph REPL binary.",
    )
    parser.add_argument(
        "--modules",
        nargs="+",
        default=["Init"],
        help="Lean modules to load on startup (default: Init).",
    )
    parser.add_argument(
        "--lake-env",
        action="store_true",
        help="Run REPL wrapped in `lake env` to load project dependencies.",
    )
    parser.add_argument(
        "--source-snapshot",
        type=Path,
        help="Source file snapshot to bind an exact environment manifest.",
    )
    parser.add_argument(
        "--session-id",
        type=str,
        default=None,
        help="Custom session ID (defaults to auto-generated UUID).",
    )
    parser.add_argument(
        "--output-socratic",
        type=Path,
        help="File path to write emitted SocraticQuestionPackets as JSONL.",
    )
    parser.add_argument(
        "--step-timeout",
        type=float,
        default=15.0,
        help="Timeout in seconds per Pantograph REPL tactic step (default: 15.0s).",
    )
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    project_root = Path(__file__).resolve().parents[2]

    # Handle dry-run / self-test mode
    if args.dry_run:
        ok = run_dry_run_verification()
        return 0 if ok else 1

    # Configure target
    target = ArangoTarget(args.endpoint.rstrip("/"), args.database, args.username, args.password)

    # Handle live test mode
    if args.live_test:
        ok = run_live_verification(
            target=target,
            repl_bin=args.repl_bin,
            project_root=project_root,
            modules=args.modules,
            use_lake_env=args.lake_env,
        )
        return 0 if ok else 1

    # Ingest candidate packets from CLI arguments
    candidates: list[CandidatePacket] = []
    if args.packet_json:
        candidates.append(CandidatePacket.from_dict(json.loads(args.packet_json)))
    elif args.packet_file:
        raw_data = json.loads(args.packet_file.read_text(encoding="utf-8"))
        if isinstance(raw_data, list):
            candidates.extend(CandidatePacket.from_dict(item) for item in raw_data)
        elif isinstance(raw_data, dict):
            candidates.append(CandidatePacket.from_dict(raw_data))
    elif args.packet_jsonl:
        with open(args.packet_jsonl, "r", encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if line:
                    candidates.append(CandidatePacket.from_dict(json.loads(line)))

    # If no inputs and not interactive, show help
    if not candidates and not args.interactive and sys.stdin.isatty():
        print("No candidate packets provided. Use --packet-json, --packet-file, --packet-jsonl, --interactive, or --dry-run.")
        return 0

    # Initialize live session
    session_id = args.session_id or f"swarm-session-{uuid.uuid4().hex[:12]}"
    command: list[str] = []
    if args.lake_env:
        command = ["lake", "env", str(args.repl_bin)] + args.modules
    else:
        command = [str(args.repl_bin)] + args.modules

    env_manifest = None
    if args.source_snapshot:
        env_manifest = build_environment_manifest(project_root, args.source_snapshot, command)
    build_fingerprint = (
        env_manifest["fingerprint"]
        if env_manifest
        else digest(canonical_json({"session": session_id, "modules": args.modules}))
    )

    store = EpistemicSwarmStore(target, session_id, build_fingerprint, environment_manifest=env_manifest)
    store.ensure_collections()
    store.start(command, "swarm-v1", args.source_snapshot)

    repl = PantographReplSession(command, store, cwd=project_root, step_timeout=args.step_timeout)
    repl.start()
    engine = EpistemicSwarmEngine(repl, store, step_timeout=args.step_timeout)

    socratic_handle = None
    if args.output_socratic:
        args.output_socratic.parent.mkdir(parents=True, exist_ok=True)
        socratic_handle = open(args.output_socratic, "a", encoding="utf-8")

    try:
        # Process batch candidates
        for cand in candidates:
            res = engine.process_candidate(cand)
            out_obj = {
                "packetId": res.packet_id,
                "formalTarget": res.formal_target,
                "status": res.status,
                "executedTactics": res.executed_tactics,
                "finalStateId": res.final_state_id,
                "socraticPacket": res.socratic_packet,
            }
            print(json.dumps(out_obj, ensure_ascii=False))
            if res.socratic_packet and socratic_handle:
                socratic_handle.write(json.dumps(res.socratic_packet, ensure_ascii=False) + "\n")
                socratic_handle.flush()

        # Handle interactive loop if requested
        if args.interactive or (not candidates and not sys.stdin.isatty()):
            print(f"Pantograph Epistemic Swarm interactive loop started (session: {session_id})", file=sys.stderr)
            for line in sys.stdin:
                line = line.strip()
                if not line or line in ("quit", "exit"):
                    break
                try:
                    data = json.loads(line)
                    cand = CandidatePacket.from_dict(data)
                    res = engine.process_candidate(cand)
                    out_obj = {
                        "packetId": res.packet_id,
                        "formalTarget": res.formal_target,
                        "status": res.status,
                        "executedTactics": res.executed_tactics,
                        "finalStateId": res.final_state_id,
                        "socraticPacket": res.socratic_packet,
                    }
                    print(json.dumps(out_obj, ensure_ascii=False), flush=True)
                    if res.socratic_packet and socratic_handle:
                        socratic_handle.write(json.dumps(res.socratic_packet, ensure_ascii=False) + "\n")
                        socratic_handle.flush()
                except Exception as exc:
                    print(json.dumps({"error": str(exc)}), flush=True)

    finally:
        if socratic_handle:
            socratic_handle.close()
        repl.close()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
