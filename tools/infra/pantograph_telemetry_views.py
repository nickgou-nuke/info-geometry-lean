#!/usr/bin/env python3
"""Pantograph Proof Frontier Telemetry & ArangoDB Views.

Configures and queries ArangoDB views/AQL for live proof frontier telemetry:
  - Active and unresolved subgoals
  - Proof search depth
  - Elapsed seconds
  - Dead-route tactics
  - Failed vs succeeded tactics count and rates

Includes a `--cli-summary` mode for operator inspection and hermetic `--dry-run`
self-tests using in-memory mock data.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

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
from tools.infra.pantograph_arango_stream import query_all_rows  # noqa: E402


# ---------------------------------------------------------------------------
# View Definitions and AQL Query Templates
# ---------------------------------------------------------------------------

DEFAULT_VIEW_NAME = "pantograph_telemetry_view"

TELEMETRY_VIEW_DEFINITION = {
    "name": DEFAULT_VIEW_NAME,
    "type": "arangosearch",
    "links": {
        "pantograph_sessions": {
            "includeAllFields": True,
            "fields": {
                "sessionId": {"analyzers": ["identity"]},
                "startedAt": {"analyzers": ["identity"]},
            },
        },
        "pantograph_requests": {
            "includeAllFields": True,
            "fields": {
                "sessionId": {"analyzers": ["identity"]},
                "command": {"analyzers": ["identity"]},
                "sequence": {"analyzers": ["identity"]},
            },
        },
        "pantograph_responses": {
            "includeAllFields": True,
            "fields": {
                "sessionId": {"analyzers": ["identity"]},
                "status": {"analyzers": ["identity"]},
                "sequence": {"analyzers": ["identity"]},
            },
        },
        "pantograph_states": {
            "includeAllFields": True,
            "fields": {
                "sessionId": {"analyzers": ["identity"]},
                "stateId": {"analyzers": ["identity"]},
            },
        },
    },
}

AQL_SESSION_OVERVIEW = """
FOR s IN pantograph_sessions
  FILTER @sessionId == null OR s.sessionId == @sessionId OR s._key == @sessionId
  LET reqs = (
    FOR r IN pantograph_requests
      FILTER r.sessionKey == s._key OR r.sessionId == s.sessionId
      SORT r.sequence ASC
      RETURN r
  )
  LET resps = (
    FOR resp IN pantograph_responses
      FILTER resp.sessionKey == s._key OR resp.sessionId == s.sessionId
      RETURN resp
  )
  LET start_time = s.startedAt || FIRST(reqs).time
  LET end_time = LAST(resps).time || LAST(reqs).time || start_time
  LET elapsed = (start_time != null AND end_time != null) ? DATE_DIFF(start_time, end_time, "fsecond") / 1000.0 : 0.0
  RETURN {
    sessionKey: s._key,
    sessionId: s.sessionId,
    startedAt: start_time,
    lastEventAt: end_time,
    elapsedSeconds: elapsed,
    requestCount: LENGTH(reqs),
    responseCount: LENGTH(resps)
  }
"""

AQL_TACTIC_TELEMETRY = """
FOR r IN pantograph_requests
  FILTER (@sessionId == null OR r.sessionId == @sessionId OR r.sessionKey == @sessionId)
  FILTER r.command == "goal.tactic"
  LET resp = FIRST(
    FOR res IN pantograph_responses
      FILTER res.requestKey == r._key OR (res.sessionId == r.sessionId AND res.sequence == r.sequence)
      LIMIT 1
      RETURN res
  )
  LET is_failed = (resp == null OR resp.status == "failed" OR (resp.response != null AND resp.response.error != null))
  LET is_succeeded = (resp != null AND resp.status == "succeeded" AND (resp.response == null OR resp.response.error == null))
  LET state_from = r.payload.stateId
  LET next_state = resp != null AND resp.response != null ? (resp.response.nextStateId || resp.response["nextStateId?"]) : null
  RETURN {
    sessionId: r.sessionId,
    sequence: r.sequence,
    tactic: r.payload.tactic,
    stateFrom: state_from,
    nextState: next_state,
    status: resp != null ? resp.status : "unanswered",
    isFailed: is_failed,
    isSucceeded: is_succeeded,
    error: resp != null AND resp.response != null ? resp.response.error : null
  }
"""

AQL_STATES_AND_GOALS = """
FOR st IN pantograph_states
  FILTER (@sessionId == null OR st.sessionId == @sessionId OR st.sessionKey == @sessionId)
  LET child_trans = (
    FOR t IN pantograph_state_transitions
      FILTER t._from == st._id OR t._from == CONCAT("pantograph_states/", st._key)
      RETURN t
  )
  LET is_leaf = LENGTH(child_trans) == 0
  LET goals = st.goals
  LET goal_count = goals != null ? LENGTH(goals) : 0
  LET is_solved = goals != null AND goal_count == 0
  LET has_open_goals = goals != null AND goal_count > 0
  RETURN {
    sessionId: st.sessionId,
    stateId: st.stateId,
    stateKey: st._key,
    isLeaf: is_leaf,
    isSolved: is_solved,
    hasOpenGoals: has_open_goals,
    goalCount: goal_count,
    goals: goals
  }
"""

AQL_STATE_TRANSITIONS = """
FOR t IN pantograph_state_transitions
  FILTER (@sessionId == null OR t.sessionId == @sessionId)
  RETURN {
    from: t._from,
    to: t._to,
    sessionId: t.sessionId,
    sequence: t.sequence,
    command: t.command
  }
"""


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

@dataclass
class SubgoalDetail:
    """Detailed representation of an unresolved proof goal."""
    state_id: int
    goal_index: int
    target: str
    hypotheses: list[str] = field(default_factory=list)
    raw_goal: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "state_id": self.state_id,
            "goal_index": self.goal_index,
            "target": self.target,
            "hypotheses": list(self.hypotheses),
            "raw_goal": dict(self.raw_goal),
        }


@dataclass
class ProofFrontierTelemetry:
    """Consolidated telemetry snapshot for proof exploration."""
    session_id: str
    status: str
    elapsed_seconds: float
    search_depth: int
    active_frontier_states: list[int]
    active_subgoals_count: int
    unresolved_subgoals: list[SubgoalDetail]
    total_tactics_count: int
    succeeded_tactics_count: int
    failed_tactics_count: int
    dead_route_tactics_count: int
    success_rate: float
    dead_route_rate: float

    def to_dict(self) -> dict[str, Any]:
        return {
            "session_id": self.session_id,
            "status": self.status,
            "elapsed_seconds": round(self.elapsed_seconds, 2),
            "search_depth": self.search_depth,
            "active_frontier_states": list(self.active_frontier_states),
            "active_subgoals_count": self.active_subgoals_count,
            "unresolved_subgoals": [g.to_dict() for g in self.unresolved_subgoals],
            "total_tactics_count": self.total_tactics_count,
            "succeeded_tactics_count": self.succeeded_tactics_count,
            "failed_tactics_count": self.failed_tactics_count,
            "dead_route_tactics_count": self.dead_route_tactics_count,
            "success_rate": round(self.success_rate, 2),
            "dead_route_rate": round(self.dead_route_rate, 2),
        }


# ---------------------------------------------------------------------------
# Core Telemetry Engine
# ---------------------------------------------------------------------------

def ensure_telemetry_view(
    target: ArangoTarget,
    view_name: str = DEFAULT_VIEW_NAME,
) -> dict[str, Any]:
    """Ensure that the ArangoSearch telemetry view exists."""
    url = db_url(target, f"/_api/view/{view_name}")
    try:
        existing = request_json("GET", url, username=target.username, password=target.password)
        if isinstance(existing, dict) and existing.get("name") == view_name:
            return existing
    except Exception:
        pass

    view_def = dict(TELEMETRY_VIEW_DEFINITION)
    view_def["name"] = view_name
    create_url = db_url(target, "/_api/view")
    res = request_json(
        "POST", create_url,
        username=target.username, password=target.password,
        payload=view_def,
    )
    return res if isinstance(res, dict) else {}


def compute_telemetry_from_records(
    session_id: str,
    sessions_data: list[dict[str, Any]],
    requests_data: list[dict[str, Any]],
    responses_data: list[dict[str, Any]],
    states_data: list[dict[str, Any]],
    transitions_data: list[dict[str, Any]],
) -> ProofFrontierTelemetry:
    """Hermetic telemetry calculator operating over raw document dictionaries."""
    # 1. Session Timing & Elapsed Seconds
    matching_sessions = [s for s in sessions_data if s.get("sessionId") == session_id or s.get("_key") == session_id]
    session_doc = matching_sessions[0] if matching_sessions else {}

    matching_reqs = sorted(
        [r for r in requests_data if r.get("sessionId") == session_id],
        key=lambda r: r.get("sequence", 0),
    )
    matching_resps = [r for r in responses_data if r.get("sessionId") == session_id]

    start_iso = session_doc.get("startedAt") or (matching_reqs[0].get("time") if matching_reqs else None)
    end_iso = (matching_resps[-1].get("time") if matching_resps else None) or (
        matching_reqs[-1].get("time") if matching_reqs else start_iso
    )

    elapsed_seconds = 0.0
    if start_iso and end_iso:
        try:
            t0 = datetime.fromisoformat(start_iso.replace("Z", "+00:00"))
            t1 = datetime.fromisoformat(end_iso.replace("Z", "+00:00"))
            elapsed_seconds = max(0.0, (t1 - t0).total_seconds())
        except Exception:
            elapsed_seconds = 0.0

    # 2. Tactic Success / Failure Metrics
    resp_by_key = {r.get("requestKey"): r for r in matching_resps if r.get("requestKey")}
    resp_by_seq = {r.get("sequence"): r for r in matching_resps if r.get("sequence") is not None}

    tactics = [r for r in matching_reqs if r.get("command") == "goal.tactic"]
    total_tactics = len(tactics)
    failed_tactics = 0
    succeeded_tactics = 0
    failed_seqs: set[int] = set()

    for req in tactics:
        seq = req.get("sequence")
        resp = resp_by_key.get(req.get("_key")) or resp_by_seq.get(seq)
        is_failed = False
        if not resp:
            is_failed = True
        else:
            status = resp.get("status")
            resp_body = resp.get("response", {})
            has_error = isinstance(resp_body, dict) and ("error" in resp_body or "parseError" in resp_body)
            if status == "failed" or has_error:
                is_failed = True
            elif status == "succeeded":
                succeeded_tactics += 1

        if is_failed:
            failed_tactics += 1
            if seq is not None:
                failed_seqs.add(seq)

    # 3. State Analysis, Unresolved Subgoals & Frontier Leaves
    state_children: dict[int, list[int]] = {}
    state_parents: dict[int, list[int]] = {}
    for st in states_data:
        sid = int(st.get("stateId", 0))
        state_children.setdefault(sid, [])
        state_parents.setdefault(sid, [])

    for tr in transitions_data:
        if tr.get("sessionId") != session_id:
            continue
        # Extract from / to state IDs
        from_str = tr.get("_from", "")
        to_str = tr.get("_to", "")
        # Can be format "pantograph_states/pst_..." or stateId
        from_key = from_str.split("/")[-1] if "/" in from_str else from_str
        to_key = to_str.split("/")[-1] if "/" in to_str else to_str

        # Match to state IDs
        from_sid = None
        to_sid = None
        for st in states_data:
            if st.get("_key") == from_key or str(st.get("stateId")) == from_key:
                from_sid = int(st.get("stateId", 0))
            if st.get("_key") == to_key or str(st.get("stateId")) == to_key:
                to_sid = int(st.get("stateId", 0))

        if from_sid is not None and to_sid is not None:
            state_children.setdefault(from_sid, []).append(to_sid)
            state_parents.setdefault(to_sid, []).append(from_sid)

    # 4. Search Depth Calculation (Shortest Path from Root State 0 via BFS)
    depths: dict[int, int] = {0: 0}
    queue: list[int] = [0]
    while queue:
        curr = queue.pop(0)
        curr_d = depths[curr]
        for child in state_children.get(curr, []):
            if child not in depths or depths[child] > curr_d + 1:
                depths[child] = curr_d + 1
                queue.append(child)

    search_depth = max(depths.values()) if depths else 0

    # 5. Active Frontier States & Unresolved Subgoals
    active_frontier_states: list[int] = []
    unresolved_subgoals: list[SubgoalDetail] = []
    is_fully_solved = False

    for st in states_data:
        if st.get("sessionId") != session_id:
            continue
        sid = int(st.get("stateId", 0))
        goals = st.get("goals")
        is_leaf = len(state_children.get(sid, [])) == 0

        if goals is not None and len(goals) == 0:
            is_fully_solved = True

        if is_leaf and goals:
            active_frontier_states.append(sid)
            for g_idx, goal in enumerate(goals):
                target_str = ""
                hyps: list[str] = []
                if isinstance(goal, dict):
                    target_str = str(goal.get("target") or goal.get("pp") or goal.get("claim") or "")
                    hyps_raw = goal.get("vars") or goal.get("hypotheses") or []
                    if isinstance(hyps_raw, list):
                        hyps = [str(h) for h in hyps_raw]
                elif isinstance(goal, str):
                    target_str = goal

                unresolved_subgoals.append(
                    SubgoalDetail(
                        state_id=sid,
                        goal_index=g_idx,
                        target=target_str,
                        hypotheses=hyps,
                        raw_goal=goal if isinstance(goal, dict) else {"target": target_str},
                    )
                )

    # 6. Dead-Route Tactics Calculation
    # Dead routes = failed tactics + successful tactics whose resulting state became an abandoned leaf with open goals
    abandoned_leaves = {
        sid for sid, children in state_children.items()
        if len(children) == 0 and sid not in depths and sid != 0
    }
    dead_route_count = failed_tactics
    for req in tactics:
        seq = req.get("sequence")
        resp = resp_by_key.get(req.get("_key")) or resp_by_seq.get(seq)
        if resp and resp.get("status") == "succeeded":
            next_sid = resp.get("response", {}).get("nextStateId")
            if next_sid in abandoned_leaves:
                dead_route_count += 1

    success_rate = (succeeded_tactics / total_tactics * 100.0) if total_tactics > 0 else 0.0
    dead_route_rate = (dead_route_count / total_tactics * 100.0) if total_tactics > 0 else 0.0

    session_status = "IN_PROGRESS"
    if is_fully_solved:
        session_status = "PROVEN"
    elif not active_frontier_states and failed_tactics > 0:
        session_status = "FAILED"

    return ProofFrontierTelemetry(
        session_id=session_id,
        status=session_status,
        elapsed_seconds=elapsed_seconds,
        search_depth=search_depth,
        active_frontier_states=sorted(active_frontier_states),
        active_subgoals_count=len(unresolved_subgoals),
        unresolved_subgoals=unresolved_subgoals,
        total_tactics_count=total_tactics,
        succeeded_tactics_count=succeeded_tactics,
        failed_tactics_count=failed_tactics,
        dead_route_tactics_count=dead_route_count,
        success_rate=success_rate,
        dead_route_rate=dead_route_rate,
    )


def query_telemetry_live(
    target: ArangoTarget,
    session_id: Optional[str] = None,
) -> list[ProofFrontierTelemetry]:
    """Execute live AQL queries against ArangoDB to assemble frontier telemetry."""
    bind = {"sessionId": session_id}
    sessions = query_all_rows(target, AQL_SESSION_OVERVIEW, bind)
    reqs = query_all_rows(target, AQL_TACTIC_TELEMETRY, bind)
    states = query_all_rows(target, AQL_STATES_AND_GOALS, bind)
    trans = query_all_rows(target, AQL_STATE_TRANSITIONS, bind)

    target_session_ids = [s.get("sessionId") for s in sessions if s.get("sessionId")]
    if not target_session_ids and session_id:
        target_session_ids = [session_id]

    results: list[ProofFrontierTelemetry] = []
    for sid in target_session_ids:
        s_data = [s for s in sessions if s.get("sessionId") == sid]
        r_data = [r for r in reqs if r.get("sessionId") == sid]
        st_data = [st for st in states if st.get("sessionId") == sid]
        tr_data = [t for t in trans if t.get("sessionId") == sid]

        # Convert to records format expected by calculator
        telemetry = compute_telemetry_from_records(
            session_id=sid,
            sessions_data=s_data,
            requests_data=r_data,
            responses_data=r_data,  # responses are pre-joined in AQL_TACTIC_TELEMETRY
            states_data=st_data,
            transitions_data=tr_data,
        )
        results.append(telemetry)

    return results


# ---------------------------------------------------------------------------
# CLI Summary Printer
# ---------------------------------------------------------------------------

def print_cli_summary(telemetries: list[ProofFrontierTelemetry]) -> None:
    """Format and print an executive telemetry summary report to stdout."""
    border = "=" * 80
    divider = "-" * 80

    for t in telemetries:
        print(border)
        print(f"🔍 PANTOGRAPH PROOF FRONTIER TELEMETRY SUMMARY")
        print(border)
        print(f"  Session ID:              {t.session_id}")
        print(f"  Frontier Status:         {t.status}")
        print(f"  Elapsed Duration:        {t.elapsed_seconds:.2f}s")
        print(f"  Proof Search Depth:      {t.search_depth}")
        print(f"  Active Frontier States:  {t.active_frontier_states}")
        print(f"  Active Open Subgoals:    {t.active_subgoals_count}")
        print(divider)
        print("📊 TACTIC PERFORMANCE METRICS:")
        print(f"  Total Tactics Evaluated: {t.total_tactics_count}")
        print(f"  Succeeded Tactics:       {t.succeeded_tactics_count} ({t.success_rate:.1f}%)")
        print(f"  Failed Tactics:          {t.failed_tactics_count} ({100.0 - t.success_rate if t.total_tactics_count else 0:.1f}%)")
        print(f"  Dead-Route Tactics:      {t.dead_route_tactics_count} ({t.dead_route_rate:.1f}%)")
        print(divider)
        print(f"🎯 ACTIVE UNRESOLVED SUBGOAL FRONTIER ({len(t.unresolved_subgoals)}):")
        if not t.unresolved_subgoals:
            print("  (No unresolved subgoals. Proof frontier closed or solved.)")
        else:
            for g in t.unresolved_subgoals:
                print(f"  • [State {g.state_id} | Goal #{g.goal_index}]")
                print(f"      Target: ⊢ {g.target}")
                if g.hypotheses:
                    print(f"      Hypotheses: {', '.join(g.hypotheses)}")
        print(border)
        print()


# ---------------------------------------------------------------------------
# Hermetic Mock Data & Self-Tests (Dry-Run)
# ---------------------------------------------------------------------------

def run_hermetic_dry_run() -> None:
    """Execute dry-run self-tests using in-memory mock Pantograph data."""
    print("=" * 80)
    print("🚀 [DRY-RUN] Executing Pantograph Proof Frontier Telemetry Verification")
    print("=" * 80)

    # 1. Synthesize Mock Session Documents
    session_id = "session-test-fisher-01"
    start_time = "2026-10-14T20:00:00Z"

    sessions = [{
        "_key": "ps_mock_01",
        "sessionId": session_id,
        "startedAt": start_time,
        "pantographVersion": "0.3.0",
    }]

    # States:
    # State 0: Initial root goal (PosDef (fisher_metric p))
    # State 1: After 'intro v' (Integrable, Variance > 0)
    # State 2: After 'sorry' on goal 0 (Variance > 0 remaining)
    # State 3: Active frontier state (Variance > 0)
    # State 4: Dead-end branch state from State 1
    states = [
        {
            "_key": "pst_0",
            "sessionId": session_id,
            "stateId": 0,
            "goals": [{"target": "PosDef (fisher_metric p)", "vars": ["p : M"]}],
        },
        {
            "_key": "pst_1",
            "sessionId": session_id,
            "stateId": 1,
            "goals": [
                {"target": "Integrable (score_function p)", "vars": ["p : M"]},
                {"target": "Variance (score_function p v) > 0", "vars": ["p : M", "v : TangentSpace M p"]},
            ],
        },
        {
            "_key": "pst_2",
            "sessionId": session_id,
            "stateId": 2,
            "goals": [
                {"target": "Variance (score_function p v) > 0", "vars": ["p : M", "v : TangentSpace M p"]},
            ],
        },
        {
            "_key": "pst_3",
            "sessionId": session_id,
            "stateId": 3,
            "goals": [
                {"target": "Variance (score_function p v) > 0", "vars": ["p : M", "v : TangentSpace M p"]},
            ],
        },
        {
            "_key": "pst_4",
            "sessionId": session_id,
            "stateId": 4,
            "goals": [
                {"target": "False", "vars": ["p : M"]},
            ],
        },
    ]

    # Requests & Responses:
    # Req 1: goal.start -> State 0
    # Req 2: goal.tactic "intro v" -> State 1 (Succeeded)
    # Req 3: goal.tactic "bogus_tactic" on State 1 -> Failed!
    # Req 4: goal.tactic "ring" on State 1 -> Failed!
    # Req 5: goal.tactic "exact sorry" on State 1 -> State 2 (Succeeded)
    # Req 6: goal.tactic "simp" on State 2 -> State 3 (Succeeded, active leaf)
    # Req 7: goal.tactic "nlinarith" on State 1 -> State 4 (Succeeded, but dead branch)
    requests = [
        {"_key": "prq_1", "sessionId": session_id, "sequence": 1, "command": "goal.start", "payload": {}, "time": "2026-10-14T20:00:01Z"},
        {"_key": "prq_2", "sessionId": session_id, "sequence": 2, "command": "goal.tactic", "payload": {"stateId": 0, "tactic": "intro v"}, "time": "2026-10-14T20:00:03Z"},
        {"_key": "prq_3", "sessionId": session_id, "sequence": 3, "command": "goal.tactic", "payload": {"stateId": 1, "tactic": "bogus_tactic"}, "time": "2026-10-14T20:00:05Z"},
        {"_key": "prq_4", "sessionId": session_id, "sequence": 4, "command": "goal.tactic", "payload": {"stateId": 1, "tactic": "ring"}, "time": "2026-10-14T20:00:07Z"},
        {"_key": "prq_5", "sessionId": session_id, "sequence": 5, "command": "goal.tactic", "payload": {"stateId": 1, "tactic": "exact sorry"}, "time": "2026-10-14T20:00:10Z"},
        {"_key": "prq_6", "sessionId": session_id, "sequence": 6, "command": "goal.tactic", "payload": {"stateId": 2, "tactic": "simp"}, "time": "2026-10-14T20:00:12Z"},
        {"_key": "prq_7", "sessionId": session_id, "sequence": 7, "command": "goal.tactic", "payload": {"stateId": 1, "tactic": "nlinarith"}, "time": "2026-10-14T20:00:15Z"},
    ]

    responses = [
        {"_key": "prs_1", "sessionId": session_id, "sequence": 1, "requestKey": "prq_1", "status": "succeeded", "response": {"stateId": 0}, "time": "2026-10-14T20:00:01Z"},
        {"_key": "prs_2", "sessionId": session_id, "sequence": 2, "requestKey": "prq_2", "status": "succeeded", "response": {"nextStateId": 1}, "time": "2026-10-14T20:00:03Z"},
        {"_key": "prs_3", "sessionId": session_id, "sequence": 3, "requestKey": "prq_3", "status": "failed", "response": {"error": "unknown identifier 'bogus_tactic'"}, "time": "2026-10-14T20:00:05Z"},
        {"_key": "prs_4", "sessionId": session_id, "sequence": 4, "requestKey": "prq_4", "status": "failed", "response": {"error": "ring failed to close goal"}, "time": "2026-10-14T20:00:07Z"},
        {"_key": "prs_5", "sessionId": session_id, "sequence": 5, "requestKey": "prq_5", "status": "succeeded", "response": {"nextStateId": 2}, "time": "2026-10-14T20:00:10Z"},
        {"_key": "prs_6", "sessionId": session_id, "sequence": 6, "requestKey": "prq_6", "status": "succeeded", "response": {"nextStateId": 3}, "time": "2026-10-14T20:00:12Z"},
        {"_key": "prs_7", "sessionId": session_id, "sequence": 7, "requestKey": "prq_7", "status": "succeeded", "response": {"nextStateId": 4}, "time": "2026-10-14T20:00:15Z"},
    ]

    transitions = [
        {"_from": "pantograph_states/pst_0", "_to": "pantograph_states/pst_1", "sessionId": session_id, "sequence": 2},
        {"_from": "pantograph_states/pst_1", "_to": "pantograph_states/pst_2", "sessionId": session_id, "sequence": 5},
        {"_from": "pantograph_states/pst_2", "_to": "pantograph_states/pst_3", "sessionId": session_id, "sequence": 6},
        {"_from": "pantograph_states/pst_1", "_to": "pantograph_states/pst_4", "sessionId": session_id, "sequence": 7},
    ]

    # 2. Run Telemetry Computation
    telemetry = compute_telemetry_from_records(
        session_id=session_id,
        sessions_data=sessions,
        requests_data=requests,
        responses_data=responses,
        states_data=states,
        transitions_data=transitions,
    )

    print("✓ In-memory telemetry computation complete.")

    # 3. Assertions
    assert telemetry.session_id == session_id
    print(f"✓ Session ID verified: {telemetry.session_id}")

    assert math.isclose(telemetry.elapsed_seconds, 15.0, abs_tol=0.1), f"Elapsed seconds mismatch: {telemetry.elapsed_seconds}"
    print(f"✓ Elapsed seconds verified: {telemetry.elapsed_seconds:.2f}s")

    assert telemetry.search_depth == 3, f"Search depth mismatch: expected 3, got {telemetry.search_depth}"
    print(f"✓ Search depth verified: {telemetry.search_depth}")

    assert telemetry.total_tactics_count == 6, f"Expected 6 tactics, got {telemetry.total_tactics_count}"
    assert telemetry.failed_tactics_count == 2, f"Expected 2 failed tactics, got {telemetry.failed_tactics_count}"
    assert telemetry.succeeded_tactics_count == 4, f"Expected 4 succeeded tactics, got {telemetry.succeeded_tactics_count}"
    assert telemetry.dead_route_tactics_count >= 2, f"Dead routes expected >= 2, got {telemetry.dead_route_tactics_count}"
    print(f"✓ Tactic metrics verified: {telemetry.succeeded_tactics_count} succeeded, {telemetry.failed_tactics_count} failed, {telemetry.dead_route_tactics_count} dead routes")

    assert 3 in telemetry.active_frontier_states, f"State 3 must be in active frontier: {telemetry.active_frontier_states}"
    assert telemetry.active_subgoals_count >= 1, f"Expected active subgoals, got {telemetry.active_subgoals_count}"
    print(f"✓ Active frontier states: {telemetry.active_frontier_states}, subgoals: {telemetry.active_subgoals_count}")

    # 4. View Definition Verification
    assert TELEMETRY_VIEW_DEFINITION["name"] == DEFAULT_VIEW_NAME
    assert "pantograph_requests" in TELEMETRY_VIEW_DEFINITION["links"]
    assert "pantograph_responses" in TELEMETRY_VIEW_DEFINITION["links"]
    print("✓ ArangoSearch view definition structure verified.")

    # 5. Render CLI Summary
    print("\n" + "=" * 80)
    print("OUTPUT OF --cli-summary (DRY-RUN):")
    print("=" * 80)
    print_cli_summary([telemetry])

    # 6. JSON Export Round-Trip
    json_repr = json.dumps(telemetry.to_dict())
    parsed = json.loads(json_repr)
    assert parsed["session_id"] == session_id
    assert parsed["search_depth"] == 3
    print("✓ JSON serialization round-trip verified.")

    print("✅ All hermetic dry-run self-tests PASSED successfully!")


# ---------------------------------------------------------------------------
# CLI Entrypoint
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Pantograph Proof Frontier Telemetry & ArangoDB Views"
    )
    parser.add_argument(
        "--session-id",
        type=str,
        help="Target Pantograph session ID to inspect.",
    )
    parser.add_argument(
        "--cli-summary",
        action="store_true",
        help="Print formatted proof frontier summary and tactic success/failure metrics.",
    )
    parser.add_argument(
        "--configure-view",
        action="store_true",
        help="Configure or ensure ArangoSearch telemetry view in the database.",
    )
    parser.add_argument(
        "--view-name",
        type=str,
        default=DEFAULT_VIEW_NAME,
        help=f"Name of the ArangoSearch telemetry view (default: {DEFAULT_VIEW_NAME}).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output raw telemetry metrics in JSON format.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Execute hermetic self-tests using in-memory mock data without connecting to ArangoDB.",
    )
    parser.add_argument(
        "--endpoint",
        type=str,
        default=None,
        help="ArangoDB HTTP endpoint (defaults to environment or repo settings).",
    )
    parser.add_argument(
        "--database",
        type=str,
        default=None,
        help="ArangoDB database name (defaults to environment or repo settings).",
    )
    parser.add_argument(
        "--username",
        type=str,
        default=None,
        help="ArangoDB username.",
    )
    parser.add_argument(
        "--password",
        type=str,
        default=None,
        help="ArangoDB password.",
    )

    args = parser.parse_args()

    if args.dry_run or (not args.session_id and not args.configure_view and not args.cli_summary and not args.json):
        run_hermetic_dry_run()
        return

    # ArangoDB Target Resolution
    endpoint = args.endpoint or arango_endpoint()
    database = args.database or arango_database()
    username = args.username or arango_username()
    password = args.password or arango_password()
    target = ArangoTarget(endpoint=endpoint, database=database, username=username, password=password)

    if args.configure_view:
        res = ensure_telemetry_view(target, view_name=args.view_name)
        print(f"Ensured ArangoSearch view {args.view_name!r}: {res}")

    telemetries = query_telemetry_live(target, session_id=args.session_id)

    if args.json:
        print(json.dumps([t.to_dict() for t in telemetries], indent=2))
    elif args.cli_summary or not args.configure_view:
        print_cli_summary(telemetries)


if __name__ == "__main__":
    main()
