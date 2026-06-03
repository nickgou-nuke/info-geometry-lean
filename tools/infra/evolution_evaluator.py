#!/usr/bin/env python3
"""Fitness evaluation for Hermes self-evolution.

Queries ArangoDB task outcomes (fossils/deadends) to compute a fitness score
for a given skill.  The score reflects how well the skill translates a pending
goal into a kernel-checked Lean proof.
"""

from __future__ import annotations

import json
import logging
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

logger = logging.getLogger("evolution_evaluator")


# ---------------------------------------------------------------------------
# ArangoDB helpers (lightweight, matching hive_arango_queue.py style)
# ---------------------------------------------------------------------------

def _auth_header(username: str, password: str) -> str:
    import base64
    token = base64.b64encode(f"{username}:{password}".encode()).decode()
    return f"Basic {token}"


def _sys_url(endpoint: str, path: str) -> str:
    return f"{endpoint.rstrip('/')}/{path.lstrip('/')}"


def _db_url(endpoint: str, database: str, path: str) -> str:
    return f"{endpoint.rstrip('/')}/_db/{quote(database)}/{path.lstrip('/')}"


def _request_json(
    method: str,
    url: str,
    *,
    username: str,
    password: str,
    payload: Any | None = None,
) -> Any:
    body = None if payload is None else json.dumps(payload, ensure_ascii=False).encode("utf-8")
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", _auth_header(username, password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc


def _aql(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    query: str,
    bind_vars: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """Execute an AQL query and return the results."""
    payload: dict[str, Any] = {"query": query}
    if bind_vars:
        payload["bindVars"] = bind_vars
    result = _request_json(
        "POST",
        _db_url(endpoint, database, "/_api/cursor"),
        username=username,
        password=password,
        payload=payload,
    )
    return result.get("result", [])


# ---------------------------------------------------------------------------
# Fitness model
# ---------------------------------------------------------------------------

@dataclass
class FitnessScore:
    """Evaluation result for a single skill version.

    Fitness is in [0, 1], where 1.0 means the skill always produces a
    correctly compiling proof in a single attempt.
    """
    skill_name: str
    generation: int
    fitness: float
    total_tasks: int
    succeeded: int
    failed: int
    avg_attempts_per_success: float       # only successful tasks
    avg_metabolic_cost_ms: float           # wall-clock per attempt (ms)
    common_failure_patterns: list[dict[str, Any]] = field(default_factory=list)
    timestamp: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())

    def brief(self) -> str:
        return (
            f"{self.skill_name} gen#{self.generation}: "
            f"fitness={self.fitness:.3f} "
            f"({self.succeeded}/{self.total_tasks} ok, "
            f"avg {self.avg_attempts_per_success:.1f} attempts)"
        )


# ---------------------------------------------------------------------------
# Evaluator
# ---------------------------------------------------------------------------

class EvolutionEvaluator:
    """Evaluates how well a skill performs against ArangoDB goals.

    Usage:
        evaluator = EvolutionEvaluator(endpoint, database, username, password)
        score = evaluator.evaluate_skill("lean-proof", generation=3,
                                         task_outcomes=[...])
    """

    def __init__(
        self,
        endpoint: str,
        database: str,
        username: str,
        password: str,
    ) -> None:
        self._ep = endpoint
        self._db = database
        self._user = username
        self._pass = password

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def evaluate_from_outcomes(
        self,
        skill_name: str,
        generation: int,
        outcomes: list[dict[str, Any]],
    ) -> FitnessScore:
        """Compute fitness from a list of task-outcome records.

        Each *outcome* dict should have the shape produced by
        ``hermes_self_evolver``::

            {
                "goal_key": str,
                "task_key": str,
                "status": "completed" | "failed",
                "attempts": int,
                "metabolic_cost_ms": float,
                "error_summary": str | None,       # for failures
                "failure_pattern": str | None,      # geometric_sector-like
            }
        """
        succeeded = [o for o in outcomes if o.get("status") == "completed"]
        failed = [o for o in outcomes if o.get("status") == "failed"]
        total = len(outcomes)
        ok = len(succeeded)
        nok = len(failed)

        if total == 0:
            return FitnessScore(
                skill_name=skill_name,
                generation=generation,
                fitness=0.0,
                total_tasks=0,
                succeeded=0,
                failed=0,
                avg_attempts_per_success=0.0,
                avg_metabolic_cost_ms=0.0,
            )

        success_rate = ok / total if total > 0 else 0.0
        avg_attempts = (
            sum(o.get("attempts", 1) for o in succeeded) / ok
            if ok > 0 else 99.0
        )

        avg_cost = (
            sum(o.get("metabolic_cost_ms", 0) for o in outcomes) / total
            if total > 0 else 0.0
        )

        # ----- fitness formula -----
        # Base: success rate
        # Penalty: each additional attempt beyond 1 halves the marginal value
        # Penalty: high cost (> 60s) slightly reduces score
        attempts_penalty = 1.0 / max(1.0, avg_attempts)
        cost_penalty = max(0.0, 1.0 - (avg_cost / 120_000.0))  # 0–120s range
        fitness = success_rate * 0.6 + attempts_penalty * 0.25 + cost_penalty * 0.15
        fitness = max(0.0, min(1.0, fitness))

        # Common failure patterns
        patterns: dict[str, int] = {}
        for o in failed:
            pat = o.get("failure_pattern") or o.get("error_summary", "unknown")[:120]
            patterns[pat] = patterns.get(pat, 0) + 1
        common = [
            {"pattern": pat, "count": cnt}
            for pat, cnt in sorted(patterns.items(), key=lambda x: -x[1])
        ][:10]

        return FitnessScore(
            skill_name=skill_name,
            generation=generation,
            fitness=round(fitness, 4),
            total_tasks=total,
            succeeded=ok,
            failed=nok,
            avg_attempts_per_success=round(avg_attempts, 2),
            avg_metabolic_cost_ms=round(avg_cost, 1),
            common_failure_patterns=common,
        )

    def list_open_goals(self, queue_name: str = "proof-search", limit: int = 20) -> list[dict[str, Any]]:
        """Query ArangoDB for pending/open goals on the given queue."""
        query = """
FOR task IN @@tasks
  FILTER task.queue_name == @queue_name
  FILTER task.status == "pending"
  SORT task.priority DESC, task.created_at ASC
  LIMIT @limit
  LET goal = DOCUMENT(@@goals, task.goal_key)
  RETURN {
    task_key: task._key,
    goal_key: task.goal_key,
    priority: task.priority,
    created_at: task.created_at,
    target_pretty: goal.target_pretty,
    module: goal.module,
    goal_index: goal.goal_index,
    formal_target: task.runtime_goal_packet.formal_target
  }
"""
        rows = _aql(
            self._ep,
            self._db,
            self._user,
            self._pass,
            query,
            {
                "@tasks": "hive_tasks",
                "@goals": "hive_goals",
                "queue_name": queue_name,
                "limit": limit,
            },
        )
        return rows

    def list_tasks_for_skill(
        self,
        skill_name: str,
        limit: int = 100,
    ) -> list[dict[str, Any]]:
        """Fetch tasks previously tagged with a given skill_name."""
        query = """
FOR task IN @@tasks
  FILTER task.skill_name == @skill_name
  SORT task.created_at DESC
  LIMIT @limit
  RETURN task
"""
        rows = _aql(
            self._ep,
            self._db,
            self._user,
            self._pass,
            query,
            {"@tasks": "hive_tasks", "skill_name": skill_name, "limit": limit},
        )
        return rows

    def queue_stats(self, queue_name: str = "proof-search") -> dict[str, Any]:
        """Summary stats for the given queue."""
        query = """
FOR task IN @@tasks
  FILTER task.queue_name == @queue_name
  COLLECT status = task.status WITH COUNT INTO count
  RETURN {status, count}
"""
        rows = _aql(
            self._ep, self._db, self._user, self._pass,
            query,
            {"@tasks": "hive_tasks", "queue_name": queue_name},
        )
        return {row["status"]: row["count"] for row in rows}


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------

def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Evaluate skill fitness against ArangoDB")
    parser.add_argument("--skill", default="lean-proof", help="Skill name to evaluate")
    parser.add_argument("--generation", type=int, default=0)
    parser.add_argument("--queue", default="proof-search")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    from tools.infra.arango_env import (
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )
    load_repo_arango_env(Path.cwd())

    ep = arango_endpoint()
    db = arango_database("hive_live")
    usr = arango_username()
    pwd = arango_password("alexandria_root")

    evaluator = EvolutionEvaluator(ep, db, usr, pwd)

    if args.dry_run:
        stats = evaluator.queue_stats(args.queue)
        print(f"Queue       : {args.queue}")
        print(f"Connection  : {ep}/{db}")
        for status, count in sorted(stats.items()):
            print(f"  {status}: {count}")
        open_goals = evaluator.list_open_goals(args.queue, limit=5)
        print(f"\nSample open goals ({len(open_goals)} shown):")
        for g in open_goals:
            print(f"  {g.get('target_pretty', '?')[:80]}")
        return

    # Evaluate from ArangoDB history
    tasks = evaluator.list_tasks_for_skill(args.skill, limit=100)
    outcomes = []
    for t in tasks:
        outcomes.append({
            "goal_key": t.get("goal_key", ""),
            "task_key": t.get("_key", ""),
            "status": t.get("status", "failed"),
            "attempts": t.get("claim_count", 1),
            "metabolic_cost_ms": 0,
            "error_summary": t.get("last_error", ""),
            "failure_pattern": None,
        })
    score = evaluator.evaluate_from_outcomes(args.skill, args.generation, outcomes)
    print(score.brief())
    if score.common_failure_patterns:
        print("Common failure patterns:")
        for p in score.common_failure_patterns[:5]:
            print(f"  x{p['count']} {p['pattern'][:100]}")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    main()
