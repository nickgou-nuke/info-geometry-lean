#!/usr/bin/env python3
"""Autonomous evolution worker — daemon that polls ArangoDB for evolution tasks.

Runs as a background service: picks up "TO BE EVOLVED" skill tasks, runs the
full GEPA + RealEvaluator + Proof Seeker + Vacuity Critic pipeline, and
writes evolved skills back to the queue.

Usage:
    # Foreground (for testing)
    python3 tools/infra/evolution_worker.py --once

    # Systemd service
    python3 tools/infra/evolution_worker.py
"""

from __future__ import annotations

import hashlib
import json
import logging
import os
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Optional

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

from tools.infra.arango_env import (
    arango_database, arango_endpoint, arango_password,
    arango_username, load_repo_arango_env,
)
from tools.infra.hive_arango_queue import (
    aql, claim_next_task, complete_task, fail_task, enqueue_goal,
    queue_stats,
)

logger = logging.getLogger("evolution_worker")

POLL_INTERVAL = 5  # seconds between polls (aggressive)
LEASE_SECONDS = 1800  # 30 min lease per task
WORKER_ID = "evolution-worker-autonomous"
EVOLUTION_QUEUE = "skill-evolution"
EVOLVED_SKILL_DIR = _REPO / "quarantine" / "hermes_skills" / "evolved"


def ensure_evolution_queue() -> None:
    """Ensure the evolution queue and related collections exist."""
    from tools.infra.hive_arango_queue import ensure_collection, CollectionSpec, ensure_index, IndexSpec

    load_repo_arango_env(_REPO)
    ep = arango_endpoint()
    db = arango_database("hive_live")
    usr = arango_username()
    pwd = arango_password("alexandria_root")

    ensure_collection(ep, db, usr, pwd, CollectionSpec("hive_evolution_runs"))
    ensure_collection(ep, db, usr, pwd, CollectionSpec("hive_evolution_skills"))
    logger.info("Evolution queue initialized")


def enqueue_evolution_task(
    skill_name: str,
    skill_path: str,
    generations: int = 10,
    eval_tasks: int = 3,
) -> dict[str, Any]:
    """Enqueue a skill evolution task in ArangoDB."""
    load_repo_arango_env(_REPO)
    ep = arango_endpoint()
    db = arango_database("hive_live")
    usr = arango_username()
    pwd = arango_password("alexandria_root")

    target = f"Evolve skill `{skill_name}` ({generations} gen, {eval_tasks} tasks)"
    import hashlib
    goal_hash = hashlib.sha256(target.encode()).hexdigest()[:24]

    result = enqueue_goal(
        ep, db, usr, pwd,
        queue_name=EVOLUTION_QUEUE,
        goal_hash_shape=goal_hash,
        canonical_shape=goal_hash,
        target_pretty=target,
        module=skill_path.replace("/", ".").replace(".md", ""),
        goal_index=0,
        priority=1.0,
        task_kind="skill.evolution",
    )
    logger.info("Enqueued evolution task: %s", target)
    return result


def run_evolution_cycle(skill_name: str, generations: int = 10) -> float:
    """Run one full GEPA evolution cycle.

    Returns the best fitness score achieved.
    """
    from tools.infra.gepa_evolver import GEPAEvolver, _load_hermes_env
    from tools.infra.gepa_real_eval import build_eval_tasks_from_arango, RealEvaluator
    from tools.infra.vacuity_critic import VacuityCritic
    from tools.infra.proof_seeker import ProofSeeker
    import dspy

    _load_hermes_env()

    # Load skill
    skill_path = _REPO / "skills" / skill_name / "SKILL.md"
    if not skill_path.exists():
        logger.error("Skill not found: %s", skill_path)
        return 0.0

    raw = skill_path.read_text(encoding="utf-8")
    parts = raw.split("---", 2)
    frontmatter = parts[1].strip() if len(parts) >= 3 else ""
    body = parts[2].strip() if len(parts) >= 3 else raw

    # Build eval tasks from real sorry patterns in the codebase
    eval_tasks = _find_real_sorries(limit=5)

    if not eval_tasks:
        logger.warning("No real sorry tasks found")
        return 0.0

    logger.info("Evolution cycle: %s, %d gen, %d tasks", skill_name, generations, len(eval_tasks))

    # Create evaluator
    load_repo_arango_env(_REPO)
    evaluator = RealEvaluator(
        tasks=eval_tasks,
        hermes_model="deepseek-v4-flash",
        compile_check=True,
        timeout=90,
        cache=False,  # no persistent cache — always fresh evaluation
    )

    # Minimal DSPy trainset
    import dspy as _dspy
    trainset = [
        _dspy.Example(
            task_input="fill the sorry",
            expected_behavior="sorry is filled and file compiles",
        ).with_inputs("task_input")
    ]

    # Run GEPA
    evolver = GEPAEvolver(
        skill_name=skill_name,
        skill_body=body,
        trainset=trainset,
        eval_metric=lambda g, p, *a, **kw: 0.5,
        reflection_model="openai/gpt-4o-mini",
        real_evaluator=evaluator,
    )

    evolved_body, best_score = evolver.evolve(generations=generations)

    # Reassemble and save
    evolved_full = f"---\n{frontmatter}\n---\n\n{evolved_body}\n"
    EVOLVED_SKILL_DIR.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = EVOLVED_SKILL_DIR / skill_name / f"autoevolved_{ts}.md"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(evolved_full, encoding="utf-8")
    _save_evolution_record(skill_name, best_score, out_path, evolved_full)

    # ---- Run Proof Seeker on failed tasks ----
    if best_score < 1.0:
        try:
            from tools.infra.proof_seeker import ProofSeeker, ProofCandidate

            seeker = ProofSeeker()
            sought = 0

            # Re-evaluate the baseline skill to get per-task breakdown
            logger.info("Proof Seeker: re-evaluating baseline for failure analysis")
            final_result = evaluator.evaluate(body)
            failed_tasks = [tr for tr in final_result.task_results if not tr.succeeded]

            if not failed_tasks:
                # Try evaluating the evolved skill too
                final_result = evaluator.evaluate(evolved_body)
                failed_tasks = [tr for tr in final_result.task_results if not tr.succeeded]

            for tr in failed_tasks[:3]:  # limit to 3 for time
                target_name = Path(tr.task.file).stem
                context_file = tr.task.abs_path
                target_line = tr.task.line
                error_msg = tr.error

                # Read docstring context to extract mathematical meaning
                context_code = context_file.read_text(errors="replace") if context_file.exists() else ""
                docstring = _extract_docstring(context_code, target_line)

                context_code = context_file.read_text(errors="replace") if context_file.exists() else ""
                formalized = False
                attempt = 0

                # Stage 0: ChatGPT auditor (slow but highly reliable)
                attempt += 1
                logger.info("Proof Seeker: attempt %d/3 — ChatGPT audit for '%s'", attempt, target_name)
                try:
                    # Full chain: send to ChatGPT, extract formatted code, save, compile, fix
                    success = seeker.audit_via_chatgpt(context_file, target_name, target_line)
                    if success:
                        logger.info("  Attempt %d: ✓ ChatGPT audit SUCCESS", attempt)
                        formalized = True
                    else:
                        logger.info("  Attempt %d: ✗ ChatGPT audit FAILED", attempt)
                    if formalized:
                        sought += 1
                        continue
                except Exception as exc:
                    logger.debug("  ChatGPT audit skipped: %s", exc)

                # Stage 1: Pi/DeepSeek direct generation
                attempt += 1
                logger.info("Proof Seeker: attempt %d/3 — Pi direct generation for '%s'", attempt, target_name)
                candidate = seeker.digest([], target_name, context_code)
                if candidate.proof_lean:
                    logger.info("  Attempt %d: candidate proof (%.2f confidence)", attempt, candidate.confidence)
                    if target_line > 0 and context_file.exists():
                        formalized = seeker.formalize(candidate, context_file, target_line)
                        logger.info("  Attempt %d: %s", attempt, "✓ SUCCESS" if formalized else "✗ FAILED")
                if formalized:
                    sought += 1
                    continue

                # Stage 2: arXiv + re-digest
                attempt += 1
                logger.info("Proof Seeker: attempt %d/3 — searching arXiv for '%s'", attempt, target_name)
                search_query = docstring or target_name
                results = seeker.search(search_query, max_results=3)
                if results:
                    logger.info("  Found %d arXiv results, re-digesting...", len(results))
                    candidate2 = seeker.digest(results, target_name, context_code)
                    if candidate2.proof_lean:
                        logger.info("  Attempt %d: candidate proof (%.2f confidence)", attempt, candidate2.confidence)
                        if target_line > 0 and context_file.exists():
                            formalized = seeker.formalize(candidate2, context_file, target_line)
                            logger.info("  Attempt %d: %s", attempt, "✓ SUCCESS" if formalized else "✗ FAILED")
                if formalized:
                    sought += 1

            if sought:
                logger.info("Proof Seeker: searched %d failed tasks", sought)
        except ImportError:
            logger.debug("ProofSeeker not available")
        except Exception as exc:
            logger.warning("Proof Seeker error: %s", exc)

    # ---- Run Vacuity Critic on failures ----
    try:
        critic = VacuityCritic()
        cache_file = _REPO / "quarantine" / "hermes_skills" / "evolved" / ".eval_cache.jsonl"
        failures = []
        if cache_file.exists():
            for line in cache_file.read_text().strip().split("\n"):
                if not line.strip():
                    continue
                entry = json.loads(line)
                if not entry.get("succeeded", True):
                    from tools.infra.vacuity_critic import FailCase
                    failures.append(FailCase(
                        task_file=entry.get("file", ""),
                        task_line=entry.get("line", 0),
                        skill_name=skill_name,
                        skill_content_preview="",
                        hermes_output="",
                        error=entry.get("error", "unknown"),
                        original_line=f"{entry.get('file', '?')}:{entry.get('line', 0)}",
                        timestamp=ts,
                    ))

        if failures:
            logger.info("Vacuity Critic: reviewing %d failures", len(failures))
            new_patterns = critic.review_failures(failures)
            if new_patterns:
                critic.extend_skill(skill_path, new_patterns)
                logger.info("Skill extended with %d new patterns", len(new_patterns))

                # Update Codex
                codex_path = _REPO / "docs" / "codex" / "codex.md"
                if codex_path.exists():
                    with open(codex_path, "a") as f:
                        f.write(f"\n### Autonomous Discovery ({ts})\n\n")
                        for p in new_patterns:
                            f.write(f"- **{p.name}** — {p.category}, synonym of {p.synonym_of}\n")

    except Exception as exc:
        logger.warning("Post-evolution steps failed: %s", exc)

    return best_score


def _find_real_sorries(limit: int = 5) -> list[Any]:
    """Scan the Lean codebase for actual `sorry` tokens (not in comments/strings).

    Returns up to *limit* EvalTask objects pointing to real proof gaps.
    Files that have already been processed (no `sorry` left) are skipped.
    """
    from tools.infra.gepa_real_eval import EvalTask
    import re, hashlib

    results = []
    lean_dir = _REPO / "lean" / "InfoGeometry"

    for f in sorted(lean_dir.rglob("*.lean")):
        if len(results) >= limit:
            break

        text = f.read_text(errors="replace")
        if "sorry" not in text:
            continue

        lines = text.split("\n")
        in_block_comment = False

        for i, line in enumerate(lines, 1):
            if len(results) >= limit:
                break

            stripped = line.strip()

            # Track block comments /- ... -/
            if in_block_comment:
                if "-/" in stripped:
                    in_block_comment = False
                continue
            if stripped.startswith("/-"):
                in_block_comment = True
                continue

            # Strip inline comments and string literals
            code_part = line.split("--")[0]
            code_part = re.sub(r'"[^"]*"', '', code_part)

            # A real `sorry` is a standalone keyword — not in comments, strings, or option names
            if re.search(r'(?<![a-zA-Z0-9_.])\bsorry\b', code_part):
                rel = f.relative_to(_REPO)
                results.append(EvalTask(
                    file=str(rel), line=i,
                    module=str(rel).replace(".lean", "").replace("/", "."),
                    description=f"Fill `sorry` at {rel}:{i}",
                    goal_hash=hashlib.sha256(f"{rel}:{i}".encode()).hexdigest()[:24],
                ))

    return results[:limit]


def _extract_docstring(code: str, near_line: int) -> str:
    """Extract docstring/comments near a given line from Lean source code."""
    lines = code.split("\n")
    start = max(0, near_line - 10)
    # Look for /-! docstring above the target
    docstring_parts = []
    in_doc = False
    for i in range(start, min(near_line + 5, len(lines))):
        line = lines[i]
        if "/-!" in line:
            in_doc = True
            docstring_parts.append(line.split("/-!")[1].strip())
        elif "-/" in line and in_doc:
            docstring_parts.append(line.split("-/")[0].strip())
            in_doc = False
        elif in_doc:
            docstring_parts.append(line.strip())
        # Also capture inline comments above
        if not in_doc and "--" in line and i >= near_line - 5:
            docstring_parts.append(line.split("--")[1].strip())
    return " ".join(docstring_parts)


def _save_evolution_record(
    skill_name: str, score: float, skill_path: Path, content: str
) -> None:
    """Persist an evolution cycle record to ArangoDB."""
    load_repo_arango_env(_REPO)
    ep = arango_endpoint()
    db = arango_database("hive_live")
    usr = arango_username()
    pwd = arango_password("alexandria_root")

    record = {
        "skill": skill_name,
        "fitness": score,
        "path": str(skill_path.relative_to(_REPO)),
        "timestamp": datetime.now().isoformat(),
    }
    # Store as a document in the evolution collection
    aql(ep, db, usr, pwd, """
        INSERT @record IN hive_evolution_runs
    """, {"record": record})
    logger.info("Evolution record saved: %s fitness=%.4f", skill_name, score)


def poll_loop(once: bool = False) -> None:
    """Main daemon loop — polls the skill-evolution queue."""
    logger.info("Evolution worker starting (poll interval: %ds)", POLL_INTERVAL)

    while True:
        try:
            load_repo_arango_env(_REPO)
            ep = arango_endpoint()
            db = arango_database("hive_live")
            usr = arango_username()
            pwd = arango_password("alexandria_root")

            # Claim a task from the skill-evolution queue
            task = claim_next_task(
                ep, db, usr, pwd,
                worker_id=WORKER_ID,
                queue_name=EVOLUTION_QUEUE,
                lease_seconds=LEASE_SECONDS,
                task_kind="skill.evolution",
            )

            if task is None:
                logger.debug("No evolution tasks pending — polling again")
                time.sleep(POLL_INTERVAL)
                continue

            # Immediately process the task — no sleep

            # Parse the task: extract skill name from the target
            target = (task.get("runtime_goal_packet") or {}).get("formal_target", "")
            import re
            m = re.search(r"skill `([^`]+)`", target)
            skill_name = m.group(1) if m else "closure-debt-proof"

            logger.info("Processing evolution task: %s", skill_name)

            # Run the evolution cycle
            score = run_evolution_cycle(skill_name)

            # Complete or fail the task
            if score > 0:
                complete_task(
                    ep, db, usr, pwd,
                    task_key_value=task["_key"],
                    worker_id=WORKER_ID,
                )
                logger.info("Evolution task COMPLETED (score=%.4f)", score)
            else:
                fail_task(
                    ep, db, usr, pwd,
                    task_key_value=task["_key"],
                    worker_id=WORKER_ID,
                    error_message=f"Evolution failed (score=0.0)",
                )
                logger.warning("Evolution task FAILED (score=0.0)")

            if once:
                break

        except KeyboardInterrupt:
            logger.info("Evolution worker stopped by user")
            break
        except Exception as exc:
            logger.error("Evolution worker error: %s", exc)
            time.sleep(60)


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Autonomous evolution worker")
    parser.add_argument("--once", action="store_true", help="Run one cycle and exit")
    parser.add_argument("--enqueue", nargs=2, metavar=("SKILL", "GENERATIONS"),
                        help="Enqueue an evolution task: --enqueue closure-debt-proof 10")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(name)s] %(message)s",
    )

    ensure_evolution_queue()

    if args.enqueue:
        skill_name, generations = args.enqueue[0], int(args.enqueue[1])
        skill_path = f"skills/{skill_name}/SKILL.md"
        enqueue_evolution_task(skill_name, skill_path, generations=generations)
        print(f"Enqueued: {skill_name} ({generations} generations)")
        return

    poll_loop(once=args.once)


if __name__ == "__main__":
    main()
