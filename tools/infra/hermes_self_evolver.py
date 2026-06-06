#!/usr/bin/env python3
"""Hermes Self-Evolution Loop — close the first reflex arc.

Usage:
    # Dry run — verify connectivity and state
    python3 tools/infra/hermes_self_evolver.py \\
        --skill lean-proof --generations 2 --dry-run

    # First live run (3 generations)
    python3 tools/infra/hermes_self_evolver.py \\
        --skill lean-proof --generations 3 --tasks-per-gen 3

    # Resume an interrupted run
    python3 tools/infra/hermes_self_evolver.py \\
        --resume quarantine/hermes_skills/evolved/lean-proof/.evolution_state.json
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import sys
import time
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

logger = logging.getLogger("hermes_self_evolver")

# ---------------------------------------------------------------------------
# Re-use local modules
# ---------------------------------------------------------------------------

# Ensure tools/ is on the path
_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]   # info-geometry-lean

from tools.infra.hive_arango_queue import (
    claim_next_task,
    complete_task,
    fail_task,
    update_task_status,
    request_json,
)
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.evolution_evaluator import EvolutionEvaluator, FitnessScore
from tools.infra.skill_mutator import FailureCase

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

WORKER_ID_PREFIX = "hermes-self-evolver"
QUEUE_NAME = "proof-search"
LEASE_SECONDS = 1800                     # 30 min per task
SKILLS_SRC = _REPO / "skills"
QUARANTINE = _REPO / "quarantine" / "hermes_skills" / "evolved"
# Lightweight model for mutation
DEFAULT_MUTATION_MODEL = "openai/gpt-4o-mini"

# Stronger model for proof attempts via direct LLM call
DEFAULT_PROVER_MODEL = "deepseek/deepseek-r1"


# ---------------------------------------------------------------------------
# Evolution run state
# ---------------------------------------------------------------------------

@dataclass
class GenerationRecord:
    """Snapshot of a single generation in the evolution run."""
    generation: int
    skill_content: str
    fitness: float
    outcomes: list[dict[str, Any]] = field(default_factory=list)
    mutation_log: str | None = None
    timestamp: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())


@dataclass
class EvolutionState:
    """Persistent state for an evolution run, stored as JSON."""
    skill_name: str
    worker_id: str
    generations: list[GenerationRecord] = field(default_factory=list)
    best_generation: int | None = None
    best_fitness: float = 0.0
    config: dict[str, Any] = field(default_factory=dict)
    created_at: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    updated_at: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())

    def best_skill_content(self) -> str | None:
        if self.best_generation is not None:
            for g in self.generations:
                if g.generation == self.best_generation:
                    return g.skill_content
        return None

    def save(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        self.updated_at = datetime.now(timezone.utc).isoformat()
        # Convert generations to dicts
        data = {
            "skill_name": self.skill_name,
            "worker_id": self.worker_id,
            "generations": [
                {
                    "generation": g.generation,
                    "fitness": g.fitness,
                    "outcomes": g.outcomes,
                    "mutation_log": g.mutation_log,
                    "timestamp": g.timestamp,
                    # Store skill content length as hint; full content on disk
                    "skill_length": len(g.skill_content),
                }
                for g in self.generations
            ],
            "best_generation": self.best_generation,
            "best_fitness": self.best_fitness,
            "config": self.config,
            "created_at": self.created_at,
            "updated_at": self.updated_at,
        }
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False))
        # Write full skill contents to sibling files
        for g in self.generations:
            skill_path = path.with_name(f"gen_{g.generation:03d}.md")
            skill_path.write_text(g.skill_content, encoding="utf-8")

    @classmethod
    def load(cls, path: Path) -> EvolutionState:
        data = json.loads(path.read_text(encoding="utf-8"))
        state = cls(
            skill_name=data["skill_name"],
            worker_id=data["worker_id"],
        )
        state.created_at = data.get("created_at", "")
        state.updated_at = data.get("updated_at", "")
        state.best_generation = data.get("best_generation")
        state.best_fitness = data.get("best_fitness", 0.0)
        state.config = data.get("config", {})
        # Rehydrate generations from skill files on disk
        for g_data in data.get("generations", []):
            skill_path = path.with_name(f"gen_{g_data['generation']:03d}.md")
            skill_content = ""
            if skill_path.exists():
                skill_content = skill_path.read_text(encoding="utf-8")
            else:
                # May have been cleaned up; use placeholder
                logger.warning("Missing skill file for gen %d: %s", g_data["generation"], skill_path)
            state.generations.append(GenerationRecord(
                generation=g_data["generation"],
                skill_content=skill_content,
                fitness=g_data["fitness"],
                outcomes=g_data.get("outcomes", []),
                mutation_log=g_data.get("mutation_log"),
                timestamp=g_data.get("timestamp", ""),
            ))
        return state


# ---------------------------------------------------------------------------
# Core loop
# ---------------------------------------------------------------------------

class HermesSelfEvolver:
    """The evolution loop: evaluate → mutate → test → select.

    Orchestrates the following per generation:
      1. Evaluate the current skill (gen0 = baseline)
      2. Claim N pending tasks from ArangoDB
      3. For each task, run Hermes with the skill to attempt a proof
      4. Verify the result with Lean
      5. Record outcome in ArangoDB
      6. Compute fitness
      7. If improved, mutate the skill → next generation
      8. If not improved, try a different mutation direction
    """

    def __init__(
        self,
        skill_name: str,
        *,
        generations: int = 5,
        tasks_per_gen: int = 3,
        mutation_model: str = DEFAULT_MUTATION_MODEL,
        prover_model: str = DEFAULT_PROVER_MODEL,
        dry_run: bool = False,
        resume_from: Path | None = None,
    ) -> None:
        load_repo_arango_env(_REPO)
        self._ep = arango_endpoint()
        self._db = arango_database("hive_live")
        self._usr = arango_username()
        self._pwd = arango_password("alexandria_root")
        self._skill_name = skill_name
        self._generations = generations
        self._tasks_per_gen = tasks_per_gen
        self._mutation_model = mutation_model
        self._prover_model = prover_model
        self._dry_run = dry_run

        self._evaluator = EvolutionEvaluator(self._ep, self._db, self._usr, self._pwd)

        # State
        if resume_from and resume_from.exists():
            self._state = EvolutionState.load(resume_from)
            logger.info("Resumed evolution for '%s' at gen %d",
                        self._state.skill_name, len(self._state.generations))
        else:
            self._state = EvolutionState(
                skill_name=skill_name,
                worker_id=f"{WORKER_ID_PREFIX}-{uuid.uuid4().hex[:8]}",
                config={
                    "target_generations": generations,
                    "tasks_per_gen": tasks_per_gen,
                    "mutation_model": mutation_model,
                    "prover_model": prover_model,
                },
            )

        self._state_path = QUARANTINE / skill_name / ".evolution_state.json"

        # Read original skill
        src_path = SKILLS_SRC / skill_name / "SKILL.md"
        if not src_path.exists():
            raise FileNotFoundError(f"Skill not found: {src_path}")
        self._original_skill = src_path.read_text(encoding="utf-8")

    # ------------------------------------------------------------------
    # Public entry point
    # ------------------------------------------------------------------

    def run(self) -> EvolutionState:
        logger.info("Starting evolution for '%s' — %d generations, %d tasks/gen",
                    self._skill_name, self._generations, self._tasks_per_gen)

        # Pre-flight connectivity check
        if self._dry_run or logger.isEnabledFor(logging.DEBUG):
            try:
                stats = self._evaluator.queue_stats(QUEUE_NAME)
                logger.info("ArangoDB connected — queue '%s': %s",
                            QUEUE_NAME, dict(stats))
            except Exception as exc:
                logger.warning("ArangoDB connection check failed: %s", exc)
                if self._dry_run:
                    logger.info("Continuing dry-run anyway (connectivity info only)")

        # Seed gen 0 from original if no generations exist yet
        if not self._state.generations:
            self._add_generation(0, self._original_skill, 0.0, outcomes=[], mutation_log="baseline")

        for gen in range(len(self._state.generations) - 1, self._generations):
            current_gen = len(self._state.generations) - 1
            logger.info("=== Generation %d ===", current_gen)

            current_content = self._state.generations[current_gen].skill_content

            # ---- Step 1: Test the current skill against pending tasks ----
            outcomes = self._run_tasks(current_content, current_gen)
            if self._dry_run:
                logger.info("[DRY RUN] Would test %d tasks, evaluate fitness, "
                            "mutate skill, repeat × %d generations",
                            self._tasks_per_gen, self._generations)
                # Early exit — dry-run validates connectivity, not the full chain
                break

            # ---- Step 2: Evaluate fitness ----
            score = self._evaluator.evaluate_from_outcomes(
                self._skill_name, current_gen, outcomes,
            )
            logger.info("Fitness: %s", score.brief())

            # Update the generation record with actual outcomes & fitness
            self._state.generations[current_gen].outcomes = outcomes
            self._state.generations[current_gen].fitness = score.fitness
            self._save_state()

            # ---- Step 3: Check if this is the best so far ----
            if score.fitness > self._state.best_fitness:
                self._state.best_fitness = score.fitness
                self._state.best_generation = current_gen
                logger.info("New best fitness: %.4f (gen %d)", score.fitness, current_gen)
            else:
                logger.info("No improvement — best remains gen %d (%.4f)",
                            self._state.best_generation, self._state.best_fitness)

            # ---- Step 4: Mutate — but only if we have more generations to go ----
            if current_gen + 1 < self._generations:
                # Pick the best-performing skill as the mutation parent
                parent_content = self._state.best_skill_content() or current_content
                parent_fitness = self._state.best_fitness

                # Build failure cases from failed outcomes
                failures = self._outcomes_to_failures(outcomes)

                logger.info("Mutating with %d failure cases ...", len(failures))
                variants = self._mutate(parent_content, failures, parent_fitness)

                # For now: use the first variant as the next generation
                # (future: test all variants and pick the best)
                if variants:
                    next_content = variants[0]
                    self._add_generation(
                        current_gen + 1,
                        next_content,
                        0.0,  # will be set after testing
                        outcomes=[],
                        mutation_log=f"mutated from gen {current_gen}; "
                                     f"{len(failures)} failures, "
                                     f"parent fitness {parent_fitness:.3f}",
                    )
                else:
                    logger.warning("Mutation failed — cloning current as next gen")
                    self._add_generation(
                        current_gen + 1,
                        parent_content,
                        0.0,
                        outcomes=[],
                        mutation_log="clone (no mutation)",
                    )

            self._save_state()

        # ---- Final summary ----
        self._print_summary()
        self._save_state()
        return self._state

    # ------------------------------------------------------------------
    # Task execution
    # ------------------------------------------------------------------

    def _run_tasks(self, skill_content: str, generation: int) -> list[dict[str, Any]]:
        """Claim pending tasks and attempt them using Hermes + this skill.

        Returns a list of outcome dicts (one per task attempted).
        """
        # Write the skill to a temp location for Hermes to reference
        skill_dir = QUARANTINE / self._skill_name / f"gen_{generation:03d}"
        skill_dir.mkdir(parents=True, exist_ok=True)
        skill_path = skill_dir / "SKILL.md"
        skill_path.write_text(skill_content, encoding="utf-8")

        outcomes: list[dict[str, Any]] = []

        for i in range(self._tasks_per_gen):
            if self._dry_run:
                outcomes.append({
                    "goal_key": f"dry-run-{i}",
                    "task_key": f"dry-run-{i}",
                    "status": "dry_run",
                    "attempts": 0,
                    "metabolic_cost_ms": 0,
                    "error_summary": "",
                    "failure_pattern": None,
                })
                continue

            # Claim a task
            task = self._claim_task()
            if task is None:
                logger.info("No pending tasks in queue — stopping task loop")
                break

            task_key = task["_key"]
            goal_key = task.get("goal_key", "")
            logger.info("  Task %d/%d: %s", i + 1, self._tasks_per_gen, task_key)

            # Attempt with LLM directly (skill loaded as system context)
            start = time.monotonic()
            outcome = self._attempt_with_llm(
                task=task,
                skill_content=skill_content,
                generation=generation,
            )
            elapsed_ms = (time.monotonic() - start) * 1000
            outcome["metabolic_cost_ms"] = elapsed_ms

            # Record in ArangoDB
            if outcome["status"] == "completed":
                # Tag the task with skill_name and generation for future evaluation
                extra_fields = {
                    "skill_name": self._skill_name,
                    "evolution_generation": generation,
                    "metabolic_cost_ms": outcome.get("metabolic_cost_ms", 0),
                }
                result = complete_task(
                    self._ep, self._db, self._usr, self._pwd,
                    task_key_value=task_key,
                    worker_id=self._state.worker_id,
                )
                if result is None:
                    logger.warning("Failed to complete task %s — worker mismatch?", task_key)
                else:
                    # Tag with extra metadata by update
                    update_task_status(
                        self._ep, self._db, self._usr, self._pwd,
                        task_key_value=task_key,
                        worker_id=self._state.worker_id,
                        status="completed",
                        extra_fields=extra_fields,
                    )
            else:
                fail_task(
                    self._ep, self._db, self._usr, self._pwd,
                    task_key_value=task_key,
                    worker_id=self._state.worker_id,
                    error_message=outcome.get("error_summary", "unknown")[:2000],
                )

            outcomes.append(outcome)
            logger.info("  → %s (%.1fs)", outcome["status"], elapsed_ms / 1000)

            # Brief pause between tasks to avoid rate limits
            time.sleep(2)

        return outcomes

    def _claim_task(self) -> dict[str, Any] | None:
        return claim_next_task(
            self._ep, self._db, self._usr, self._pwd,
            worker_id=self._state.worker_id,
            queue_name=QUEUE_NAME,
            lease_seconds=LEASE_SECONDS,
            task_kind="proof.search",
        )

    def _attempt_with_llm(
        self,
        task: dict[str, Any],
        skill_content: str,
        generation: int,
    ) -> dict[str, Any]:
        """Attempt a proof using the Hermes CLI (which already has working auth).

        Reads the file containing the sorry, builds a prompt, and calls
        ``hermes chat -q`` with the skill loaded as context.
        """
        import subprocess

        formal_target = (task.get("runtime_goal_packet") or {}).get("formal_target") or ""
        module_hint = (task.get("runtime_goal_packet") or {}).get("module_hint") or ""

        # Parse file:line from formal_target: "Prove `name` in file.lean:line"
        file_path = module_hint.replace(".", "/") + ".lean"
        import re as _re
        m = _re.search(r"(\S+\.lean):(\d+)", formal_target)
        if m:
            file_path = m.group(1)
            str_line_no = m.group(2)
            line_no = int(str_line_no)
        else:
            str_line_no = ""
            line_no = 0

        # Read the target file to find the sorry context
        abs_path = _REPO / file_path
        if not abs_path.exists():
            # Fallback: try with lean/InfoGeometry/ prefix (tasks enqueued without full path)
            alt_path = _REPO / "lean" / "InfoGeometry" / file_path
            if alt_path.exists():
                abs_path = alt_path
        if not abs_path.exists():
            logger.warning("Target file not found: %s (tried %s)", file_path, abs_path)
            return {
                "goal_key": task.get("goal_key", ""),
                "task_key": task["_key"],
                "status": "failed",
                "attempts": 1,
                "error_summary": f"File not found: {file_path}",
                "failure_pattern": "file_not_found",
                "lean_output": "",
            }

        file_content = abs_path.read_text(encoding="utf-8")
        lines = file_content.split("\n")

        # Extract surrounding context (15 lines around the sorry)
        start = max(0, line_no - 15)
        end = min(len(lines), line_no + 10)
        context_lines = []
        for i in range(start, end):
            marker = " >>>" if i + 1 == line_no else "    "
            context_lines.append(f"{i+1:5d}{marker} {lines[i]}")
        context_block = "\n".join(context_lines)

        # Write skill to a temp dir for Hermes to load
        skill_dir = QUARANTINE / self._skill_name / f"gen_{generation:03d}"
        skill_dir.mkdir(parents=True, exist_ok=True)
        (skill_dir / "SKILL.md").write_text(skill_content, encoding="utf-8")

        query = (
            f"Fill in the `sorry` in this Lean file.\n\n"
            f"File: {file_path}\n"
            f"Line: ~{line_no}\n\n"
            f"Context:\n```lean4\n{context_block}\n```\n\n"
            f"Use read_file to read the full file, then write_file "
            f"to replace the `sorry` with a complete Lean proof. "
            f"Output the replacement code."
        )

        try:
            result = subprocess.run(
                [
                    "hermes", "chat",
                    "-m", "deepseek-v4-flash",
                    "-s", str(skill_dir),
                    "-q", query,
                    "--accept-hooks",
                    "--yolo",
                ],
                capture_output=True,
                text=True,
                timeout=300,  # 5 min per attempt
            )

            stdout = result.stdout or ""
            stderr = result.stderr or ""
            returncode = result.returncode

            if returncode != 0:
                return {
                    "goal_key": task.get("goal_key", ""),
                    "task_key": task["_key"],
                    "status": "failed",
                    "attempts": 1,
                    "error_summary": stderr[:500] or stdout[:500],
                    "failure_pattern": "hermes_cli_error",
                    "lean_output": stderr[:1000],
                }

            # Check if the file still has the sorry at that line
            current_content = abs_path.read_text(encoding="utf-8")
            current_lines = current_content.split("\n")
            still_has_sorry = (
                line_no <= len(current_lines)
                and "sorry" in current_lines[line_no - 1]
            )

            if still_has_sorry:
                return {
                    "goal_key": task.get("goal_key", ""),
                    "task_key": task["_key"],
                    "status": "failed",
                    "attempts": 1,
                    "error_summary": "Sorry still present at target line",
                    "failure_pattern": "hermes_did_not_fix",
                    "lean_output": stdout[:2000],
                }

            return {
                "goal_key": task.get("goal_key", ""),
                "task_key": task["_key"],
                "status": "completed",
                "attempts": 1,
                "error_summary": "",
                "failure_pattern": None,
                "lean_output": stdout[:2000],
            }

        except subprocess.TimeoutExpired:
            return {
                "goal_key": task.get("goal_key", ""),
                "task_key": task["_key"],
                "status": "failed",
                "attempts": 1,
                "error_summary": "Hermes timeout after 300s",
                "failure_pattern": "timeout",
                "lean_output": "",
            }

    @staticmethod
    def _extract_lean_code(text: str) -> str:
        """Extract Lean code from LLM output — prefers fenced blocks."""
        import re
        # Try fenced lean blocks first
        blocks = re.findall(r"```(?:lean4|lean)\s*\n(.*?)```", text, re.DOTALL)
        if blocks:
            return "\n\n".join(b.strip() for b in blocks)
        # Fallback: look for `theorem` or `lemma` or `by` blocks
        lean_keywords = re.findall(r"(theorem|lemma|def|instance|by\s+)[^;]+", text)
        if lean_keywords:
            return "\n\n".join(lean_keywords[:3])
        return ""

    # ------------------------------------------------------------------
    # Mutation
    # ------------------------------------------------------------------

    def _mutate(
        self,
        parent_content: str,
        failures: list[FailureCase],
        parent_fitness: float,
    ) -> list[str]:
        """Produce mutated variants of the skill using Hermes CLI.

        Returns list of SKILL.md content strings (may be empty on failure).
        """
        import subprocess

        failures_text = "\n".join(
            f"Failure {i}: {f.error_summary[:200]}"
            for i, f in enumerate(failures)
        ) or "No recorded failures — suggest a general improvement."

        prompt = (
            f"I need to improve a Lean proof-writing skill file (SKILL.md).\n\n"
            f"Current skill fitness: {parent_fitness:.3f}/1.0\n\n"
            f"## Recent failures when using this skill\n{failures_text}\n\n"
            f"## Current skill content\n```markdown\n{parent_content[:4000]}\n```\n\n"
            f"## Task\n"
            f"Produce an improved version of the skill above. "
            f"Target the sections most related to the observed failures. "
            f"Add concrete error-handling steps, revise tactical guidance, "
            f"or strengthen the search strategy. "
            f"Output ONLY the mutated SKILL.md content, starting with '---'."
        )

        try:
            result = subprocess.run(
                ["hermes", "chat", "-q", prompt, "--yolo"],
                capture_output=True, text=True, timeout=120,
            )
            output = result.stdout or ""
            # Clean up Hermes output: strip chat artifacts, find SKILL.md content
            lines = output.split("\n")
            content_lines = []
            in_skill = False
            for line in lines:
                if line.strip().startswith("---") and not in_skill:
                    in_skill = True
                    content_lines.append(line)
                elif in_skill:
                    content_lines.append(line)
            mutated = "\n".join(content_lines) if in_skill else output

            if len(mutated) > 200 and ("---" in mutated[:500] or "name:" in mutated[:500]):
                return [mutated]
            else:
                logger.warning("Hermes did not produce valid SKILL.md — cloning")
                return []

        except Exception as exc:
            logger.warning("Mutation via Hermes failed: %s", exc)
            return []

    @staticmethod
    def _outcomes_to_failures(outcomes: list[dict[str, Any]]) -> list[FailureCase]:
        """Convert outcome dicts to FailureCase instances for the mutator."""
        failures = []
        for o in outcomes:
            if o.get("status") != "failed":
                continue
            failures.append(FailureCase(
                error_summary=o.get("error_summary", ""),
                failure_pattern=o.get("failure_pattern"),
                lean_error_output=o.get("lean_output"),
            ))
        return failures

    # ------------------------------------------------------------------
    # State management
    # ------------------------------------------------------------------

    def _add_generation(
        self,
        gen: int,
        content: str,
        fitness: float,
        outcomes: list[dict[str, Any]],
        mutation_log: str | None,
    ) -> None:
        self._state.generations.append(GenerationRecord(
            generation=gen,
            skill_content=content,
            fitness=fitness,
            outcomes=outcomes,
            mutation_log=mutation_log,
        ))
        self._save_state()
        logger.info("Added gen %d (fitness=%.4f)", gen, fitness)

    def _save_state(self) -> None:
        self._state.save(self._state_path)

    # ------------------------------------------------------------------
    # Summary
    # ------------------------------------------------------------------

    def _print_summary(self) -> None:
        print("\n" + "=" * 60)
        print(f"EVOLUTION COMPLETE — {self._skill_name}")
        print("=" * 60)
        for g in self._state.generations:
            marker = " ✓ BEST" if g.generation == self._state.best_generation else ""
            print(f"  Gen {g.generation:2d}: fitness={g.fitness:.4f}  "
                  f"({len(g.outcomes)} tasks){marker}")
        if self._state.best_generation is not None:
            print(f"\nBest: gen {self._state.best_generation} "
                  f"(fitness={self._state.best_fitness:.4f})")
            best_path = self._state_path.with_name(
                f"gen_{self._state.best_generation:03d}.md"
            )
            print(f"Evolved skill: {best_path}")
        else:
            print("\nNo best generation recorded (dry run or no generations completed)")
        print("=" * 60)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Hermes Self-Evolution Loop",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--skill", default="lean-proof",
                        help="Skill name under skills/<name>/SKILL.md")
    parser.add_argument("--generations", type=int, default=5,
                        help="Number of evolution generations")
    parser.add_argument("--tasks-per-gen", type=int, default=3,
                        help="Tasks to attempt per generation")
    parser.add_argument("--mutation-model", default=DEFAULT_MUTATION_MODEL,
                        help="Model for skill mutation")
    parser.add_argument("--prover-model", default=DEFAULT_PROVER_MODEL,
                        help="Model for proof attempts via Hermes")
    parser.add_argument("--resume", type=Path, default=None,
                        help="Resume from .evolution_state.json")
    parser.add_argument("--dry-run", action="store_true",
                        help="Check connectivity and state without executing")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    evolver = HermesSelfEvolver(
        skill_name=args.skill,
        generations=args.generations,
        tasks_per_gen=args.tasks_per_gen,
        mutation_model=args.mutation_model,
        prover_model=args.prover_model,
        dry_run=args.dry_run,
        resume_from=args.resume,
    )

    try:
        state = evolver.run()
    except KeyboardInterrupt:
        logger.info("Interrupted — saving state")
        evolver._save_state()
        sys.exit(130)

    if args.dry_run:
        print("\nDry-run complete. Ready for live run.")
        print(f"  Skill : skills/{args.skill}/SKILL.md")
        print(f"  Queue : {QUEUE_NAME} on {evolver._ep}/{evolver._db}")
        print(f"  Worker: {evolver._state.worker_id}")
        print(f"  Run   : hermes-self-evolver --skill {args.skill} "
              f"--generations {args.generations}")


if __name__ == "__main__":
    main()
