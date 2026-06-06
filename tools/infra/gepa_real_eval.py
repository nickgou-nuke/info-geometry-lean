#!/usr/bin/env python3
"""Real evaluation harness for GEPA-evolved skills.

Measures fitness by actually running Hermes against real sorry tasks,
checking if the sorry was filled, and verifying the file still compiles.

Usage:
    python3 tools/infra/gepa_real_eval.py \\
        --skill quarantine/hermes_skills/evolved/lean-proof/gepa_evolved_*.md \\
        --tasks-file tasks.jsonl
"""

from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any, Iterator, Optional

from tools.infra.thermodynamic_scoring import DEFAULT_HEURISTIC_WEIGHT, score_outcomes
from tools.quality.semantic_vacuity_gate import DEFAULT_PATTERNS as VACUITY_PATTERNS
from tools.quality.semantic_vacuity_gate import audit_text as audit_vacuity_text
from tools.quality.semantic_vacuity_gate import load_patterns as load_vacuity_patterns

logger = logging.getLogger("gepa_real_eval")

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]

CACHE_FILE = _REPO / "quarantine" / "hermes_skills" / "evolved" / ".eval_cache.jsonl"


# ---------------------------------------------------------------------------
# Task model
# ---------------------------------------------------------------------------

def _normalize_lean_file_path(file_path: str) -> str:
    """Normalize Lean task paths to repository-relative paths when possible."""
    raw = str(file_path).strip()
    if not raw:
        return raw

    path = Path(raw)
    if path.is_absolute():
        try:
            return str(path.resolve().relative_to(_REPO))
        except ValueError:
            return str(path)

    normalized = raw.replace("\\", "/")
    if normalized.startswith("lean/InfoGeometry/"):
        return normalized
    if normalized.startswith("InfoGeometry/"):
        return f"lean/{normalized}"
    # Queue tasks may lack the lean/InfoGeometry/ prefix
    candidate = f"lean/InfoGeometry/{normalized}"
    if (_REPO / candidate).exists():
        return candidate
    return normalized

@dataclass
class EvalTask:
    """A single sorry-filling task for evaluation."""
    file: str                    # relative to repo root, e.g. "lean/InfoGeometry/..."
    line: int                    # line number of the sorry
    module: str                  # Lean module path
    description: str = ""       # human-readable
    goal_hash: str = ""

    def __post_init__(self) -> None:
        self.file = _normalize_lean_file_path(self.file)

    @property
    def abs_path(self) -> Path:
        return _REPO / self.file

    def to_dict(self) -> dict:
        return {
            "file": self.file, "line": self.line,
            "module": self.module, "description": self.description,
            "goal_hash": self.goal_hash,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "EvalTask":
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


# ---------------------------------------------------------------------------
# Real evaluator
# ---------------------------------------------------------------------------

@dataclass
class EvalResult:
    """Result of evaluating a skill against a set of tasks."""
    skill_hash: str
    task_results: list["TaskResult"] = field(default_factory=list)
    average_fitness: float = 0.0
    policy_fitness: float = 0.0
    selection_fitness: float = 0.0
    thermodynamic_fitness: float = 0.0
    temperature: float = 1.0
    partition_function: float = 0.0
    free_energy: float = 0.0
    elapsed_seconds: float = 0.0

    @property
    def n_succeeded(self) -> int:
        return sum(1 for r in self.task_results if r.succeeded)


@dataclass
class TaskResult:
    """Result for a single task."""
    task: EvalTask
    succeeded: bool = False
    sorry_removed: bool = False
    compiled: bool = False
    policy_clean: bool = True
    policy_score: float = 1.0
    hermes_output: str = ""
    error: str = ""
    elapsed_ms: float = 0.0


@dataclass
class HermesRun:
    """Output from one Hermes invocation."""
    output: str = ""
    error: str = ""
    returncode: int = 0


class RealEvaluator:
    """Evaluates a skill by running Hermes on real sorry tasks.

    The evaluation flow per task:
        1. Backup the original file
        2. Invoke Hermes with the skill prompt to fill the sorry
        3. Check if the sorry was removed from the target line
        4. Optionally compile with ``lake env lean``
        5. Restore the backup
        6. Cache the result

    Parameters
    ----------
    tasks : list[EvalTask]
        The validation set of sorry tasks.
    hermes_model : str
        Model name passed to ``hermes chat -m``.
    compile_check : bool
        Whether to run ``lake env lean`` after filling (default True).
    timeout : int
        Max seconds per task (default 60).
    cache : bool
        Whether to read/write a JSONL cache (default True).
    isolated : bool
        Whether Hermes edits a temporary copy instead of the repository file
        (default True).
    """

    def __init__(
        self,
        tasks: list[EvalTask],
        *,
        hermes_model: str = "deepseek-v4-flash",
        compile_check: bool = True,
        timeout: int = 60,
        cache: bool = True,
        isolated: bool = True,
        heuristic_weight: float = DEFAULT_HEURISTIC_WEIGHT,
    ) -> None:
        self.tasks = tasks
        self.hermes_model = hermes_model
        self.compile_check = compile_check
        self.timeout = timeout
        self.cache = cache
        self.isolated = isolated
        self.heuristic_weight = heuristic_weight
        self._cache: dict[str, dict[str, Any]] = {}
        try:
            self._vacuity_categories = load_vacuity_patterns(VACUITY_PATTERNS)["categories"]
        except Exception:
            self._vacuity_categories = {}

        if cache:
            self._load_cache()

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def evaluate(self, skill_content: str) -> EvalResult:
        """Evaluate *skill_content* against all tasks.

        Returns an EvalResult with per-task breakdown and average fitness.
        """
        skill_hash = self._hash(skill_content)
        logger.info("Evaluating skill %s against %d tasks", skill_hash[:12], len(self.tasks))

        start = time.monotonic()
        task_results: list[TaskResult] = []

        for task in self.tasks:
            task_start = time.monotonic()
            tr = self._evaluate_one(skill_content, skill_hash, task)
            tr.elapsed_ms = (time.monotonic() - task_start) * 1000
            task_results.append(tr)

            icon = "✓" if tr.succeeded else "✗"
            logger.info("  %s %s:%d (%dms)", icon, task.file, task.line, tr.elapsed_ms)

        elapsed = time.monotonic() - start
        avg_fitness = sum(r.succeeded for r in task_results) / max(1, len(task_results))
        policy_fitness = sum(r.policy_score for r in task_results) / max(1, len(task_results))
        thermo = score_outcomes(
            [
                {
                    "status": "completed" if r.succeeded else "failed",
                    "succeeded": r.succeeded,
                    "attempts": 1,
                    "metabolic_cost_ms": r.elapsed_ms,
                }
                for r in task_results
            ]
            ,
            heuristic_weight=self.heuristic_weight,
        )
        selection_fitness = max(0.0, min(1.0, 0.85 * thermo.fitness + 0.15 * policy_fitness))

        return EvalResult(
            skill_hash=skill_hash,
            task_results=task_results,
            average_fitness=avg_fitness,
            policy_fitness=policy_fitness,
            selection_fitness=selection_fitness,
            thermodynamic_fitness=selection_fitness,
            temperature=thermo.temperature,
            partition_function=thermo.partition_function,
            free_energy=thermo.free_energy,
            elapsed_seconds=elapsed,
        )

    # ------------------------------------------------------------------
    # Single task evaluation
    # ------------------------------------------------------------------

    def _evaluate_one(
        self, skill_content: str, skill_hash: str, task: EvalTask,
    ) -> TaskResult:
        """Evaluate a single skill against a single task."""

        # --- Validate file exists ---
        abs_path = task.abs_path
        if not abs_path.exists():
            logger.warning("Task file not found: %s", abs_path)
            return TaskResult(
                task=task, succeeded=False,
                error=f"File not found: {task.file}",
            )

        # --- Backup ---
        original = abs_path.read_text(encoding="utf-8")
        original_lines = original.split("\n")

        line_no, line_error = self._resolve_sorry_line(task, original_lines)
        is_closure_debt = line_error == "closure_debt_no_sorry"
        if line_error and not is_closure_debt:
            return TaskResult(
                task=task, succeeded=False,
                error=line_error,
            )
        if line_no != task.line and not is_closure_debt:
            task = replace(task, line=line_no)

        file_hash = self._hash(original)[:16]
        cache_key = f"{skill_hash}:{task.file}:{task.line}:{task.goal_hash}:{file_hash}"
        if self.cache and cache_key in self._cache:
            cached = self._cache[cache_key]
            if cached:
                return TaskResult(
                    task=task,
                    succeeded=bool(cached.get("succeeded", False)),
                    sorry_removed=bool(cached.get("sorry_removed", False)),
                    compiled=bool(cached.get("compiled", False)),
                    policy_clean=bool(cached.get("policy_clean", True)),
                    policy_score=float(cached.get("policy_score", 1.0)),
                    hermes_output="(cached)",
                    error=str(cached.get("error", "")),
                )

        with self._evaluation_file(abs_path, original) as eval_path:
            hermes = self._run_hermes(skill_content, task, eval_path, original_lines)
            if hermes.error:
                return self._result(task, False, hermes.error, hermes_output=hermes.output[:1000])

            # --- Check outcome ---
            # For closure-debt tasks (no sorry, just _True pattern), check if _True field was removed
            is_closure_debt = line_error == "closure_debt_no_sorry" and task.line >= 1

            current = eval_path.read_text(encoding="utf-8")
            current_lines = current.split("\n")
            if hasattr(self, '_audit_policy_window'):
                policy_clean, policy_score, policy_error = self._audit_policy_window(current_lines, task)
            else:
                # GEPA compatibility: if the attribute is missing (DSPy teleprompt wrapping),
                # skip the audit window check entirely.
                policy_clean, policy_score, policy_error = True, 1.0, ""

            if is_closure_debt:
                # Check if the _True : Prop := pattern was removed from the file
                original_line = original_lines[task.line - 1] if task.line <= len(original_lines) else ""
                # Extract the field name (e.g., "generic_True" from "generic_True : Prop := True")
                import re as _re
                field_match = _re.match(r"\s*([a-zA-Z_]+_True)\s*:", original_line)
                field_name = field_match.group(1) if field_match else ""
                _True_removed = field_name and field_name not in current
                sorry_removed = True  # not applicable
            else:
                # Standard sorry-filling check
                if line_error:
                    return self._result(task, False, line_error, hermes_output=hermes.output[:1000])
                if line_no != task.line:
                    task = replace(task, line=line_no)
                still_has_sorry = (
                    1 <= task.line <= len(current_lines)
                    and "sorry" in current_lines[task.line - 1]
                )
                sorry_removed = not still_has_sorry
                _True_removed = True  # not applicable

            # --- Compilation check ---
            compiled = False
            if self.compile_check and sorry_removed and policy_clean:
                compiled = self._check_compiles(eval_path, task)

            succeeded = sorry_removed and policy_clean and (not self.compile_check or compiled)

            tr = TaskResult(
                task=task, succeeded=succeeded,
                sorry_removed=sorry_removed, compiled=compiled,
                policy_clean=policy_clean, policy_score=policy_score,
                hermes_output=hermes.output[:1000],
                error="" if succeeded else (
                    "sorry still present" if not sorry_removed
                    else policy_error if not policy_clean
                    else "compilation failed" if self.compile_check and not compiled
                    else ""
                ),
            )

            # --- Cache ---
            if self.cache:
                self._cache[cache_key] = {
                    "succeeded": succeeded,
                    "sorry_removed": sorry_removed,
                    "compiled": compiled,
                    "policy_clean": policy_clean,
                    "policy_score": policy_score,
                    "error": tr.error,
                }
                self._dump_cache(
                    skill_hash,
                    task,
                    succeeded,
                    tr.error,
                    file_hash=file_hash,
                    sorry_removed=sorry_removed,
                    compiled=compiled,
                    policy_clean=policy_clean,
                    policy_score=policy_score,
                )

            return tr

    def _audit_policy_window(self, lines: list[str], task: EvalTask) -> tuple[bool, float, str]:
        """Audit the repaired theorem window for semantic vacuity patterns."""
        if not lines:
            return True, 1.0, ""

        if task.line > 0:
            start = max(0, task.line - 15)
            stop = min(len(lines), task.line + 20)
        else:
            start = 0
            stop = min(len(lines), 40)

        window = "\n".join(lines[start:stop])
        findings = audit_vacuity_text(str(task.abs_path), window, self._vacuity_categories)
        error_findings = [f for f in findings if f.severity == "error"]
        warning_findings = [f for f in findings if f.severity == "warning"]

        if error_findings:
            detail = "; ".join(f"{f.category}:{f.subject}" for f in error_findings[:3])
            return False, 0.0, f"semantic vacuity findings: {detail}"

        penalty = min(0.8, 0.15 * len(warning_findings))
        return True, max(0.0, 1.0 - penalty), ""

    @staticmethod
    def _result(task: EvalTask, succeeded: bool, error: str,
                hermes_output: str = "") -> TaskResult:
        return TaskResult(
            task=task, succeeded=succeeded,
            sorry_removed=False, compiled=False,
            hermes_output=hermes_output, error=error,
        )

    @contextmanager
    def _evaluation_file(self, abs_path: Path, original: str) -> Iterator[Path]:
        """Yield the file Hermes should edit for this task.

        Isolated evaluation keeps the repository worktree clean by letting
        Hermes mutate a temporary Lean file. The legacy in-place mode remains
        available for operators who explicitly want to inspect the patch.
        """
        if self.isolated:
            with tempfile.TemporaryDirectory(prefix="gepa-real-eval-") as tmp_dir:
                tmp_path = Path(tmp_dir) / abs_path.name
                tmp_path.write_text(original, encoding="utf-8")
                yield tmp_path
            return

        try:
            yield abs_path
        finally:
            abs_path.write_text(original, encoding="utf-8")

    def _run_hermes(
        self,
        skill_content: str,
        task: EvalTask,
        eval_path: Path,
        original_lines: list[str],
    ) -> HermesRun:
        """Invoke Hermes with the evolved skill against ``eval_path``."""
        context_start = max(0, task.line - 10)
        context_end = min(len(original_lines), task.line + 5)
        context_lines = []
        for i in range(context_start, context_end):
            marker = " >>>" if i + 1 == task.line else "    "
            context_lines.append(f"{i+1:5d}{marker} {original_lines[i]}")
        context_block = "\n".join(context_lines)

        query = (
            f"Fill in the `sorry` at line {task.line} in this temporary Lean file:\n"
            f"`{eval_path}`\n\n"
            f"The original repository path is `{task.file}` and the module hint is "
            f"`{task.module}`. Do not edit the original file during evaluation.\n\n"
            f"Context:\n```lean4\n{context_block}\n```\n\n"
            f"Read the temporary file, replace only the target `sorry` with a complete "
            f"Lean proof, and write the modified temporary file back. Do not introduce "
            f"`sorry`, `admit`, or new axioms. The fitness gate will compile the "
            f"temporary file with `lake env lean` from the repository root.\n\n"
            f"Skill: this is the methodology you should follow for this task:\n"
            f"{skill_content[:3000]}"
        )

        try:
            result = subprocess.run(
                ["hermes", "chat", "-m", self.hermes_model, "-q", query,
                 "--accept-hooks", "--yolo"],
                capture_output=True, text=True, timeout=self.timeout,
                cwd=str(_REPO),
        )
        except subprocess.TimeoutExpired:
            return HermesRun(error=f"Hermes timeout after {self.timeout}s")
        except FileNotFoundError:
            return HermesRun(error="Hermes CLI not found on PATH")
        except Exception as exc:
            return HermesRun(error=f"Hermes invocation error: {exc}")

        output = (result.stdout or "") + (result.stderr or "")
        if result.returncode != 0:
            return HermesRun(
                output=output,
                error=f"Hermes exited with status {result.returncode}",
                returncode=result.returncode,
            )
        return HermesRun(output=output, returncode=result.returncode)

    # ------------------------------------------------------------------
    # Compilation check
    # ------------------------------------------------------------------

    @staticmethod
    def _resolve_sorry_line(task: EvalTask, lines: list[str]) -> tuple[int, str]:
        """Return the concrete sorry line for *task*, or an error string."""
        if task.line > len(lines):
            return 0, f"Line {task.line} exceeds file length ({len(lines)})"

        if task.line >= 1:
            target = lines[task.line - 1]
            if "sorry" in target:
                return task.line, ""
            # If target line has 'by' but no sorry, try the next line
            if "by" in target and task.line < len(lines):
                if "sorry" in lines[task.line]:
                    return task.line + 1, ""
            # Check for _True : Prop := True pattern (no sorry at all)
            if "_True" in target and "True" in target and "Prop" in target:
                return task.line, "closure_debt_no_sorry"
            return 0, f"No sorry at {task.file}:{task.line}"

        sorry_lines = [idx + 1 for idx, line in enumerate(lines) if "sorry" in line]
        if not sorry_lines:
            return 0, f"No sorry found in {task.file}"
        if len(sorry_lines) > 1:
            return 0, (
                f"Ambiguous sorry task in {task.file}: explicit line required "
                f"({len(sorry_lines)} candidates)"
            )
        return sorry_lines[0], ""

    def _check_compiles(self, file_path: Path, task: EvalTask) -> bool:
        """Run ``lake env lean`` and check exit code."""
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(file_path)],
                capture_output=True, text=True, timeout=60,
                cwd=str(_REPO),
            )
            return result.returncode == 0
        except subprocess.TimeoutExpired:
            logger.debug("Compilation timeout on %s", task.file)
            return False
        except Exception as exc:
            logger.debug("Compilation error on %s: %s", task.file, exc)
            return False

    # ------------------------------------------------------------------
    # Caching
    # ------------------------------------------------------------------

    @staticmethod
    def _hash(content: str) -> str:
        return hashlib.sha256(content.encode()).hexdigest()

    def _load_cache(self) -> None:
        if not CACHE_FILE.exists():
            return
        try:
            for line in CACHE_FILE.read_text().strip().split("\n"):
                if not line.strip():
                    continue
                entry = json.loads(line)
                goal_hash = entry.get("goal_hash", "")
                file_hash = entry.get("file_hash", "")
                key = f"{entry['skill_hash']}:{entry['file']}:{entry['line']}:{goal_hash}:{file_hash}"
                self._cache[key] = entry
            logger.debug("Loaded %d cached eval results", len(self._cache))
        except Exception as exc:
            logger.warning("Failed to load eval cache: %s", exc)

    def _dump_cache(self, skill_hash: str, task: EvalTask,
                    succeeded: bool, error: str, *, file_hash: str,
                    sorry_removed: bool, compiled: bool,
                    policy_clean: bool, policy_score: float) -> None:
        entry = {
            "skill_hash": skill_hash,
            "file": task.file, "line": task.line,
            "goal_hash": task.goal_hash,
            "file_hash": file_hash,
            "succeeded": succeeded, "error": error,
            "sorry_removed": sorry_removed,
            "compiled": compiled,
            "policy_clean": policy_clean,
            "policy_score": policy_score,
            "timestamp": time.time(),
        }
        try:
            CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
            with open(CACHE_FILE, "a") as f:
                f.write(json.dumps(entry) + "\n")
        except Exception as exc:
            logger.debug("Failed to write eval cache: %s", exc)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_eval_tasks_from_arango(limit: int = 5) -> list[EvalTask]:
    """Load tasks from the ArangoDB queue and convert to EvalTask list."""
    from tools.infra.arango_env import (
        arango_database, arango_endpoint, arango_password,
        arango_username, load_repo_arango_env,
    )
    from tools.infra.hive_arango_queue import aql

    load_repo_arango_env(_REPO)
    ep = arango_endpoint()
    db = arango_database("hive_live")
    usr = arango_username()
    pwd = arango_password("alexandria_root")

    rows = aql(ep, db, usr, pwd, f"""
        FOR t IN hive_tasks
          FILTER t.queue_name == "proof-search"
          FILTER t.status == "pending"
          SORT RAND()
          LIMIT {limit}
          RETURN {{
            formal_target: t.runtime_goal_packet.formal_target,
            module_hint: t.runtime_goal_packet.module_hint,
            goal_key: t.goal_key,
            task_key: t._key
          }}
    """)

    tasks = []
    for r in rows:
        formal = r.get("formal_target", "") or ""
        module_hint = (r.get("module_hint", "") or "").replace(".", "/") + ".lean"
        m = re.search(r"(\S+\.lean):(\d+)", formal)
        if m:
            file_path = m.group(1)
            line_no = int(m.group(2))
        else:
            file_path = module_hint
            line_no = 0
        tasks.append(EvalTask(
            file=file_path, line=line_no,
            module=module_hint, description=formal,
            goal_hash=r.get("task_key", ""),
        ))
    return tasks


def build_eval_tasks_from_file(path: Path) -> list[EvalTask]:
    """Load tasks from a JSONL file."""
    tasks = []
    for line in path.read_text().strip().split("\n"):
        if not line.strip():
            continue
        tasks.append(EvalTask.from_dict(json.loads(line)))
    return tasks


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Real evaluation for GEPA skills")
    parser.add_argument("--skill", help="Path to evolved SKILL.md")
    parser.add_argument("--tasks-file", type=Path, help="JSONL with tasks")
    parser.add_argument("--tasks-limit", type=int, default=3,
                        help="Max tasks from ArangoDB queue")
    parser.add_argument("--model", default="deepseek-v4-flash")
    parser.add_argument("--no-compile", action="store_true",
                        help="Skip compilation check")
    parser.add_argument("--heuristic-weight", type=float, default=DEFAULT_HEURISTIC_WEIGHT,
                        help="Blend weight for the legacy heuristic term [0,1]")
    parser.add_argument("--dump-cache", action="store_true",
                        help="Print cache contents and exit")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s [%(name)s] %(message)s",
    )

    if args.dump_cache:
        if CACHE_FILE.exists():
            for line in CACHE_FILE.read_text().strip().split("\n"):
                if line.strip():
                    print(json.dumps(json.loads(line), indent=2))
                    print("---")
        else:
            print("No cache file found")
        return

    # Load tasks
    if args.tasks_file:
        tasks = build_eval_tasks_from_file(args.tasks_file)
        logger.info("Loaded %d tasks from %s", len(tasks), args.tasks_file)
    else:
        tasks = build_eval_tasks_from_arango(limit=args.tasks_limit)
        logger.info("Loaded %d tasks from ArangoDB", len(tasks))

    if not tasks:
        logger.warning("No tasks available for evaluation")
        print(json.dumps({"average_fitness": 0.0, "task_results": []}))
        return

    # Load skill
    if args.skill:
        skill_path = _REPO / args.skill if not Path(args.skill).is_absolute() else Path(args.skill)
        if not skill_path.exists():
            logger.error("Skill not found: %s", skill_path)
            sys.exit(1)
        skill_content = skill_path.read_text(encoding="utf-8")
    else:
        # Use the baseline lean-proof skill
        skill_content = (_REPO / "skills" / "lean-proof" / "SKILL.md").read_text(encoding="utf-8")
        logger.info("No skill specified — using baseline lean-proof skill")

    # Evaluate
    evaluator = RealEvaluator(
        tasks=tasks, hermes_model=args.model,
        compile_check=not args.no_compile,
        heuristic_weight=args.heuristic_weight,
    )
    result = evaluator.evaluate(skill_content)

    # Report
    print(json.dumps({
        "skill_hash": result.skill_hash[:16],
        "average_fitness": result.average_fitness,
        "selection_fitness": result.selection_fitness,
        "thermodynamic_fitness": result.thermodynamic_fitness,
        "temperature": round(result.temperature, 4),
        "partition_function": round(result.partition_function, 6),
        "free_energy": round(result.free_energy, 6),
        "n_succeeded": result.n_succeeded,
        "n_tasks": len(result.task_results),
        "elapsed_seconds": round(result.elapsed_seconds, 1),
        "task_results": [
            {
                "file": tr.task.file, "line": tr.task.line,
                "succeeded": tr.succeeded,
                "sorry_removed": tr.sorry_removed,
                "compiled": tr.compiled,
                "error": tr.error,
                "elapsed_ms": round(tr.elapsed_ms, 1),
            }
            for tr in result.task_results
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
