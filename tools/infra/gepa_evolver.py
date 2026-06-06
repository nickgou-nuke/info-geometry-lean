#!/usr/bin/env python3
"""GEPA + DSPy integration for skill self-evolution.

Wraps our ArangoDB-based evaluation pipeline as a DSPy-compatible
metric function and uses dspy.GEPA to evolve skill files via
Pareto-optimized genetic search.

Usage:
    python3 tools/infra/gepa_evolver.py --skill lean-proof --generations 5
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

import dspy

# Ensure tools/ is on the path
_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

logger = logging.getLogger("gepa_evolver")


def save_rollback_archive(
    *,
    skill_name: str,
    skill_content: str,
    fitness: float,
    generation: int,
) -> Path:
    """Persist an evolved skill variant for rollback/lineage review."""
    archive_dir = _REPO / "quarantine" / "hermes_skills" / "archive" / skill_name
    archive_dir.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256(skill_content.encode("utf-8")).hexdigest()[:12]
    path = archive_dir / f"gen_{generation:04d}_fitness_{fitness:.4f}_{digest}.md"
    path.write_text(skill_content, encoding="utf-8")
    manifest_entry = {
        "skill": skill_name,
        "generation": generation,
        "fitness": fitness,
        "hash": digest,
        "path": str(path.relative_to(_REPO)),
        "timestamp": datetime.now().isoformat(timespec="seconds"),
    }
    manifest = archive_dir / "manifest.jsonl"
    with manifest.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(manifest_entry, sort_keys=True) + "\n")
    return path


def load_best_skill(skill_name: str, *, fallback: str = "") -> str:
    """Load the highest-fitness archived skill variant, or *fallback*."""
    archive_dir = _REPO / "quarantine" / "hermes_skills" / "archive" / skill_name
    manifest = archive_dir / "manifest.jsonl"
    if not manifest.exists():
        return fallback

    best: dict[str, Any] | None = None
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            entry = json.loads(line)
        except json.JSONDecodeError:
            continue
        if best is None or float(entry.get("fitness", -1.0)) > float(best.get("fitness", -1.0)):
            best = entry
    if not best:
        return fallback

    path = _REPO / str(best.get("path", ""))
    if not path.exists():
        return fallback
    return path.read_text(encoding="utf-8")


def _load_hermes_env() -> None:
    """Load ~/.hermes/.env if it exists (Hermes keeps real keys there)."""
    env_path = Path.home() / ".hermes" / ".env"
    if not env_path.exists():
        return
    try:
        import dotenv
        dotenv.load_dotenv(env_path)
    except ImportError:
        # Fallback: manually parse the env file
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, _, val = line.partition("=")
            key = key.strip()
            val = val.strip().strip("'\"")
            if key and val and not os.environ.get(key):
                os.environ[key] = val


class GEPAEvolver:
    """Wraps dspy.GEPA to evolve a skill file using our evaluation pipeline.

    The GEPA optimizer treats the skill body text as an optimizable parameter,
    proposes mutations via its reflection-based genetic algorithm, and evaluates
    each candidate using the provided metric function.

    Usage:
        evolver = GEPAEvolver(skill_content, eval_metric=my_metric_fn)
        best_skill = evolver.evolve(generations=5)
    """

    def __init__(
        self,
        skill_name: str,
        skill_body: str,
        trainset: list[dspy.Example],
        eval_metric,
        *,
        reflection_model: str = "openai/gpt-4o-mini",
        eval_model: str = "openai/gpt-4o-mini",
        pareto_strategy: str = "pareto",
        num_threads: int = 1,
        real_evaluator=None,  # Optional: RealEvaluator for grounded fitness
    ) -> None:
        self._skill_name = skill_name
        self._skill_body = skill_body
        self._trainset = trainset
        self._eval_metric = eval_metric
        self._reflection_model = reflection_model
        self._eval_model = eval_model
        self._pareto_strategy = pareto_strategy
        self._num_threads = num_threads
        self._real_evaluator = real_evaluator
        self._module: Optional[_SkillModule] = None

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def evolve(
        self,
        generations: int = 5,
        *,
        valset: Optional[list[dspy.Example]] = None,
    ) -> tuple[str, float]:
        """Run GEPA evolution.

        Args:
            generations: Number of GEPA iterations.
            valset: Optional validation set (used by GEPA for selection).

        Returns:
            Tuple of (evolved_skill_body: str, best_score: float).
        """
        logger.info(
            "GEPA evolution: %s, %d generations, %d train examples",
            self._skill_name, generations, len(self._trainset),
        )

        # ---- 1. Configure DSPy LM ----
        # GEPA needs an LM for its reflection/mutation proposals.
        # Priority: ~/.hermes/.env -> DEEPSEEK_API_KEY -> OPENROUTER_API_KEY
        _load_hermes_env()
        deepseek_key = os.environ.get("DEEPSEEK_API_KEY") or ""
        openrouter_key = os.environ.get("OPENROUTER_API_KEY") or ""

        if deepseek_key:
            api_key = deepseek_key
            base_url = "https://api.deepseek.com/v1"
            model_name = "deepseek-v4-flash"
        else:
            api_key = openrouter_key
            base_url = "https://openrouter.ai/api/v1"
            model_name = self._reflection_model

        reflection_lm = dspy.LM(
            model=model_name,
            api_key=api_key or None,
            api_base=base_url,
        )
        # Default LM for any DSPy forward passes
        dspy.configure(lm=reflection_lm)

        # ---- 2. Create SkillModule ----
        baseline_module = _SkillModule(self._skill_body)
        self._module = baseline_module  # keep ref for real-eval metric closure

        # ---- 2b. Build metric (real eval overrides the provided metric) ----
        if self._real_evaluator is not None:
            _eval_cache: dict[str, float] = {}

            def _real_metric(gold, pred, trace=None, pred_name=None, pred_trace=None):
                """Metric: run Hermes + Lean on the module's evolved instructions."""
                inst = self._extract_instructions_from_trace(pred_trace)
                if not inst:
                    inst = self._extract_current_instructions()
                skill_text = self._instructions_to_skill(inst)
                skill_key = hashlib.sha256(skill_text.encode()).hexdigest()[:16] if skill_text else "?"
                if skill_key in _eval_cache:
                    return _eval_cache[skill_key]
                logger.info("Real eval for skill variant %s ...", skill_key[:10])
                result = self._real_evaluator.evaluate(skill_text)
                score = getattr(
                    result,
                    "selection_fitness",
                    getattr(result, "thermodynamic_fitness", result.average_fitness),
                )
                _eval_cache[skill_key] = score
                logger.info("  → score: %.3f (%d/%d, %.1fs)",
                            score, result.n_succeeded, len(result.task_results),
                            result.elapsed_seconds)
                if hasattr(result, "policy_fitness"):
                    logger.info("  → policy fitness: %.3f", getattr(result, "policy_fitness", 0.0))
                return score

            chosen_metric = _real_metric
        else:
            chosen_metric = self._eval_metric

        # ---- 3. Configure GEPA ----
        optimizer = dspy.GEPA(
            metric=chosen_metric,
            max_full_evals=generations,
            # Let GEPA propose mutations using the reflection LM
            reflection_lm=reflection_lm,
            candidate_selection_strategy=self._pareto_strategy,
            num_threads=self._num_threads,
            skip_perfect_score=False,  # We want to evaluate even perfect candidates
        )

        # ---- 4. Run optimization ----
        start = time.time()
        try:
            optimized = optimizer.compile(
                student=baseline_module,
                trainset=self._trainset,
                valset=valset,
            )
        except Exception as exc:
            logger.error("GEPA optimization failed: %s", exc)
            return self._skill_body, 0.0

        elapsed = time.time() - start
        logger.info("GEPA completed in %.1fs", elapsed)

        # ---- 5. Extract evolved skill from GEPA-mutated instructions ----
        # GEPA mutates the predictor's instructions (which is the skill text).
        # It may wrap with a prefix OR completely replace the text.
        evolved_body = self._skill_body  # fallback
        for p in optimized._predictor.predictors():
            inst = p.dump_state().get("signature", {}).get("instructions", "")
            if not inst:
                continue
            extracted = self._instructions_to_skill(inst)
            if extracted and len(extracted) > 100:  # reasonable skill size
                evolved_body = extracted
                break

        # Score the evolved skill using the same authority as selection.
        if self._real_evaluator is not None:
            result = self._real_evaluator.evaluate(evolved_body)
            best_score = getattr(
                result,
                "selection_fitness",
                getattr(result, "thermodynamic_fitness", result.average_fitness),
            )
        else:
            best_score = 0.0
            for ex in self._trainset:
                try:
                    pred = optimized(task_input=ex.task_input)
                    score = self._eval_metric(ex, pred)
                    best_score = max(best_score, score)
                except Exception:
                    continue

        logger.info("Evolved skill score: %.4f (baseline: ?)", best_score)
        return evolved_body, best_score

    @staticmethod
    def _instructions_to_skill(inst: str) -> str:
        """Strip DSPy wrapper to get skill body back.

        GEPA may either:
        a) Wrap the skill with "Respond to the task following these instructions:" prefix
        b) Completely replace the instructions with new content (no wrapper)
        """
        if not inst:
            return ""
        # Try to strip the known wrapper prefix
        prefix = "Respond to the task following these instructions:\n\n"
        if prefix in inst:
            body_text = inst.split(prefix, 1)[1]
        else:
            # GEPA replaced instructions entirely — use as-is
            body_text = inst
        # Remove any trailing DSPy field definitions
        if "\n\nTask Input:" in body_text:
            body_text = body_text.split("\n\nTask Input:")[0].strip()
        if "\n\n" in body_text:
            # Only keep up to the first double-newline that precedes field syntax
            parts = body_text.rsplit("\n\n", 1)
            if len(parts) > 1 and ("{" in parts[1] or ":" in parts[1].split("\n")[0]):
                body_text = parts[0]
        return body_text.strip()

    def _extract_current_instructions(self) -> str:
        """Read the current evolved instructions from the module."""
        if self._module is None:
            return self._skill_body
        for p in self._module._predictor.predictors():
            inst = p.dump_state().get("signature", {}).get("instructions", "")
            if inst and "Respond to the task" in inst:
                return inst
        return self._skill_body

    @staticmethod
    def _extract_instructions_from_trace(pred_trace) -> str:
        """Extract candidate instructions from DSPy's GEPA predictor trace."""
        if not pred_trace:
            return ""
        for item in pred_trace:
            predictor = None
            if isinstance(item, tuple) and item:
                predictor = item[0]
            elif isinstance(item, dict):
                predictor = item.get("predictor")
            if predictor is None:
                continue
            signature = getattr(predictor, "signature", None)
            inst = getattr(signature, "instructions", "")
            if inst:
                return str(inst)
        return ""


# ---------------------------------------------------------------------------
# DSPy Module — wraps a skill file as an optimizable module
# ---------------------------------------------------------------------------

class _SkillModule(dspy.Module):
    """A DSPy module whose instructions (skill body) are optimized by GEPA.

    The skill body text is baked into the predictor's instructions so that
    GEPA's reflection-based mutation directly optimizes the skill content.
    After optimization, ``evolved_instructions()`` returns the mutated text.
    """

    def __init__(self, skill_text: str):
        super().__init__()
        # Build a signature whose instructions ARE the skill text
        sig = dspy.Signature("task_input -> output")
        sig.instructions = (
            f"Respond to the task following these instructions:\n\n"
            f"{skill_text}"
        )
        self._skill_text = skill_text
        self._predictor = dspy.ChainOfThought(sig)

    @property
    def skill_text(self) -> str:
        return self._skill_text

    def forward(self, task_input: str) -> dspy.Prediction:
        result = self._predictor(task_input=task_input)
        return dspy.Prediction(output=result.output)

    def evolved_instructions(self) -> str:
        """Extract the GEPA-evolved instructions (mutated skill text)."""
        for p in self._predictor.predictors():
            inst = p.dump_state().get("signature", {}).get("instructions", "")
            if inst and "Respond to the task following these instructions:" in inst:
                return inst
        return self._skill_text


# ---------------------------------------------------------------------------
# Factory: wires GEPA into our existing evaluation infrastructure
# ---------------------------------------------------------------------------

def create_gepa_evolver(
    skill_name: str,
    skill_body: str,
    evaluator,  # EvolutionEvaluator instance
    tasks: list[dict[str, Any]],
    model: str = "openai/gpt-4o-mini",
) -> GEPAEvolver:
    """Create a GEPAEvolver wired to our ArangoDB-based evaluator.

    Args:
        skill_name: Name of the skill being evolved.
        skill_body: The markdown body of the skill (without frontmatter).
        evaluator: An EvolutionEvaluator connected to ArangoDB.
        tasks: List of task dicts (from ArangoDB) to use as training examples.
        model: Model name for GEPA's reflection LM.

    Returns:
        Configured GEPAEvolver instance.
    """
    # Build DSPy examples from ArangoDB tasks
    trainset = []
    for t in tasks:
        formal_target = (t.get("runtime_goal_packet") or {}).get("formal_target", "")
        module_hint = (t.get("runtime_goal_packet") or {}).get("module_hint", "")
        task_key = t.get("_key", "")
        goal_key = t.get("goal_key", "")

        ex = dspy.Example(
            task_input=formal_target or f"Prove goal {goal_key}",
            expected_behavior=f"Fill in the sorry at {formal_target} in module {module_hint}",
            task_key=task_key,
            goal_key=goal_key,
        ).with_inputs("task_input")
        trainset.append(ex)

    # Build the metric function
    def metric(gold, pred, trace=None, pred_name=None, pred_trace=None) -> float:
        """DSPy-compatible metric for GEPA."""
        output = getattr(pred, "output", "") or ""
        expected = getattr(gold, "expected_behavior", "") or ""
        if not output.strip():
            return 0.0
        expected_words = set(expected.lower().split())
        output_words = set(output.lower().split())
        if expected_words:
            overlap = len(expected_words & output_words) / len(expected_words)
            return min(1.0, max(0.0, 0.3 + 0.7 * overlap))
        return 0.5

    return GEPAEvolver(
        skill_name=skill_name,
        skill_body=skill_body,
        trainset=trainset,
        eval_metric=metric,
        reflection_model=model,
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="GEPA skill evolution")
    parser.add_argument("--skill", default="lean-proof", help="Skill name")
    parser.add_argument("--generations", type=int, default=5)
    parser.add_argument("--model", default="openai/gpt-4o-mini")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--real-eval", action="store_true",
                        help="Use real Hermes+Lean evaluation instead of keyword overlap")
    parser.add_argument("--real-eval-tasks", type=int, default=2,
                        help="Number of real sorry tasks for evaluation")
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s [%(name)s] %(message)s")

    # Load the skill
    skill_path = _REPO / "skills" / args.skill / "SKILL.md"
    if not skill_path.exists():
        logger.error("Skill not found: %s", skill_path)
        sys.exit(1)

    raw = skill_path.read_text(encoding="utf-8")
    parts = raw.split("---", 2)
    frontmatter = parts[1].strip() if len(parts) >= 3 else ""
    body = parts[2].strip() if len(parts) >= 3 else raw

    # Load tasks from ArangoDB
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

    pending = aql(ep, db, usr, pwd, """
        FOR t IN hive_tasks
          FILTER t.queue_name == "proof-search"
          FILTER t.status == "pending"
          SORT t.priority DESC
          LIMIT 10
          RETURN t
    """)

    if not pending:
        logger.warning("No pending tasks in queue — using synthetic examples")
        from evolution.core.dataset_builder import SyntheticDatasetBuilder
        from evolution.core.config import EvolutionConfig
        builder = SyntheticDatasetBuilder(EvolutionConfig())
        dataset = builder.generate(artifact_text=body, artifact_type="skill")
        dspy_examples = dataset.to_dspy_examples("train")
    else:
        from tools.infra.evolution_evaluator import EvolutionEvaluator
        evaluator = EvolutionEvaluator(ep, db, usr, pwd)
        evolver = create_gepa_evolver(args.skill, body, evaluator, pending, model=args.model)
        dspy_examples = evolver._trainset

    # ---- Build real evaluation tasks (if --real-eval) ----
    real_eval_tasks = []
    if args.real_eval:
        from tools.infra.gepa_real_eval import build_eval_tasks_from_arango, EvalTask
        real_eval_tasks = build_eval_tasks_from_arango(limit=args.real_eval_tasks)
        if not real_eval_tasks:
            logger.error("No real tasks available for --real-eval")
            sys.exit(1)
        logger.info("Real eval: %d tasks from ArangoDB", len(real_eval_tasks))

    if args.dry_run:
        print(f"Skill    : {args.skill} ({len(body)} chars body)")
        print(f"Model    : {args.model}")
        print(f"Examples : {len(dspy_examples)}")
        print(f"GEPA     : {args.generations} generations")
        print(f"Real eval: {'✓ ' + str(len(real_eval_tasks)) + ' tasks' if args.real_eval else '✗ (keyword overlap)'}")
        print(f"API key  : {'✓ set' if os.environ.get('OPENROUTER_API_KEY') else '✗ missing'}")
        print(f"Base URL : {os.environ.get('OPENAI_BASE_URL', 'https://openrouter.ai/api/v1')}")
        return

    logger.info("Starting GEPA evolution for '%s' (%d examples, real_eval=%s)",
                args.skill, len(dspy_examples), args.real_eval)

    # Load Hermes env for DeepSeek key
    _load_hermes_env()

    # Build RealEvaluator if --real-eval
    real_evaluator = None
    if args.real_eval and real_eval_tasks:
        from tools.infra.gepa_real_eval import RealEvaluator
        real_eval_model = os.environ.get("HERMES_EVAL_MODEL", "deepseek-v4-flash")
        real_evaluator = RealEvaluator(
            tasks=real_eval_tasks,
            hermes_model=real_eval_model,
            compile_check=True,
            timeout=90,
            cache=True,
        )
        # Minimal trainset (1 dummy) — GEPA needs at least 1 example
        dspy_examples = [
            dspy.Example(
                task_input="fill the sorry",
                expected_behavior="sorry is filled and file compiles",
            ).with_inputs("task_input")
        ]
        logger.info("Real eval: %d tasks, model=%s", len(real_eval_tasks), real_eval_model)
    else:
        logger.info("Keyword overlap metric: %d examples", len(dspy_examples))

    # Run GEPA (metric logic is inside GEPAEvolver.evolve)
    evolver = GEPAEvolver(
        skill_name=args.skill,
        skill_body=body,
        trainset=dspy_examples,
        eval_metric=lambda g, p, *a, **kw: 0.5,  # baseline; real_eval or GEPA's internal metric overrides
        reflection_model=args.model,
        real_evaluator=real_evaluator,
    )

    evolved_body, best_score = evolver.evolve(generations=args.generations)

    # Reassemble and save (timestamped)
    evolved_full = f"---\n{frontmatter}\n---\n\n{evolved_body}\n"
    out_dir = _REPO / "quarantine" / "hermes_skills" / "evolved" / args.skill
    out_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = out_dir / f"gepa_evolved_{ts}.md"
    out_path.write_text(evolved_full, encoding="utf-8")
    archive_path = save_rollback_archive(
        skill_name=args.skill,
        skill_content=evolved_full,
        fitness=best_score,
        generation=args.generations,
    )

    # Show diff summary
    original_full = f"---\n{frontmatter}\n---\n\n{body}\n"
    if evolved_full != original_full:
        added = len(evolved_body) - len(body)
        print(f"\nEvolved skill saved: {out_path}")
        print(f"Size change: {added:+d} chars")
        # Show a brief diff
        import difflib
        diff = list(difflib.unified_diff(
            body.splitlines(), evolved_body.splitlines(),
            fromfile="baseline", tofile="evolved", n=3,
        ))
        # Only show first 30 lines of diff
        for line in diff[:30]:
            print(line)
    else:
        print("\nEvolved skill is IDENTICAL to baseline (no mutation occurred)")
    print(f"Best score: {best_score:.4f}")
    print(f"Rollback archive: {archive_path}")

    # ---- Run Proof Seeker on failed tasks ----
    if args.real_eval and real_evaluator is not None and best_score < 1.0:
        try:
            from tools.infra.proof_seeker import ProofSeeker

            seeker = ProofSeeker()
            cache_file = _REPO / "quarantine" / "hermes_skills" / "evolved" / ".eval_cache.jsonl"
            sought = 0
            if cache_file.exists():
                for line in cache_file.read_text().strip().split("\n"):
                    if not line.strip():
                        continue
                    entry = json.loads(line)
                    if entry.get("succeeded", True) or "file" not in entry:
                        continue

                    target_name = Path(entry["file"]).stem
                    context_file = _REPO / entry["file"]
                    target_line = entry.get("line", 0)

                    logger.info("Proof Seeker: searching for '%s'", target_name)
                    results = seeker.search(
                        target_name,
                        module_hint=entry.get("file", ""),
                        max_results=5,
                    )

                    if results:
                        sought += 1
                        print(f"  [SEEKER] Found {len(results)} results for {target_name}")
                        for r in results[:3]:
                            print(f"          [{r.source:10s}] {r.title[:80]}")

                        # Try to digest and formalize
                        context_code = context_file.read_text(errors="replace") if context_file.exists() else ""
                        candidate = seeker.digest(results, target_name, context_code)
                        if candidate.proof_lean:
                            print(f"          Proof candidate ({candidate.confidence:.2f} confidence)")
                        else:
                            print(f"          No proof generated")

            if sought:
                print(f"  [SEEKER] Searched for {sought} failed tasks")
        except ImportError:
            logger.debug("ProofSeeker not available — skipping")
        except Exception as exc:
            logger.warning("Proof Seeker error: %s", exc)

    # ---- Run Vacuity Critic on real-eval results ----
    if args.real_eval and real_evaluator is not None:
        try:
            from tools.infra.vacuity_critic import VacuityCritic, FailCase

            # Build failure cases from the evaluator's cached results
            critic = VacuityCritic()
            failures = []

            # Read the evaluator cache to find failed tasks
            cache_file = _REPO / "quarantine" / "hermes_skills" / "evolved" / ".eval_cache.jsonl"
            if cache_file.exists():
                for line in cache_file.read_text().strip().split("\n"):
                    if not line.strip():
                        continue
                    entry = json.loads(line)
                    if not entry.get("succeeded", True):
                        from datetime import datetime as _dt
                        failures.append(FailCase(
                            task_file=entry.get("file", ""),
                            task_line=entry.get("line", 0),
                            skill_name=args.skill,
                            skill_content_preview=evolved_body[:2000],
                            hermes_output="",
                            error=entry.get("error", "unknown"),
                            original_line=f"{entry.get('file', '?')}:{entry.get('line', 0)}",
                            timestamp=_dt.now().isoformat(),
                        ))

            if failures:
                logger.info("Vacuity Critic: reviewing %d failed evaluations", len(failures))
                new_patterns = critic.review_failures(failures)

                if new_patterns:
                    logger.info("Discovered %d new obfuscation patterns!", len(new_patterns))
                    # Extend the skill if we're running on a closure-debt skill
                    if "closure-debt" in args.skill:
                        skill_path = _REPO / "skills" / args.skill / "SKILL.md"
                        critic.extend_skill(skill_path, new_patterns)
                        logger.info("Skill extended with new anti-patterns: %s", skill_path)

                    # Update the codex reference
                    codex_path = _REPO / "docs" / "codex" / "codex.md"
                    if codex_path.exists():
                        # Append a record of the discovery
                        with open(codex_path, "a") as f:
                            f.write(f"\n### Discovery: {ts}\n\n")
                            for p in new_patterns:
                                f.write(f"- **{p.name}** — {p.category} ({p.severity}), "
                                        f"synonym of {p.synonym_of or '?'}\n")
                        logger.info("Codex updated: %s", codex_path)

                    for p in new_patterns:
                        print(f"  [CRITIC] New pattern: {p.name} ({p.category})")
                else:
                    logger.info("Vacuity Critic: no new patterns discovered")
            else:
                logger.info("Vacuity Critic: no failed evaluations to review")
        except ImportError:
            logger.debug("VacuityCritic not available — skipping")
        except Exception as exc:
            logger.warning("Vacuity Critic error: %s", exc)


if __name__ == "__main__":
    main()
