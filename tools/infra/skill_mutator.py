#!/usr/bin/env python3
"""SKILL.md mutation engine for Hermes self-evolution.

Takes a skill's current content + failure cases (error traces, deadend
diagnostics from ArangoDB) and proposes improved variants using an LLM.
Each variant targets specific weaknesses revealed by the observed failures.
"""

from __future__ import annotations

import json
import logging
import os
import re
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
from typing import Any

logger = logging.getLogger("skill_mutator")

DEFAULT_MUTATOR_MODEL = "openai/gpt-4o-mini"   # cheap, fast for small mutations
DEFAULT_MUTATOR_URL = "https://openrouter.ai/api/v1"
DEFAULT_NUM_VARIANTS = 3

MUTATION_SYSTEM_PROMPT = """You are a skill evolution engine for a Lean 4 theorem-proving agent.

Your task is to mutate a skill file (SKILL.md) to improve its ability to produce
correct Lean 4 proofs.  You will receive:

1. The current skill content (markdown with YAML frontmatter)
2. A list of failure cases — actual Lean errors encountered when using this skill

Your job: produce an improved version of the skill that would help the agent
avoid or recover from the observed failure patterns.

**Mutation rules:**
- Preserve the YAML frontmatter; only update `description` and `version` if relevant.
- Keep the same overall structure and tone — do not rewrite from scratch.
- Target the specific sections most relevant to the failures:
  - *Tactical approach* — if failures suggest wrong tactic choices
  - *Error handling / recovery* — if failures repeat without recovery
  - *Search strategy* — if failures are about missing lemmas or imports
  - *Anti-patterns* — if failures match known anti-patterns
- Add concrete, actionable guidance.  Avoid vague advice like "be careful".
- Each mutation should be focused: change 1-3 sections meaningfully.
- If the failure suggests a missing pattern entirely, add a new subsection.

Output format: return ONLY the mutated SKILL.md content, starting with `---`.
Do not wrap in markdown code fences.  Do not add commentary before or after."""


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass
class FailureCase:
    """A single proof attempt failure that the mutator can learn from."""
    error_summary: str
    failure_pattern: str | None = None
    lean_error_output: str | None = None   # raw Lean diagnostic
    goal_context: str | None = None         # what was being proved
    attempted_strategy: str | None = None   # what the skill suggested
    module: str | None = None

    def to_prompt_block(self, idx: int) -> str:
        lines = [f"### Failure {idx}"]
        if self.module:
            lines.append(f"Module: `{self.module}`")
        if self.goal_context:
            lines.append(f"Goal: {self.goal_context[:200]}")
        if self.error_summary:
            lines.append(f"Error: {self.error_summary[:300]}")
        if self.failure_pattern:
            lines.append(f"Pattern: {self.failure_pattern}")
        if self.lean_error_output:
            lines.append(f"Lean output:\n```\n{self.lean_error_output[:600]}\n```")
        return "\n".join(lines)


@dataclass
class MutationResult:
    """Result of one mutation pass."""
    variant_index: int
    content: str
    token_estimate: int
    timestamp: str


# ---------------------------------------------------------------------------
# Mutator
# ---------------------------------------------------------------------------

class SkillMutator:
    """Proposes mutated variants of a SKILL.md given observed failures.

    Uses an OpenAI-compatible API (default: OpenRouter) as the mutation engine.
    """

    def __init__(
        self,
        api_key: str,
        base_url: str = DEFAULT_MUTATOR_URL,
        model: str = DEFAULT_MUTATOR_MODEL,
        num_variants: int = DEFAULT_NUM_VARIANTS,
    ) -> None:
        self._api_key = api_key
        self._base_url = base_url.rstrip("/")
        self._model = model
        self._num_variants = num_variants

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def mutate(
        self,
        skill_content: str,
        failures: list[FailureCase],
        *,
        parent_fitness: float | None = None,
    ) -> list[MutationResult]:
        """Generate mutated variants of *skill_content* informed by *failures*.

        Returns *num_variants* distinct variants.  On error (e.g. API
        outage) returns fewer or falls back to the original.
        """
        if not skill_content.strip():
            logger.warning("Empty skill content — nothing to mutate")
            return []

        prompt = self._build_prompt(skill_content, failures, parent_fitness)
        variants: list[MutationResult] = []

        for i in range(self._num_variants):
            try:
                content = self._call_llm(prompt) or skill_content
                # The LLM may return fence-wrapped content; strip fences
                content = self._clean_response(content)
                if not self._looks_like_skill_md(content):
                    logger.warning("Variant %d response doesn't look like SKILL.md — keeping original", i)
                    content = skill_content
                variants.append(MutationResult(
                    variant_index=i,
                    content=content,
                    token_estimate=len(prompt) + len(content) // 2,
                    timestamp=__import__("datetime").datetime.now(
                        __import__("datetime").timezone.utc
                    ).isoformat(),
                ))
            except Exception as exc:
                logger.error("Mutation variant %d failed: %s", i, exc)
                continue

        # At minimum, keep the original as variant[0]
        if not variants:
            variants.append(MutationResult(
                variant_index=0,
                content=skill_content,
                token_estimate=0,
                timestamp="fallback-original",
            ))

        return variants

    # ------------------------------------------------------------------
    # Internal
    # ------------------------------------------------------------------

    def _build_prompt(
        self,
        skill_content: str,
        failures: list[FailureCase],
        parent_fitness: float | None,
    ) -> str:
        parts = [MUTATION_SYSTEM_PROMPT, "\n\n"]

        parts.append("## Current Skill\n")
        parts.append("```markdown\n")
        parts.append(skill_content)
        parts.append("\n```\n\n")

        if parent_fitness is not None:
            parts.append(f"Current fitness score: {parent_fitness:.3f} / 1.0\n\n")

        if failures:
            parts.append("## Observed Failures\n")
            parts.append(f"The skill failed {len(failures)} time(s) recently:\n\n")
            for i, f in enumerate(failures):
                parts.append(f.to_prompt_block(i))
                parts.append("\n")
        else:
            parts.append("## No failures recorded\n")
            parts.append("Propose a general improvement to make the skill more robust.\n")

        parts.append("\n## Instruction\n")
        parts.append("Produce a single mutated variant of the skill above. ")
        parts.append("Target the sections most related to the observed failures. ")
        parts.append("Make concrete changes—add new error-handling steps, ")
        parts.append("revise the tactical guidance, or strengthen the search strategy. ")
        parts.append("Output ONLY the mutated SKILL.md content.\n")

        return "".join(parts)

    def _call_llm(self, prompt: str) -> str | None:
        from openai import OpenAI

        # Ensure the API key reaches the SDK regardless of env var name
        key = self._api_key
        if not key:
            key = os.environ.get("OPENROUTER_API_KEY") or os.environ.get("OPENAI_API_KEY") or ""

        client = OpenAI(
            api_key=key or None,
            base_url=self._base_url,
        )
        resp = client.chat.completions.create(
            model=self._model,
            messages=[
                {"role": "system", "content": MUTATION_SYSTEM_PROMPT},
                {"role": "user", "content": prompt},
            ],
            temperature=0.7 + (hash(prompt) % 30) / 100,  # slight per-request jitter
            max_tokens=4096,
        )
        msg = resp.choices[0].message
        return msg.content

    @staticmethod
    def _clean_response(raw: str) -> str:
        """Remove common LLM wrapping artifacts."""
        # Strip outer code fences
        raw = re.sub(r"^```(?:markdown|yaml)?\s*\n?", "", raw.strip())
        raw = re.sub(r"\n?```\s*$", "", raw)
        # Ensure it starts with frontmatter
        if not raw.startswith("---"):
            # Try to find the first frontmatter delimiter
            idx = raw.find("\n---")
            if idx > 0:
                raw = raw[idx + 1:]
            else:
                raw = "---\nname: placeholder-mutation\n---\n" + raw
        return raw.strip()

    @staticmethod
    def _looks_like_skill_md(content: str) -> bool:
        """Cheap validation: must have frontmatter delimiters and a name field."""
        return ("---" in content[:500] and "name:" in content[:500] and len(content) > 100)


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------

def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Mutate a SKILL.md given failure cases")
    parser.add_argument("--skill", default="skills/lean-proof/SKILL.md", help="Path to SKILL.md")
    parser.add_argument("--failures", help="JSON file with failure cases", default=None)
    parser.add_argument("--model", default=DEFAULT_MUTATOR_MODEL)
    parser.add_argument("--variants", type=int, default=2)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    skill_path = Path(args.skill) if args.skill else Path.cwd()
    if not skill_path.exists():
        # Try resolving from repo root
        skill_path = Path.cwd() / args.skill
    if not skill_path.exists():
        print(f"Skill not found: {args.skill}")
        sys.exit(1)

    skill_content = skill_path.read_text(encoding="utf-8")

    failures = []
    if args.failures:
        with open(args.failures) as f:
            raw = json.load(f)
        for item in raw:
            failures.append(FailureCase(**item))
    else:
        # Synthetic failure for smoke test
        failures.append(FailureCase(
            error_summary="unknown identifier: `some_missing_theorem`",
            failure_pattern="missing_identifier",
            lean_error_output="error: unknown identifier 'some_missing_theorem'",
            goal_context="theorem test : A → A := by",
        ))

    api_key = os.environ.get("OPENROUTER_API_KEY", "")
    if not api_key:
        print("OPENROUTER_API_KEY not set. Use --dry-run to validate without calling LLM.")
        if not args.dry_run:
            sys.exit(1)

    if args.dry_run:
        print(f"Skill     : {skill_path}")
        print(f"Model     : {args.model}")
        print(f"Variants  : {args.variants}")
        print(f"Failures  : {len(failures)}")
        print(f"API key   : {'✓ set' if api_key else '✗ missing'}")
        prompt = SkillMutator(api_key=api_key)._build_prompt(skill_content, failures, 0.5)
        print(f"Prompt len: ~{len(prompt)} chars")
        return

    mutator = SkillMutator(api_key=api_key, model=args.model, num_variants=args.variants)
    results = mutator.mutate(skill_content, failures)

    out_dir = Path("quarantine/hermes_skills/evolved/mutation_smoke")
    out_dir.mkdir(parents=True, exist_ok=True)
    for r in results:
        path = out_dir / f"variant_{r.variant_index}.md"
        path.write_text(r.content)
        print(f"Wrote {path} ({len(r.content)} chars)")

    print(f"\nGenerated {len(results)} variants")


if __name__ == "__main__":
    import os, sys
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    main()
