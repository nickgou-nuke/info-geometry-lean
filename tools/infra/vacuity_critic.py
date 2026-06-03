#!/usr/bin/env python3
"""Vacuity Critic — identifies new obfuscation patterns and extends the evaluator.

The critic sits above GEPA and extends the evolution loop at Level 1:
it reviews failed evaluations, identifies synonymic obfuscation patterns
that the current evaluator missed, and extends both the detection schema
and the skill's anti-pattern list.

Usage:
    python3 tools/infra/vacuity_critic.py \\
        --failed-tasks artifacts/eval_failures.jsonl \\
        --skill skills/closure-debt-proof/SKILL.md \\
        --schema tools/schema/vacuity/certificate_patterns.json \\
        --update-skill
"""

from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import sys
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, Optional

logger = logging.getLogger("vacuity_critic")

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass
class ObfuscationPattern:
    """A single obfuscation pattern detected by the critic."""
    name: str                     # e.g., "_guarantee", "_pledge"
    pattern: str                  # regex or structural pattern
    category: str                 # "certificate_field", "true_default", "wrapper"
    severity: str                 # "high", "medium", "low"
    example: str                  # example Lean code
    discovered_by: str            # "critic" or "manual"
    synonym_of: str = ""          # what known pattern this is a synonym of

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass
class FailCase:
    """A failed evaluation task for the critic to analyze."""
    task_file: str
    task_line: int
    skill_name: str
    skill_content_preview: str
    hermes_output: str
    error: str
    original_line: str
    timestamp: str

    @classmethod
    def from_eval_result(cls, result: dict, task_result: dict) -> "FailCase":
        return cls(
            task_file=task_result.get("file", "?"),
            task_line=task_result.get("line", 0),
            skill_name=result.get("skill_name", "?"),
            # Trim to avoid bloating
            skill_content_preview=result.get("skill_body", "")[:2000],
            hermes_output=task_result.get("hermes_output", "")[:3000],
            error=task_result.get("error", ""),
            original_line=f"{task_result.get('file', '?')}:{task_result.get('line', 0)}",
            timestamp=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        )


# ---------------------------------------------------------------------------
# The Critic
# ---------------------------------------------------------------------------

class VacuityCritic:
    """Reviews failed evaluations and extends the detection schema.

    Uses an LLM to identify new obfuscation patterns from failed tasks,
    then updates both the schema file and optionally the skill file.
    """

    KNOWN_CATEGORIES = {
        "certificate_field": "Field with `_cert`, `_valid`, `_witness`, `_guarantee` etc. suffix of type Prop",
        "true_default": "Prop field with `:= True` or `:= by` that defaults to trivial truth",
        "wrapper": "A field that wraps another certificate (indirection)",
        "hidden_sorry": "A `sorry` hidden inside a `Prop := by` block",
        "naming_synonym": "A new synonym of an existing certificate naming pattern",
    }

    # Base schema: patterns we already know about
    BASE_PATTERNS = [
        ObfuscationPattern("_True", r"\w+_True\s*:", "certificate_field", "high",
                           "someProperty_True : Prop := True", "builtin"),
        ObfuscationPattern("_sorryProof", r"\w+_sorryProof\s*:", "certificate_field", "high",
                           "someProperty_sorryProof : someProperty_True", "builtin"),
        ObfuscationPattern("_certificate", r"\w+_certificate\s*:", "certificate_field", "high",
                           "result_certificate : Prop := by sorry", "builtin"),
        ObfuscationPattern("_valid", r"\w+_valid\s*:", "certificate_field", "medium",
                           "x_valid : Prop := by sorry", "builtin"),
        ObfuscationPattern("_witness", r"\w+_witness\s*:", "certificate_field", "medium",
                           "y_witness : Prop := by sorry", "builtin"),
        ObfuscationPattern("_bridge", r"\w+_bridge\s*:", "certificate_field", "medium",
                           "z_bridge : Prop := by sorry", "builtin"),
    ]

    def __init__(
        self,
        schema_path: Optional[Path] = None,
        critic_model: str = "deepseek-v4-flash",
    ):
        self._schema_path = schema_path or _REPO / "tools" / "schema" / "vacuity" / "certificate_patterns.json"
        self._critic_model = critic_model
        self._patterns = list(self.BASE_PATTERNS)
        self._load_schema()

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def review_failures(
        self,
        failures: list[FailCase],
        *,
        verbose: bool = False,
    ) -> list[ObfuscationPattern]:
        """Analyze failed tasks and return newly discovered patterns.

        The critic:
        1. Groups failures by error message
        2. Extracts the obfuscated field name from the task context
        3. Calls the LLM to classify whether the pattern is a new synonym
        4. Returns any novel patterns discovered
        """
        if not failures:
            logger.info("No failures to review")
            return []

        logger.info("Reviewing %d failed evaluations", len(failures))

        new_patterns: list[ObfuscationPattern] = []
        seen = set()

        for f in failures:
            # Extract the field name from the original line context
            field_name = self._extract_field_name(f.original_line)
            if not field_name:
                continue

            # Check if we already know about this suffix
            suffix = self._extract_suffix(field_name)
            if not suffix:
                continue

            if suffix in seen or self._is_known_pattern(suffix):
                seen.add(suffix)
                continue

            seen.add(suffix)

            # Call the LLM to classify this new pattern
            pattern = self._classify_pattern(f, suffix, field_name, verbose=verbose)
            if pattern:
                new_patterns.append(pattern)
                self._patterns.append(pattern)
                logger.info("  Discovered new pattern: %s (%s)", pattern.name, pattern.category)

        if new_patterns:
            self._save_schema()

        return new_patterns

    def extend_skill(
        self,
        skill_path: Path,
        new_patterns: list[ObfuscationPattern],
        *,
        dry_run: bool = False,
    ) -> str:
        """Add newly discovered patterns to the skill's anti-pattern section.

        Returns the updated skill content (or dry-run diff).
        """
        if not new_patterns:
            return ""

        skill_text = skill_path.read_text(encoding="utf-8")
        original = skill_text

        # Build an anti-pattern block for the new patterns
        new_entries = []
        for p in new_patterns:
            new_entries.append(f"- `{p.name}` — {p.category} synonym, detected by critic")

        # Find the anti-pattern area or create one
        anti_pattern_marker = "## Anti-patterns"
        if anti_pattern_marker in skill_text:
            # Insert after the anti-pattern section header
            insert_point = skill_text.index(anti_pattern_marker)
            insert_point = skill_text.index("\n", insert_point) + 1
            insert_point = skill_text.index("\n", insert_point) + 1  # skip blank line
            new_block = "\n".join(new_entries) + "\n"
            skill_text = skill_text[:insert_point] + new_block + skill_text[insert_point:]
        else:
            # Append a new anti-pattern section
            new_block = (
                f"\n## Anti-patterns\n\n"
                f"### Detected by Vacuity Critic\n\n"
                + "\n".join(new_entries) + "\n"
            )
            skill_text = skill_text.rstrip() + new_block

        if not dry_run:
            skill_path.write_text(skill_text, encoding="utf-8")
            logger.info("Extended skill with %d new anti-patterns", len(new_patterns))

        return self._diff(original, skill_text) if dry_run else "Updated"

    def synthesize_candidates(self) -> list[str]:
        """Use the LLM to generate CANDIDATE patterns for the list.

        The principle is used INTERNALLY by the critic as a heuristic to surface
        candidates — it is NEVER written into the skill. The candidates are
        added to the explicit list (the conscious ego).
        """
        self._load_hermes_env()
        api_key = os.environ.get("DEEPSEEK_API_KEY") or os.environ.get("OPENROUTER_API_KEY") or ""
        if not api_key:
            return []

        patterns_summary = "\n".join(
            f"  {p.name:20s}" for p in self._patterns
        )

        prompt = (
            f"List 12 synonyms for guarantee, warranty, certificate, assurance, witness, "
            f"validation, bridge, true. Include rare and domain-specific terms from law, "
            f"theology, accounting, quality assurance.\n"
            f"Return ONLY JSON array: [\"_word1\", \"_word2\", ...]"
        )

        try:
            import subprocess
            result = subprocess.run(
                ["hermes", "chat", "-m", self._critic_model, "-q", prompt,
                 "--accept-hooks", "--yolo", "-Q"],
                capture_output=True, text=True, timeout=30,
            )
            text = (result.stdout or "") + (result.stderr or "")
            m = re.search(r"\[.*?\]", text, re.DOTALL)
            if m:
                candidates = json.loads(m.group())
                # Normalize: add underscore prefix if missing
                normalized = []
                for c in candidates:
                    if not isinstance(c, str):
                        continue
                    if not c.startswith("_"):
                        c = "_" + c
                    normalized.append(c)
                return normalized
        except Exception as exc:
            logger.debug("Candidate synthesis failed: %s", exc)
        return []

    def expand_dictionary(self, skill_path: Path, *, dry_run: bool = False) -> str:
        """Expand the skill's explicit obfuscation dictionary using LLM-generated candidates.

        The list IS the comprehension. This method adds new candidate suffixes
        to the skill's anti-pattern list. Each candidate is explicitly named.
        Returns a summary of what was added.
        """
        candidates = self.synthesize_candidates()
        if not candidates:
            return "No candidates generated"

        # Filter already-known patterns
        new_suffixes = [c for c in candidates if not self._is_known_pattern(c)]
        if not new_suffixes:
            return "All candidates already known"

        skill_text = skill_path.read_text(encoding="utf-8")

        # Build the anti-pattern entries for new suffixes
        new_entries = []
        for s in new_suffixes:
            name = s.strip("_")
            new_entries.append(
                f"- `{s}` — certificate/assurance synonym, detected by Vacuity Critic"
            )

        entries_block = "\n".join(new_entries) + "\n"

        # Find or create the anti-patterns section
        if "## Anti-patterns" in skill_text:
            # Insert after the anti-patterns section header
            idx = skill_text.index("## Anti-patterns")
            idx = skill_text.index("\n", idx) + 1  # past header
            updated = skill_text[:idx] + "\n" + entries_block + skill_text[idx:]
        else:
            # Append before the last section, or at end
            updated = skill_text.rstrip() + f"\n\n## Anti-patterns\n\n### Critic Discoveries\n\n{entries_block}\n"

        if dry_run:
            import difflib
            diff_lines = list(difflib.unified_diff(
                skill_text.splitlines(), updated.splitlines(),
                fromfile="before", tofile="after", n=3,
            ))
            return f"{len(new_suffixes)} candidates would be added:\n" + \
                   "\n".join(f"  + {s}" for s in new_suffixes) + \
                   "\n" + "\n".join(diff_lines[:20])

        skill_path.write_text(updated, encoding="utf-8")
        logger.info("Dictionary expanded: %s (+%d entries)", skill_path, len(new_suffixes))
        return f"Added {len(new_suffixes)} new suffixes to skill dictionary:\n" + \
               "\n".join(f"  + {s}" for s in new_suffixes[:20])

    def refactor_skill_core(self, skill_path: Path, *, dry_run: bool = False) -> str:
        """Deprecated: use expand_dictionary instead.

        The list IS the comprehension. Principle-based refactoring would
        replace ground truth with confabulation. This method is kept for
        backward compatibility but delegates to expand_dictionary.
        """
        return self.expand_dictionary(skill_path, dry_run=dry_run)

    def evaluate_coverage(self, file_path: Path) -> dict[str, Any]:
        """Evaluate how many obfuscation patterns exist in a file."""
        text = file_path.read_text(encoding="utf-8")
        matches = []
        for p in self._patterns:
            for i, line in enumerate(text.split("\n"), 1):
                if re.search(p.pattern, line):
                    matches.append({"line": i, "pattern": p.name, "line_content": line.strip()})
                    break  # one match per pattern per file

        return {
            "file": str(file_path),
            "total_patterns": len(self._patterns),
            "matched": len(matches),
            "coverage": len(matches) / max(1, len(self._patterns)),
            "matches": matches,
        }

    # ------------------------------------------------------------------
    # Internal
    # ------------------------------------------------------------------

    def _extract_field_name(self, line_context: str) -> str:
        """Extract the certificate field name from an error context."""
        m = re.search(r'Prove `([^`]+)`', line_context)
        if m:
            return m.group(1)
        m = re.search(r'Replace `([^`]+)`', line_context)
        if m:
            return m.group(1)
        return ""

    def _extract_suffix(self, field_name: str) -> str:
        """Extract the suffix from a field name like ``result_certificate``."""
        m = re.search(r"_([a-zA-Z]+)$", field_name)
        return f"_{m.group(1)}" if m else ""

    def _is_known_pattern(self, suffix: str) -> bool:
        """Check if a suffix is already covered by known patterns."""
        suffix_lower = suffix.lower()
        for p in self._patterns:
            if p.name.lower() == suffix_lower:
                return True
            if p.name.lower() in suffix_lower or suffix_lower in p.name.lower():
                return True
        return False

    def _classify_pattern(
        self,
        fail: FailCase,
        suffix: str,
        field_name: str,
        *,
        verbose: bool = False,
    ) -> Optional[ObfuscationPattern]:
        """Use the LLM to classify a new obfuscation synonym via Hermes CLI."""
        prompt = (
            f"You are an obfuscation pattern detector for Lean 4 code. "
            f"A proof-filling agent failed to fill a `sorry` in a file because "
            f"the obfuscation pattern used an unrecognized naming convention.\n\n"
            f"Failed task:\n"
            f"  File: {fail.task_file}:{fail.task_line}\n"
            f"  Error: {fail.error}\n"
            f"  Field name: {field_name}\n"
            f"  Suffix: {suffix}\n\n"
            f"Known obfuscation patterns:\n"
            + "\n".join(f"  {p.name} ({p.category})" for p in self._patterns) +
            f"\n\n"
            f"Is `{suffix}` a synonym of any known pattern? "
            f"Answer with JSON: {{\"is_synonym\": true/false, \"synonym_of\": \"...\", "
            f"\"category\": \"certificate_field|true_default|wrapper|hidden_sorry|naming_synonym\", "
            f"\"severity\": \"high|medium|low\", \"example\": \"...\", "
            f"\"rationale\": \"...\"}}"
        )

        try:
            import subprocess
            result = subprocess.run(
                ["hermes", "chat", "-m", self._critic_model, "-q", prompt,
                 "--accept-hooks", "--yolo", "-Q"],
                capture_output=True, text=True, timeout=30,
            )
            text = (result.stdout or "") + (result.stderr or "")

            # Parse JSON from the response
            m = re.search(r"\{.*\}", text, re.DOTALL)
            if m:
                data = json.loads(m.group())
                if data.get("is_synonym") and data.get("synonym_of"):
                    return ObfuscationPattern(
                        name=suffix,
                        pattern=rf"\w+{re.escape(suffix)}\s*:",
                        category=data.get("category", "naming_synonym"),
                        severity=data.get("severity", "medium"),
                        example=data.get("example", f"someField{suffix} : Prop := True"),
                        discovered_by="critic",
                        synonym_of=data.get("synonym_of", ""),
                    )
        except Exception as exc:
            if verbose:
                logger.debug("LLM classification failed: %s", exc)

        return self._heuristic_classify(suffix, field_name)

    def _heuristic_classify(self, suffix: str, field_name: str) -> Optional[ObfuscationPattern]:
        """Fallback classification when LLM is unavailable."""
        # Common assurance synonyms that might be used as obfuscation
        assurance_suffixes = [
            "_guarantee", "_pledge", "_vouch", "_attest", "_endorse",
            "_cert", "_confirm", "_warrant", "_avow", "_testify",
            "_assure", "_swear", "_undertake", "_promise", "_covenant",
            "_bond", "_seal", "_stamp", "_notarize", "_bear_witness",
        ]

        if suffix in assurance_suffixes:
            return ObfuscationPattern(
                name=suffix,
                pattern=rf"\w+{re.escape(suffix)}\s*:",
                category="naming_synonym",
                severity="medium",
                example=f"someField{suffix} : Prop := True",
                discovered_by="critic_heuristic",
                synonym_of="_certificate" if "_cert" in suffix else "_witness" if "_witness" in suffix else "_True",
            )
        return None

    def _load_schema(self) -> None:
        if self._schema_path and self._schema_path.exists():
            try:
                data = json.loads(self._schema_path.read_text())
                for item in data.get("patterns", []):
                    self._patterns.append(ObfuscationPattern(**item))
                logger.debug("Loaded %d patterns from schema", len(self._patterns))
            except Exception as exc:
                logger.warning("Failed to load schema: %s", exc)

    def _save_schema(self) -> None:
        if not self._schema_path:
            return
        self._schema_path.parent.mkdir(parents=True, exist_ok=True)
        data = {
            "version": 2,
            "description": "Obfuscation certificate patterns detected by Vacuity Critic",
            "patterns": [p.to_dict() for p in self._patterns],
        }
        self._schema_path.write_text(json.dumps(data, indent=2, ensure_ascii=False))
        logger.info("Schema saved: %s (%d patterns)", self._schema_path, len(self._patterns))

    @staticmethod
    def _load_hermes_env() -> None:
        env_path = Path.home() / ".hermes" / ".env"
        if not env_path.exists():
            return
        try:
            import dotenv
            dotenv.load_dotenv(env_path)
        except ImportError:
            for line in env_path.read_text().splitlines():
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                key, _, val = line.partition("=")
                key = key.strip()
                val = val.strip().strip("'\"")
                if key and val and not os.environ.get(key):
                    os.environ[key] = val

    @staticmethod
    def _diff(original: str, updated: str) -> str:
        import difflib
        return "\n".join(difflib.unified_diff(
            original.splitlines(), updated.splitlines(),
            fromfile="original", tofile="updated", n=3,
        )[:30])


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Vacuity Critic — discover new obfuscation patterns")
    parser.add_argument("--failed-tasks", type=Path, help="JSONL file with failed evaluation results")
    parser.add_argument("--skill", type=Path, default=_REPO / "skills" / "closure-debt-proof" / "SKILL.md")
    parser.add_argument("--schema", type=Path, default=None)
    parser.add_argument("--update-skill", action="store_true", help="Write new patterns into SKILL.md")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--scan-file", type=Path, help="Scan a Lean file for known patterns")
    parser.add_argument("--refactor", action="store_true", dest="_deprecated_refactor",
                        help=argparse.SUPPRESS)  # kept for compat, delegates to expand-dictionary
    parser.add_argument("--expand-dictionary", action="store_true",
                        help="Expand skill's explicit obfuscation dictionary with new suffix candidates")
    parser.add_argument("--synthesize", action="store_true", dest="_deprecated_synthesize",
                        help=argparse.SUPPRESS)
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(name)s] %(message)s")

    critic = VacuityCritic(schema_path=args.schema)

    if args._deprecated_refactor or args.expand_dictionary:
        result = critic.expand_dictionary(args.skill, dry_run=args.dry_run)
        print(result)
        return

    if args._deprecated_synthesize:
        candidates = critic.synthesize_candidates()
        if candidates:
            print(f"Synthesized {len(candidates)} candidate suffixes:")
            for c in candidates[:20]:
                print(f"  {c}")
        else:
            print("Candidate synthesis returned nothing")
        return

    if args.scan_file:
        report = critic.evaluate_coverage(args.scan_file)
        print(f"Coverage report for {args.scan_file}:")
        print(f"  Patterns: {report['matched']}/{report['total_patterns']} matched ({report['coverage']:.0%})")
        for m in report["matches"]:
            print(f"  Line {m['line']:5d}: {m['pattern']:20s} {m['line_content'][:60]}")
        return

    if args.failed_tasks:
        failures = []
        for line in args.failed_tasks.read_text().strip().split("\n"):
            if line.strip():
                data = json.loads(line)
                failures.append(FailCase(**data))

        new_patterns = critic.review_failures(failures, verbose=not args.dry_run)

        if new_patterns:
            print(f"\nDiscovered {len(new_patterns)} new pattern(s):")
            for p in new_patterns:
                print(f"  {p.name:20s} ({p.category:20s}) synonym of {p.synonym_of or '?'}")

            if args.update_skill and not args.dry_run:
                critic.extend_skill(args.skill, new_patterns)
                print(f"Skill extended: {args.skill}")
        else:
            print("No new patterns discovered.")
    else:
        # Default: show current coverage on the test file
        test_file = _REPO / "lean" / "InfoGeometry" / "Eval" / "ClosureDebtTest.lean"
        if test_file.exists():
            report = critic.evaluate_coverage(test_file)
            print(f"Current evaluator coverage on ClosureDebtTest.lean:")
            print(f"  {report['matched']}/{report['total_patterns']} patterns matched")
            for m in report["matches"]:
                print(f"  Line {m['line']:5d}: {m['pattern']}")

        print(f"\nBase schema: {len(critic._patterns)} patterns")
        print(f"Schema file: {critic._schema_path}")
        print(f"Skill file:  {args.skill}")
        if args.dry_run:
            print("Dry run — no changes made")


if __name__ == "__main__":
    main()
