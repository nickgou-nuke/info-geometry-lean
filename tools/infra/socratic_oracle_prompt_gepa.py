#!/usr/bin/env python3
"""Archive-first GEPA-style evolution for Socratic oracle prompt addenda.

This script does not send prompts and does not modify the stable oracle
workflow. It ranks additive prompt profiles using archived oracle event reports
and a small repo-style prior. Deployment is refused unless the archive contains
enough empirical proof-repair outcomes for the winning profile.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import re
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_PROFILES_DIR = ROOT / "configs" / "oracle_prompt_profiles"
DEFAULT_ARCHIVE_DIR = ROOT / "quarantine" / "oracle_prompt_gepa" / "archive"

REQUIRED_SIGNALS = (
    "complete owner file",
    "lean",
    "kernel",
    "root cause",
    "minimal",
    "patch",
    "mathlib",
)

FORBIDDEN_PATTERNS = (
    re.compile(r"\b(?:use|add|insert|leave|keep)\s+`?(?:sorry|admit|axiom)`?", re.IGNORECASE),
    re.compile(r"\b(?:sorry|admit|axiom)s?\s+(?:are|is)\s+(?:ok|okay|acceptable|allowed)\b", re.IGNORECASE),
    re.compile(r"\b(?:show|reveal|provide|recover)\s+(?:hidden\s+)?chain[- ]of[- ]thought\b", re.IGNORECASE),
    re.compile(r"\bignore (?:the )?compiler\b", re.IGNORECASE),
    re.compile(r"\brewrite (?:the )?(?:whole|entire) file\b", re.IGNORECASE),
)

MUTATIONS = (
    "State the exact Lean API shape before proposing the patch.",
    "Penalize any answer that changes theorem content instead of repairing proof structure.",
    "If the proof already compiles, return only a robustness audit and no speculative rewrite.",
    "Name all remaining obligations as compiler-checkable facts, not prose.",
    "Prefer one integrated patch over multiple independent edits.",
    "Report any suspected vacuity surface explicitly.",
    "Separate source evidence from proof authority.",
    "Use the shortest answer that still identifies the root cause and patch.",
)


@dataclass(frozen=True)
class PromptProfile:
    name: str
    text: str
    source: str
    parent: str = ""
    mutation: str = ""

    @property
    def digest(self) -> str:
        return hashlib.sha256(self.text.encode("utf-8")).hexdigest()[:12]


@dataclass
class EventStats:
    profile: str
    trials: int = 0
    successes: int = 0
    api_trials: int = 0
    api_successes: int = 0
    suspect_intermediate: int = 0
    candidate_chars_total: int = 0
    warning_count: int = 0
    error_count: int = 0

    @property
    def posterior_success(self) -> float:
        # Jaynes/Laplace rule of succession with a Beta(1, 1) prior.
        return (self.successes + 1.0) / (self.trials + 2.0)

    @property
    def api_success_rate(self) -> float:
        if self.api_trials == 0:
            return 0.5
        return self.api_successes / self.api_trials

    @property
    def avg_candidate_chars(self) -> float:
        if self.api_trials == 0:
            return 0.0
        return self.candidate_chars_total / self.api_trials


@dataclass
class ScoredProfile:
    name: str
    source: str
    parent: str
    mutation: str
    digest: str
    chars: int
    required_hits: int
    forbidden_hits: int
    empirical_trials: int
    empirical_successes: int
    posterior_success: float
    jaynes_cost: float
    length_cost: float
    style_cost: float
    uncertainty_cost: float
    readback_cost: float
    fitness: float
    deployable: bool
    text_path: str = ""


def read_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def load_profiles(profiles_dir: Path) -> list[PromptProfile]:
    profiles = [PromptProfile(name="builtin", text="", source="builtin")]
    if profiles_dir.exists():
        for path in sorted(profiles_dir.glob("*.md")):
            text = path.read_text(encoding="utf-8").strip()
            profiles.append(PromptProfile(name=path.stem, text=text, source=str(path.relative_to(ROOT))))
    return profiles


def load_events(roots: list[Path]) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for root in roots:
        root = root if root.is_absolute() else ROOT / root
        if root.is_file() and root.suffix == ".json":
            paths = [root]
        elif root.is_dir():
            paths = sorted(root.rglob("*.json"))
        else:
            continue
        for path in paths:
            try:
                data = read_json(path)
            except Exception:
                continue
            if isinstance(data, dict):
                data.setdefault("_event_path", str(path))
                events.append(data)
    return events


def event_profile(event: dict[str, Any]) -> str:
    profile = event.get("prompt_profile")
    if isinstance(profile, str) and profile:
        return profile
    meta = event.get("aiclaw_result", {}).get("meta", {})
    if isinstance(meta, dict):
        profile = meta.get("prompt_profile")
        if isinstance(profile, str) and profile:
            return profile
    return "builtin"


def lean_output(event: dict[str, Any]) -> str:
    check = event.get("lean_check", {})
    if not isinstance(check, dict):
        return ""
    return "\n".join(str(check.get(key) or "") for key in ("stderr", "stdout"))


def diagnostic_counts(text: str) -> tuple[int, int]:
    errors = len(re.findall(r"\berror(?:\(|:)", text, flags=re.IGNORECASE))
    warnings = len(re.findall(r"\bwarning(?:\(|:)", text, flags=re.IGNORECASE))
    return errors, warnings


def event_response_text(event: dict[str, Any]) -> str:
    result = event.get("aiclaw_result")
    if not isinstance(result, dict):
        return ""
    content = result.get("content")
    if isinstance(content, str):
        return content
    raw = result.get("raw")
    if isinstance(raw, dict) and isinstance(raw.get("content"), str):
        return raw["content"]
    return ""


def response_contract_suspect(event: dict[str, Any]) -> bool:
    """Recompute readback-risk from archived content, not only old flags."""
    if bool(event.get("needs_readback") or event.get("response_contract_suspect")):
        return True
    text = event_response_text(event)
    if not text.strip():
        return False
    if re.search(r"\bno replacement needed\b", text, re.IGNORECASE):
        return False
    replacement_seen = re.search(r"(?im)^\s*(?:###\s*)?Replacement\s*$", text)
    if replacement_seen and "```" not in text:
        return True
    flattened_lean_marker = re.search(
        r"\b(?:lean4|lean)(?:import|open|namespace|section|noncomputable|def|theorem|lemma)\b",
        text,
    )
    return bool(flattened_lean_marker)


def event_outcome(event: dict[str, Any]) -> bool | None:
    # Prefer explicit post-patch verification fields when present.
    for key in ("verification", "post_patch_lean_check", "repair_check", "final_lean_check"):
        value = event.get(key)
        if isinstance(value, dict) and "success" in value:
            return bool(value.get("success"))
    if "outcome_success" in event:
        return bool(event.get("outcome_success"))
    return None


def collect_stats(events: list[dict[str, Any]]) -> dict[str, EventStats]:
    stats: dict[str, EventStats] = {}
    for event in events:
        profile = event_profile(event)
        item = stats.setdefault(profile, EventStats(profile=profile))

        result = event.get("aiclaw_result", {})
        if isinstance(result, dict):
            item.api_trials += 1
            if bool(result.get("success", False)):
                item.api_successes += 1
            if bool(
                result.get("suspect_intermediate")
                or event.get("suspect_intermediate")
                or response_contract_suspect(event)
            ):
                item.suspect_intermediate += 1
        item.candidate_chars_total += int(event.get("candidate_chars") or 0)

        errors, warnings = diagnostic_counts(lean_output(event))
        item.error_count += errors
        item.warning_count += warnings

        outcome = event_outcome(event)
        if outcome is not None:
            item.trials += 1
            if outcome:
                item.successes += 1
    return stats


def profile_style_counts(text: str) -> tuple[int, int]:
    lower = text.lower()
    required_hits = sum(1 for signal in REQUIRED_SIGNALS if signal in lower)
    forbidden_hits = 0
    for pattern in FORBIDDEN_PATTERNS:
        for match in pattern.finditer(text):
            prefix = text[max(0, match.start() - 16):match.start()].lower()
            if "do not " in prefix or "never " in prefix:
                continue
            forbidden_hits += 1
            break
    return required_hits, forbidden_hits


def score_profile(profile: PromptProfile, stats: EventStats, *, min_trials: int) -> ScoredProfile:
    required_hits, forbidden_hits = profile_style_counts(profile.text)
    posterior = stats.posterior_success

    # Information-geometric objective: minimize smoothed surprisal plus costs.
    jaynes_cost = -math.log(max(1e-9, posterior))
    length_cost = math.log1p(len(profile.text)) / 90.0
    missing_required = max(0, len(REQUIRED_SIGNALS) - required_hits)
    style_cost = 0.055 * missing_required + 0.7 * forbidden_hits
    uncertainty_cost = 0.28 / math.sqrt(stats.trials + 1.0)
    readback_rate = stats.suspect_intermediate / stats.api_trials if stats.api_trials else 0.0
    readback_cost = 0.25 * readback_rate
    total_cost = jaynes_cost + length_cost + style_cost + uncertainty_cost + readback_cost
    fitness = math.exp(-total_cost)
    deployable = stats.trials >= min_trials and forbidden_hits == 0

    return ScoredProfile(
        name=profile.name,
        source=profile.source,
        parent=profile.parent,
        mutation=profile.mutation,
        digest=profile.digest,
        chars=len(profile.text),
        required_hits=required_hits,
        forbidden_hits=forbidden_hits,
        empirical_trials=stats.trials,
        empirical_successes=stats.successes,
        posterior_success=posterior,
        jaynes_cost=jaynes_cost,
        length_cost=length_cost,
        style_cost=style_cost,
        uncertainty_cost=uncertainty_cost,
        readback_cost=readback_cost,
        fitness=fitness,
        deployable=deployable,
    )


def mutate_profile(parent: PromptProfile, mutation: str, index: int) -> PromptProfile:
    text = parent.text.strip()
    if text:
        text = f"{text}\n\nGEPA candidate constraint:\n- {mutation}"
    else:
        text = f"GEPA candidate constraint:\n- {mutation}"
    name = f"{parent.name}_m{index:02d}_{hashlib.sha256(mutation.encode()).hexdigest()[:6]}"
    return PromptProfile(
        name=name,
        text=text,
        source="generated",
        parent=parent.name,
        mutation=mutation,
    )


def evolve(
    profiles: list[PromptProfile],
    stats: dict[str, EventStats],
    *,
    generations: int,
    population_size: int,
    min_trials: int,
    seed: int,
) -> list[tuple[PromptProfile, ScoredProfile]]:
    rng = random.Random(seed)
    population = profiles[:population_size]
    archive: list[tuple[PromptProfile, ScoredProfile]] = []

    for _generation in range(max(1, generations)):
        scored = [
            (profile, score_profile(profile, stats.get(profile.name, EventStats(profile.name)), min_trials=min_trials))
            for profile in population
        ]
        scored.sort(key=lambda item: item[1].fitness, reverse=True)
        archive.extend(scored)

        survivors = [profile for profile, _score in scored[: max(1, population_size // 2)]]
        next_population = survivors[:]
        mutation_index = 0
        while len(next_population) < population_size:
            parent = rng.choice(survivors)
            mutation = rng.choice(MUTATIONS)
            next_population.append(mutate_profile(parent, mutation, mutation_index))
            mutation_index += 1
        population = next_population

    # Keep best score for each digest.
    by_digest: dict[str, tuple[PromptProfile, ScoredProfile]] = {}
    for profile, score in archive:
        old = by_digest.get(profile.digest)
        if old is None or score.fitness > old[1].fitness:
            by_digest[profile.digest] = (profile, score)
    return sorted(by_digest.values(), key=lambda item: item[1].fitness, reverse=True)


def archive_run(
    scored: list[tuple[PromptProfile, ScoredProfile]],
    *,
    out_dir: Path,
    run_id: str,
) -> tuple[Path, list[ScoredProfile]]:
    run_dir = out_dir / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    updated: list[ScoredProfile] = []
    manifest = run_dir / "manifest.jsonl"
    with manifest.open("w", encoding="utf-8") as handle:
        for profile, score in scored:
            text_path = run_dir / f"{score.name}_{score.digest}.md"
            text_path.write_text(profile.text + ("\n" if profile.text else ""), encoding="utf-8")
            score.text_path = str(text_path.relative_to(ROOT))
            updated.append(score)
            handle.write(json.dumps(asdict(score), sort_keys=True) + "\n")
    return run_dir, updated


def render_report(
    *,
    run_id: str,
    archive_roots: list[Path],
    event_count: int,
    scored: list[ScoredProfile],
    baseline: ScoredProfile | None,
    recommendation: str,
) -> str:
    lines = [
        "# Socratic Oracle Prompt GEPA Report",
        "",
        f"Run: `{run_id}`",
        f"Generated: `{datetime.now(timezone.utc).isoformat()}`",
        f"Events loaded: `{event_count}`",
        f"Archive roots: `{', '.join(str(p) for p in archive_roots)}`",
        f"Recommendation: `{recommendation}`",
        "",
        "## Metric",
        "",
        "Fitness is `exp(-cost)`, where cost is smoothed Jaynes surprisal plus prompt length,",
        "style regression, uncertainty, and readback penalties. Empirical proof-repair outcomes",
        "dominate only after archived verification results exist for a profile.",
        "",
        "## Top Candidates",
        "",
        "| Rank | Profile | Fitness | Trials | Successes | Deployable | Text |",
        "|------|---------|---------|--------|-----------|------------|------|",
    ]
    for rank, score in enumerate(scored[:12], 1):
        lines.append(
            f"| {rank} | `{score.name}` | {score.fitness:.4f} | "
            f"{score.empirical_trials} | {score.empirical_successes} | "
            f"{score.deployable} | `{score.text_path}` |"
        )
    if baseline is not None:
        lines.extend([
            "",
            "## Baseline",
            "",
            f"`{baseline.name}` fitness `{baseline.fitness:.4f}`, "
            f"trials `{baseline.empirical_trials}`, successes `{baseline.empirical_successes}`.",
        ])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profiles-dir", type=Path, default=DEFAULT_PROFILES_DIR)
    parser.add_argument("--archive", action="append", type=Path, default=[],
                        help="JSON file or directory containing oracle event reports. May repeat.")
    parser.add_argument("--generations", type=int, default=2)
    parser.add_argument("--population", type=int, default=8)
    parser.add_argument("--min-trials", type=int, default=3)
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_ARCHIVE_DIR)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--md-out", type=Path)
    args = parser.parse_args()

    archive_roots = args.archive or [Path("artifacts/oracle"), Path("quarantine/oracle_prompt_gepa/events")]
    profiles = load_profiles(args.profiles_dir if args.profiles_dir.is_absolute() else ROOT / args.profiles_dir)
    events = load_events(archive_roots)
    stats = collect_stats(events)
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + f"_{int(time.time())}"

    evolved = evolve(
        profiles,
        stats,
        generations=args.generations,
        population_size=args.population,
        min_trials=args.min_trials,
        seed=args.seed,
    )
    out_dir = args.out_dir if args.out_dir.is_absolute() else ROOT / args.out_dir
    run_dir, scored = archive_run(evolved, out_dir=out_dir, run_id=run_id)

    baseline = next((score for score in scored if score.name == "builtin"), None)
    best = scored[0] if scored else None
    recommendation = "keep_builtin"
    if best and baseline and best.deployable and best.fitness > baseline.fitness:
        recommendation = f"candidate_deployable:{best.name}"
    elif best and best.deployable and baseline is None:
        recommendation = f"candidate_deployable:{best.name}"

    payload = {
        "run_id": run_id,
        "run_dir": str(run_dir.relative_to(ROOT)),
        "events_loaded": len(events),
        "profiles_loaded": len(profiles),
        "min_trials": args.min_trials,
        "recommendation": recommendation,
        "baseline": asdict(baseline) if baseline else None,
        "best": asdict(best) if best else None,
        "scores": [asdict(score) for score in scored],
    }

    json_out = args.json_out if args.json_out else run_dir / "report.json"
    md_out = args.md_out if args.md_out else run_dir / "report.md"
    json_out = json_out if json_out.is_absolute() else ROOT / json_out
    md_out = md_out if md_out.is_absolute() else ROOT / md_out
    write_json(json_out, payload)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(
        render_report(
            run_id=run_id,
            archive_roots=archive_roots,
            event_count=len(events),
            scored=scored,
            baseline=baseline,
            recommendation=recommendation,
        ),
        encoding="utf-8",
    )

    print(json.dumps({
        "recommendation": recommendation,
        "events_loaded": len(events),
        "best": asdict(best) if best else None,
        "json_out": str(json_out.relative_to(ROOT)),
        "md_out": str(md_out.relative_to(ROOT)),
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
