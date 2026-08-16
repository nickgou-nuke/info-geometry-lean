#!/usr/bin/env python3
"""GEPA observer for agent-generated model/oracle messages.

This reads the append-only agent message ledger plus selected legacy prompt
artifacts and produces empirical review evidence:

- normalized message observations;
- thermodynamic score over message outcomes;
- provider/model/channel/failure summaries;
- review-only recommendations for prompt/SOP mutation.

It observes communications. It does not edit Archon workflows, canonical SOPs,
Lean source, or skills.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

from tools.infra.thermodynamic_scoring import DEFAULT_HEURISTIC_WEIGHT, score_outcomes


@dataclass
class MessageObservation:
    source_kind: str
    source_path: str
    event_id: str
    ts: str = ""
    source_tool: str = ""
    channel: str = ""
    direction: str = ""
    provider: str = ""
    model: str = ""
    platform: str = ""
    prompt_sha256: str = ""
    prompt_chars: int = 0
    response_sha256: str = ""
    response_chars: int = 0
    success: bool | None = None
    latency_ms: float = 0.0
    failure_pattern: str = ""
    metadata: dict[str, Any] = field(default_factory=dict)

    def outcome(self) -> dict[str, Any]:
        succeeded = bool(self.success)
        return {
            "status": "completed" if succeeded else "failed",
            "succeeded": succeeded,
            "attempts": 1,
            "metabolic_cost_ms": max(0.0, float(self.latency_ms or 0.0)),
            "error_summary": self.failure_pattern,
            "failure_pattern": self.failure_pattern or ("ok" if succeeded else "unknown_message_outcome"),
        }


def _repo_rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(_REPO))
    except ValueError:
        return str(path)


def _hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()


def _source_hash(path: Path) -> str:
    try:
        return _hash_text(path.read_text(encoding="utf-8", errors="replace"))[:16]
    except OSError:
        return ""


def _utc_tag() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _read_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return []
    rows: list[dict[str, Any]] = []
    for line in lines:
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            rows.append(value)
    return rows


def _bool_or_none(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    return None


def _failure_pattern(event: dict[str, Any]) -> str:
    if bool(event.get("success")):
        return ""
    metadata = event.get("metadata")
    if isinstance(metadata, dict):
        queue = metadata.get("queue")
        if isinstance(queue, dict):
            if queue.get("queue_state") == "needs_readback" or queue.get("readback_required") or queue.get("held"):
                return "oracle_needs_readback"
            hold_reason = queue.get("hold_reason")
            if isinstance(hold_reason, str) and hold_reason.strip():
                return hold_reason.strip()[:160]
        for key in ("failure_pattern", "error", "error_summary", "hold_reason"):
            value = metadata.get(key)
            if isinstance(value, str) and value.strip():
                lowered = value.lower()
                if "needs_readback" in lowered or "readback" in lowered:
                    return "oracle_needs_readback"
                if "lane" in lowered and "busy" in lowered:
                    return "oracle_lane_busy"
                return value.strip()[:160]
    response = str(event.get("response_text") or "")
    if "ORACLE UNAVAILABLE" in response:
        return "oracle_unavailable"
    if "ORACLE ERROR" in response:
        return "oracle_error"
    if "CHATGPT ORACLE BUSY" in response:
        return "oracle_lane_busy"
    if "NEEDS READBACK" in response:
        return "suspect_intermediate_readback"
    if event.get("prompt_sensitive_matches"):
        return "sensitive_prompt_guard"
    return "unknown_message_outcome"


def observe_ledger_file(path: Path) -> list[MessageObservation]:
    observations: list[MessageObservation] = []
    for event in _read_jsonl(path):
        prompt_chars = int(event.get("prompt_chars") or 0)
        response_chars = int(event.get("response_chars") or 0)
        observations.append(MessageObservation(
            source_kind="agent_message_ledger",
            source_path=_repo_rel(path),
            event_id=str(event.get("event_id") or event.get("prompt_sha256") or _source_hash(path)),
            ts=str(event.get("ts", "")),
            source_tool=str(event.get("source_tool", "")),
            channel=str(event.get("channel", "")),
            direction=str(event.get("direction", "")),
            provider=str(event.get("provider", "")),
            model=str(event.get("model", "")),
            platform=str(event.get("platform", "")),
            prompt_sha256=str(event.get("prompt_sha256", "")),
            prompt_chars=prompt_chars,
            response_sha256=str(event.get("response_sha256", "")),
            response_chars=response_chars,
            success=_bool_or_none(event.get("success")),
            latency_ms=float(event.get("latency_ms") or 0.0),
            failure_pattern=_failure_pattern(event),
            metadata=event.get("metadata") if isinstance(event.get("metadata"), dict) else {},
        ))
    return observations


PROMPT_FILE_RE = re.compile(r"(prompt|query|message|oracle|socratic|gemini|chatgpt|codex)", re.IGNORECASE)


def observe_legacy_prompt_file(path: Path) -> MessageObservation | None:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    if not text.strip():
        return None
    lower = path.name.lower()
    provider = ""
    if "gemini" in lower:
        provider = "gemini"
    elif "chatgpt" in lower:
        provider = "chatgpt"
    elif "codex" in lower:
        provider = "codex"
    elif "oracle" in lower:
        provider = "oracle"
    elif "socratic" in str(path).lower():
        provider = "socratic"
    return MessageObservation(
        source_kind="legacy_prompt_artifact",
        source_path=_repo_rel(path),
        event_id=_source_hash(path),
        source_tool="legacy_artifact_scan",
        channel="legacy_prompt_artifact",
        direction="agent_to_model",
        provider=provider,
        prompt_sha256=_hash_text(text),
        prompt_chars=len(text),
        success=None,
        failure_pattern="unscored_legacy_prompt",
        metadata={"filename": path.name},
    )


def observe_gepa_eval_cache(path: Path) -> list[MessageObservation]:
    observations: list[MessageObservation] = []
    for row in _read_jsonl(path):
        success = _bool_or_none(row.get("succeeded"))
        error = str(row.get("error") or "")
        event_id = _hash_text(json.dumps(row, sort_keys=True))[:16]
        observations.append(MessageObservation(
            source_kind="gepa_eval_cache",
            source_path=_repo_rel(path),
            event_id=event_id,
            source_tool="gepa_real_eval",
            channel="hermes_eval_cache",
            direction="model_result_to_agent",
            provider="hermes",
            prompt_sha256=str(row.get("skill_hash", "")),
            success=success,
            failure_pattern="" if success else (error[:160] or "gepa_eval_failed"),
            metadata={k: row.get(k) for k in ("file", "line", "compiled", "policy_clean", "policy_score")},
        ))
    return observations


def _recent_files(root: Path, patterns: list[str], limit: int) -> list[Path]:
    paths: list[Path] = []
    if root.exists():
        for pattern in patterns:
            paths.extend(p for p in root.rglob(pattern) if p.is_file())
    paths = sorted(set(paths), key=lambda p: p.stat().st_mtime, reverse=True)
    return paths[:limit] if limit > 0 else paths


def collect(args: argparse.Namespace) -> list[MessageObservation]:
    observations: list[MessageObservation] = []
    if args.ledger:
        for path in _recent_files(Path(args.ledger_dir), ["*.jsonl"], args.limit):
            observations.extend(observe_ledger_file(path))
    if args.gepa_cache:
        cache = _REPO / "quarantine" / "hermes_skills" / "evolved" / ".eval_cache.jsonl"
        if cache.exists():
            observations.extend(observe_gepa_eval_cache(cache))
    if args.legacy_artifacts:
        roots = [Path(p) for p in args.legacy_root]
        for root in roots:
            for path in _recent_files(root, ["*.txt", "*.md", "*.json", "*.jsonl"], args.legacy_limit):
                if PROMPT_FILE_RE.search(str(path)):
                    obs = observe_legacy_prompt_file(path)
                    if obs is not None:
                        observations.append(obs)
    observations.sort(key=lambda item: (item.ts, item.source_path, item.event_id))
    return observations


def _counter_by(observations: list[MessageObservation], attr: str) -> dict[str, int]:
    c = Counter(str(getattr(obs, attr) or "unknown") for obs in observations)
    return dict(sorted(c.items(), key=lambda item: (-item[1], item[0])))


def _success_by_key(observations: list[MessageObservation], attr: str) -> list[dict[str, Any]]:
    groups: dict[str, list[MessageObservation]] = defaultdict(list)
    for obs in observations:
        groups[str(getattr(obs, attr) or "unknown")].append(obs)
    rows = []
    for key, items in sorted(groups.items()):
        scored = [item for item in items if item.success is not None]
        successes = sum(1 for item in scored if item.success)
        rows.append({
            attr: key,
            "n": len(items),
            "scored": len(scored),
            "successes": successes,
            "success_rate": round(successes / len(scored), 6) if scored else None,
            "avg_prompt_chars": round(sum(item.prompt_chars for item in items) / len(items), 1) if items else 0.0,
        })
    rows.sort(key=lambda row: (-(row["success_rate"] or -1), -row["n"], row[attr]))
    return rows


def recommendations(observations: list[MessageObservation]) -> list[dict[str, str]]:
    failures = Counter(obs.failure_pattern for obs in observations if obs.failure_pattern)
    recs: list[dict[str, str]] = []
    if (
        failures.get("oracle_lane_busy", 0)
        or failures.get("suspect_intermediate_readback", 0)
        or failures.get("oracle_needs_readback", 0)
    ):
        recs.append({
            "review_status": "proposal_only",
            "candidate": "Require readback/release before another browser-oracle send",
            "reason": "Observed unresolved or suspect oracle lane outcomes.",
        })
    if failures.get("oracle_unavailable", 0) or failures.get("oracle_error", 0):
        recs.append({
            "review_status": "proposal_only",
            "candidate": "Add provider preflight to every external-oracle call path",
            "reason": "Observed unavailable/error oracle outcomes.",
        })
    if failures.get("sensitive_prompt_guard", 0):
        recs.append({
            "review_status": "proposal_only",
            "candidate": "Split sensitive context from oracle prompts and pass only hashes/excerpts",
            "reason": "Sensitive-looking prompt material was detected by the ledger.",
        })
    long_prompts = [obs for obs in observations if obs.prompt_chars > 20000]
    if long_prompts:
        recs.append({
            "review_status": "proposal_only",
            "candidate": "Summarize retrieved context before oracle submission",
            "reason": f"Observed {len(long_prompts)} prompt(s) over 20k characters.",
        })
    if not recs:
        recs.append({
            "review_status": "hold",
            "candidate": "Collect more communication events before mutating prompts",
            "reason": "No dominant communication failure pattern was detected.",
        })
    return recs


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def write_review(path: Path, report: dict[str, Any], recs: list[dict[str, str]]) -> None:
    score = report["thermodynamic_score"]
    lines = [
        "# GEPA Agent Message Observer Review",
        "",
        "Status: `review-only`",
        "",
        "This packet reviews what agents submitted to model/oracle/collaborator",
        "lanes and what came back. It is not SOP promotion authority.",
        "",
        "## Thermodynamic Score",
        "",
        f"- observations: `{report['observation_count']}`",
        f"- scored observations: `{report['scored_observation_count']}`",
        f"- fitness: `{score['fitness']}`",
        f"- success_rate: `{score['success_rate']}`",
        f"- temperature: `{score['temperature']}`",
        f"- free_energy: `{score['free_energy']}`",
        f"- entropy: `{score['entropy']}`",
        "",
        "## Top Failure Patterns",
        "",
    ]
    failures = report.get("failure_patterns", {})
    if failures:
        for name, count in failures.items():
            lines.append(f"- `{name}`: `{count}`")
    else:
        lines.append("- none")
    lines.extend(["", "## Candidate Prompt/Process Mutations", ""])
    for rec in recs:
        lines.append(f"- `{rec['review_status']}`: {rec['candidate']}")
        lines.append(f"  Reason: {rec['reason']}")
    lines.extend([
        "",
        "## Evidence",
        "",
        f"- observations: `{report['observations_jsonl']}`",
        f"- report: `{report['report_json']}`",
        "",
        "Promotion boundary: use this as empirical evidence only. Stable Archon",
        "workflows, commandments, and skills require explicit review/promotion.",
    ])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Observe agent-generated model/oracle messages.")
    parser.add_argument("--ledger-dir", default="artifacts/agent_messages")
    parser.add_argument("--output-dir", default="artifacts/gepa_agent_message_observer")
    parser.add_argument("--review-dir", default="quarantine/agent_message_reviews")
    parser.add_argument("--limit", type=int, default=30, help="Recent ledger files; <=0 means all")
    parser.add_argument("--legacy-root", action="append", default=["artifacts/socratic_loops", "artifacts/leantrail", "artifacts/research"])
    parser.add_argument("--legacy-limit", type=int, default=80)
    parser.add_argument("--cost-budget-ms", type=float, default=600_000.0)
    parser.add_argument("--heuristic-weight", type=float, default=DEFAULT_HEURISTIC_WEIGHT)
    parser.add_argument("--no-ledger", dest="ledger", action="store_false")
    parser.add_argument("--no-gepa-cache", dest="gepa_cache", action="store_false")
    parser.add_argument("--no-legacy-artifacts", dest="legacy_artifacts", action="store_false")
    parser.add_argument("--no-review", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.set_defaults(ledger=True, gepa_cache=True, legacy_artifacts=True)
    args = parser.parse_args()

    observations = collect(args)
    scored = [obs for obs in observations if obs.success is not None]
    thermo = score_outcomes(
        [obs.outcome() for obs in scored],
        cost_budget_ms=args.cost_budget_ms,
        heuristic_weight=args.heuristic_weight,
    )
    tag = _utc_tag()
    output_dir = Path(args.output_dir)
    review_dir = Path(args.review_dir)
    observations_jsonl = output_dir / f"{tag}_message_observations.jsonl"
    report_json = output_dir / f"{tag}_message_report.json"
    review_path = None if args.no_review else review_dir / f"{tag}_message_review.md"

    write_jsonl(observations_jsonl, (asdict(obs) for obs in observations))
    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "mode": "agent_message_observer_review_only",
        "observation_count": len(observations),
        "scored_observation_count": len(scored),
        "source_kinds": _counter_by(observations, "source_kind"),
        "channels": _counter_by(observations, "channel"),
        "providers": _counter_by(observations, "provider"),
        "models": _counter_by(observations, "model"),
        "failure_patterns": dict(Counter(obs.failure_pattern for obs in observations if obs.failure_pattern)),
        "success_by_provider": _success_by_key(observations, "provider"),
        "success_by_channel": _success_by_key(observations, "channel"),
        "thermodynamic_score": {
            "fitness": round(thermo.fitness, 6),
            "legacy_fitness": round(thermo.legacy_fitness, 6),
            "thermodynamic_fitness": round(thermo.thermodynamic_fitness, 6),
            "temperature": round(thermo.temperature, 6),
            "partition_function": round(thermo.partition_function, 6),
            "free_energy": round(thermo.free_energy, 6),
            "energy_mean": round(thermo.energy_mean, 6),
            "energy_variance": round(thermo.energy_variance, 6),
            "entropy": round(thermo.entropy, 6),
            "expected_success": round(thermo.expected_success, 6),
            "success_rate": round(thermo.success_rate, 6),
        },
        "observations_jsonl": _repo_rel(observations_jsonl),
        "report_json": _repo_rel(report_json),
        "review_packet": _repo_rel(review_path) if review_path else "",
        "authority_boundary": "communication evidence only; Lean/promotion gates remain authority",
    }
    report_json.parent.mkdir(parents=True, exist_ok=True)
    report_json.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    recs = recommendations(observations)
    if review_path is not None:
        write_review(review_path, report, recs)

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        score = report["thermodynamic_score"]
        print(f"observations: {report['observation_count']}")
        print(f"scored: {report['scored_observation_count']}")
        print(f"fitness: {score['fitness']}")
        print(f"success_rate: {score['success_rate']}")
        print(f"observations_jsonl: {report['observations_jsonl']}")
        print(f"report_json: {report['report_json']}")
        if review_path is not None:
            print(f"review_packet: {report['review_packet']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
