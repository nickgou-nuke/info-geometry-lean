#!/usr/bin/env python3
"""Closed-loop repo research controller.

Implements a practical planner -> retriever -> reader -> critic -> memory loop
using existing repository tooling. This is intentionally operational and
stateful: each iteration records what was attempted, what evidence was produced,
and what remains unresolved.

Design goals:
- no UI coupling; JSON state is the source of truth
- strict gating (artifact presence, extraction quality, vacuity status)
- incremental convergence with explicit uncertainty tracking
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def slugify(text: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return cleaned[:64] or "research-goal"


@dataclass
class CommandResult:
    cmd: list[str]
    exit_code: int
    ok: bool
    duration_sec: float
    stdout_tail: str
    stderr_tail: str


@dataclass
class Metrics:
    keyword: dict[str, Any] = field(default_factory=dict)
    deep_search: dict[str, Any] = field(default_factory=dict)
    significance: dict[str, Any] = field(default_factory=dict)


@dataclass
class Verdict:
    confidence: float
    blockers: list[str]
    uncertainties: list[str]
    findings: list[str]
    open_questions: list[str]
    done: bool


@dataclass
class Iteration:
    iteration: int
    timestamp: str
    selected_subtask: str
    actions: list[dict[str, Any]]
    command_results: list[CommandResult]
    metrics: Metrics
    verdict: Verdict


def run_cmd(cmd: list[str], cwd: Path, timeout_sec: int) -> CommandResult:
    start = datetime.now(timezone.utc)
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            text=True,
            capture_output=True,
            timeout=timeout_sec,
            check=False,
        )
        end = datetime.now(timezone.utc)
        return CommandResult(
            cmd=cmd,
            exit_code=proc.returncode,
            ok=(proc.returncode == 0),
            duration_sec=(end - start).total_seconds(),
            stdout_tail=proc.stdout[-4000:],
            stderr_tail=proc.stderr[-4000:],
        )
    except subprocess.TimeoutExpired as ex:
        end = datetime.now(timezone.utc)
        return CommandResult(
            cmd=cmd,
            exit_code=124,
            ok=False,
            duration_sec=(end - start).total_seconds(),
            stdout_tail=(ex.stdout or "")[-4000:] if isinstance(ex.stdout, str) else "",
            stderr_tail=(ex.stderr or "")[-4000:] if isinstance(ex.stderr, str) else "",
        )


def load_json(path: Path) -> Any | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def file_age_hours(path: Path) -> float | None:
    if not path.exists():
        return None
    mtime = datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc)
    return (datetime.now(timezone.utc) - mtime).total_seconds() / 3600.0


def coerce_count(value: Any) -> int:
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, (int, float)):
        return int(value)
    if isinstance(value, list):
        return len(value)
    if isinstance(value, dict):
        return len(value)
    if value is None:
        return 0
    try:
        return int(value)
    except Exception:
        return 0


def needs_refresh(path: Path, policy: str, max_age_hours: float) -> bool:
    if policy == "always":
        return True
    if policy == "never":
        return False
    if not path.exists():
        return True
    if policy == "missing":
        return False
    age = file_age_hours(path)
    if age is None:
        return True
    return age > max_age_hours


def read_keyword_metrics(path: Path) -> dict[str, Any]:
    payload = load_json(path)
    if not isinstance(payload, dict):
        return {"present": False}

    term_index = payload.get("termIndex", [])
    top_terms: list[str] = []
    if isinstance(term_index, list):
        for row in term_index[:12]:
            if isinstance(row, dict) and isinstance(row.get("term"), str):
                top_terms.append(row["term"])

    return {
        "present": True,
        "path": str(path),
        "indexedLeanFiles": coerce_count(payload.get("indexedLeanFiles", 0)),
        "termCount": len(term_index) if isinstance(term_index, list) else 0,
        "topTerms": top_terms,
        "generatedAt": payload.get("generatedAt"),
        "gitHead": payload.get("gitHead"),
        "ageHours": file_age_hours(path),
    }


def read_deep_search_metrics(path: Path) -> dict[str, Any]:
    payload = load_json(path)
    if not isinstance(payload, dict):
        return {"present": False}

    terms = payload.get("characteristicTerms", [])
    if not isinstance(terms, list):
        terms = []

    decl_total = 0
    kind_counts: dict[str, int] = {}
    top_terms: list[str] = []

    for row in terms:
        if not isinstance(row, dict):
            continue
        if isinstance(row.get("term"), str) and len(top_terms) < 12:
            top_terms.append(row["term"])
        decl_total += int(row.get("declarationCount", 0) or 0)
        kc = row.get("kindCounts", {})
        if isinstance(kc, dict):
            for k, v in kc.items():
                try:
                    kind_counts[k] = kind_counts.get(k, 0) + int(v)
                except Exception:
                    continue

    return {
        "present": True,
        "path": str(path),
        "profile": payload.get("profile"),
        "characteristicTermCount": len(terms),
        "declarationBlocks": coerce_count(payload.get("declarationBlocks", 0)),
        "declarationHitsTotal": decl_total,
        "kindCounts": kind_counts,
        "topTerms": top_terms,
        "generatedAt": payload.get("generatedAt"),
        "gitHead": payload.get("gitHead"),
        "ageHours": file_age_hours(path),
    }


def read_significance_metrics(path: Path) -> dict[str, Any]:
    payload = load_json(path)
    if not isinstance(payload, list):
        return {"present": False}

    by_level: dict[str, int] = {}
    by_code: dict[str, int] = {}
    with_violations = 0
    for row in payload:
        if not isinstance(row, dict):
            continue
        violations = row.get("violations", [])
        if not isinstance(violations, list) or not violations:
            continue
        with_violations += 1
        for v in violations:
            if not isinstance(v, dict):
                continue
            lvl = str(v.get("level", "unknown"))
            code = str(v.get("code", "unknown"))
            by_level[lvl] = by_level.get(lvl, 0) + 1
            by_code[code] = by_code.get(code, 0) + 1

    top_codes = sorted(by_code.items(), key=lambda kv: kv[1], reverse=True)[:12]
    return {
        "present": True,
        "path": str(path),
        "declarationCount": len(payload),
        "declarationsWithViolations": with_violations,
        "violationsByLevel": by_level,
        "topViolationCodes": top_codes,
        "generatedAt": None,
        "gitHead": None,
        "ageHours": file_age_hours(path),
    }


def collect_metrics(keyword_path: Path, deep_path: Path, sig_path: Path, include_sig: bool) -> Metrics:
    return Metrics(
        keyword=read_keyword_metrics(keyword_path),
        deep_search=read_deep_search_metrics(deep_path),
        significance=read_significance_metrics(sig_path) if include_sig else {"present": False},
    )


def evaluate(metrics: Metrics, confidence_threshold: float, include_sig: bool) -> Verdict:
    blockers: list[str] = []
    uncertainties: list[str] = []
    findings: list[str] = []
    open_questions: list[str] = []

    confidence = 0.0

    k = metrics.keyword
    d = metrics.deep_search
    s = metrics.significance

    if k.get("present"):
        confidence += 0.25
        findings.append(f"Keyword index loaded ({k.get('termCount', 0)} terms).")
    else:
        blockers.append("Keyword index artifact missing or invalid.")
        open_questions.append("refresh_keywords")

    if d.get("present"):
        confidence += 0.30
        hits = int(d.get("declarationHitsTotal", 0) or 0)
        terms = int(d.get("characteristicTermCount", 0) or 0)
        findings.append(
            f"Deep declaration search loaded ({terms} characteristic terms, {hits} declaration hits)."
        )
        if terms < 8:
            uncertainties.append("Characteristic-term surface is thin (<8 terms).")
            open_questions.append("expand_deep_search")
        if hits < 80:
            uncertainties.append("Declaration-hit coverage is low (<80).")
            open_questions.append("expand_deep_search")
        else:
            confidence += 0.15
    else:
        blockers.append("Deep-search artifact missing or invalid.")
        open_questions.append("refresh_deep_search")

    if include_sig:
        if s.get("present"):
            confidence += 0.20
            by_level = s.get("violationsByLevel", {})
            if isinstance(by_level, dict):
                errs = int(by_level.get("error", 0) or 0)
                warns = int(by_level.get("warning", 0) or 0)
                if errs > 0:
                    uncertainties.append(f"Vacuity gate has {errs} error-level violations.")
                    open_questions.append("resolve_vacuity_errors")
                    confidence -= min(0.25, errs / 200.0)
                if warns > 0:
                    findings.append(f"Vacuity warnings present ({warns}).")
                v0 = 0
                for code, count in s.get("topViolationCodes", []):
                    if code == "V0/syntactic-vacuity":
                        v0 = int(count)
                        break
                if v0 > 0:
                    uncertainties.append(f"Syntactic vacuity signal present (V0={v0}).")
                    confidence -= min(0.12, v0 / 120.0)
        else:
            blockers.append("Theorem-significance artifact missing or invalid.")
            open_questions.append("refresh_significance")

    if k.get("present") and d.get("present"):
        terms = int(k.get("termCount", 0) or 0)
        cterms = int(d.get("characteristicTermCount", 0) or 0)
        if terms > 0 and cterms == 0:
            uncertainties.append("Lexical index exists but characteristic term selection is empty.")
            open_questions.append("refresh_deep_search")

    # Deduplicate while preserving order.
    open_seen = set()
    open_unique = []
    for q in open_questions:
        if q not in open_seen:
            open_seen.add(q)
            open_unique.append(q)

    conf = max(0.0, min(1.0, confidence))
    done = (conf >= confidence_threshold) and (len(blockers) == 0) and (len(open_unique) == 0)

    return Verdict(
        confidence=conf,
        blockers=blockers,
        uncertainties=uncertainties,
        findings=findings,
        open_questions=open_unique,
        done=done,
    )


def select_subtask(verdict: Verdict) -> str:
    if verdict.open_questions:
        return verdict.open_questions[0]
    return "synthesize"


def build_actions(
    subtask: str,
    root: Path,
    profile: str,
    sig_json: Path,
    run_vacuity_gate: bool,
) -> list[dict[str, Any]]:
    sig_md = sig_json.with_suffix(".md")
    if subtask == "refresh_keywords":
        return [{"label": "keyword_index", "cmd": ["python3", "tools/infra/generate_keyword_research_report.py"]}]
    if subtask in {"refresh_deep_search", "expand_deep_search"}:
        cmd = ["python3", "tools/infra/generate_repo_story_from_keyword_index.py", "--profile", profile]
        if subtask == "expand_deep_search":
            cmd.extend(["--term-count", "40", "--max-decls-per-term", "80"])
        return [{"label": "deep_search_story", "cmd": cmd}]
    if subtask in {"refresh_significance", "resolve_vacuity_errors"}:
        actions = [
            {
                "label": "theorem_significance",
                "cmd": [
                    "python3",
                    "tools/theorem_significance.py",
                    "--out",
                    str(sig_json.relative_to(root)),
                    "--md",
                    str(sig_md.relative_to(root)),
                ],
            }
        ]
        if run_vacuity_gate:
            actions.append(
                {
                    "label": "vacuity_gate",
                    "cmd": [
                        "python3",
                        "tools/check_vacuity_policy.py",
                        str(sig_json.relative_to(root)),
                    ],
                }
            )
        return actions
    return []


def write_state(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--goal", required=True, help="Research goal statement.")
    p.add_argument(
        "--profile",
        choices=["balanced", "physics", "methodology"],
        default="balanced",
        help="Characteristic-term profile for deep search.",
    )
    p.add_argument("--max-iterations", type=int, default=4)
    p.add_argument("--confidence-threshold", type=float, default=0.78)
    p.add_argument(
        "--refresh-policy",
        choices=["missing", "stale", "always", "never"],
        default="missing",
        help="When to run retrieval actions for artifacts.",
    )
    p.add_argument("--max-artifact-age-hours", type=float, default=24.0)
    p.add_argument("--timeout-sec", type=int, default=1800)
    p.add_argument("--include-significance", action="store_true", help="Include theorem-significance/vacuity lane.")
    p.add_argument("--run-vacuity-gate", action="store_true", help="Run Layer-C vacuity policy gate after significance generation.")
    p.add_argument(
        "--keyword-json",
        default="reports/keywords/lean_keyword_research_report.json",
        help="Keyword index JSON artifact path.",
    )
    p.add_argument(
        "--deep-json",
        default="reports/keywords/characteristic_term_deep_search.json",
        help="Characteristic-term deep-search JSON artifact path.",
    )
    p.add_argument(
        "--significance-json",
        default="reports/theorem-significance-current.json",
        help="Theorem-significance JSON artifact path.",
    )
    p.add_argument(
        "--state-out",
        default="",
        help="Output path for controller state JSON (default: reports/research/controller-state-<timestamp>-<slug>.json).",
    )
    return p.parse_args()


def main() -> None:
    args = parse_args()
    root = Path(__file__).resolve().parents[2]
    keyword_json = root / args.keyword_json
    deep_json = root / args.deep_json
    sig_json = root / args.significance_json

    timestamp_slug = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    default_state = root / "reports" / "research" / f"controller-state-{timestamp_slug}-{slugify(args.goal)}.json"
    state_path = Path(args.state_out).resolve() if args.state_out else default_state

    run_meta: dict[str, Any] = {
        "generatedAt": utc_now(),
        "goal": args.goal,
        "profile": args.profile,
        "maxIterations": args.max_iterations,
        "confidenceThreshold": args.confidence_threshold,
        "refreshPolicy": args.refresh_policy,
        "maxArtifactAgeHours": args.max_artifact_age_hours,
        "includeSignificance": args.include_significance,
        "runVacuityGate": args.run_vacuity_gate,
        "artifacts": {
            "keyword": str(keyword_json.relative_to(root)),
            "deepSearch": str(deep_json.relative_to(root)),
            "significance": str(sig_json.relative_to(root)),
        },
    }

    iterations: list[Iteration] = []
    verdict = evaluate(
        collect_metrics(keyword_json, deep_json, sig_json, args.include_significance),
        args.confidence_threshold,
        args.include_significance,
    )

    for i in range(1, args.max_iterations + 1):
        subtask = select_subtask(verdict)
        actions = build_actions(
            subtask=subtask,
            root=root,
            profile=args.profile,
            sig_json=sig_json,
            run_vacuity_gate=args.run_vacuity_gate,
        )

        command_results: list[CommandResult] = []
        for action in actions:
            cmd = action["cmd"]
            out_path = None
            if action["label"] == "keyword_index":
                out_path = keyword_json
            elif action["label"] == "deep_search_story":
                out_path = deep_json
            elif action["label"] in {"theorem_significance", "vacuity_gate"}:
                out_path = sig_json

            should_run = True
            if out_path is not None:
                should_run = needs_refresh(out_path, args.refresh_policy, args.max_artifact_age_hours)
            if should_run:
                command_results.append(run_cmd(cmd, cwd=root, timeout_sec=args.timeout_sec))
            else:
                command_results.append(
                    CommandResult(
                        cmd=cmd,
                        exit_code=0,
                        ok=True,
                        duration_sec=0.0,
                        stdout_tail=f"Skipped by refresh policy '{args.refresh_policy}'.",
                        stderr_tail="",
                    )
                )

        metrics = collect_metrics(keyword_json, deep_json, sig_json, args.include_significance)
        verdict = evaluate(metrics, args.confidence_threshold, args.include_significance)

        iterations.append(
            Iteration(
                iteration=i,
                timestamp=utc_now(),
                selected_subtask=subtask,
                actions=actions,
                command_results=command_results,
                metrics=metrics,
                verdict=verdict,
            )
        )

        if verdict.done:
            break
        # If no actions are available for the selected subtask, stop to avoid spin.
        if not actions:
            break

    final_payload = {
        "run": run_meta,
        "iterations": [
            {
                **asdict(it),
                "command_results": [asdict(r) for r in it.command_results],
                "metrics": asdict(it.metrics),
                "verdict": asdict(it.verdict),
            }
            for it in iterations
        ],
        "finalVerdict": asdict(verdict),
        "completedAt": utc_now(),
    }
    write_state(state_path, final_payload)

    print(f"[research-controller] state written: {state_path}")
    print(f"[research-controller] confidence={verdict.confidence:.3f} done={verdict.done}")
    if verdict.blockers:
        print("[research-controller] blockers:")
        for b in verdict.blockers:
            print(f"  - {b}")
    if verdict.open_questions:
        print("[research-controller] open questions:")
        for q in verdict.open_questions:
            print(f"  - {q}")

    sys.exit(0 if verdict.done else 2)


if __name__ == "__main__":
    main()
