#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from tools.infra.hermes_vibe_coding_agent import LeanstralConfig, propose, sanitize_candidate
from tools.infra.lean_interact_wrapper_local import apply_tactic

SCHEMA = "hermes_leanstral_autoproof_loop.v1"


@dataclass(frozen=True)
class ProofPrompt:
    kind: str
    goal: str
    imports: list[str]
    context: str
    prior_candidate: str = ""
    lean_feedback: str = ""

    def as_task(self) -> str:
        if self.kind == "initial":
            return self.goal
        feedback = self.lean_feedback.strip() or "Lean rejected the previous candidate."
        prior = self.prior_candidate.strip() or "<empty>"
        return (
            f"{self.goal}\n\n"
            "The previous Lean tactic candidate failed.\n"
            f"Previous candidate:\n{prior}\n\n"
            f"Lean feedback:\n{feedback}\n\n"
            "Return a corrected single Lean tactic candidate."
        )


LeanChecker = Callable[..., dict]
Proposer = Callable[[ProofPrompt], dict[str, object]]


def _lean_feedback(lean_result: dict[str, object], *, limit: int = 6000) -> str:
    lean = lean_result.get("lean") if isinstance(lean_result, dict) else None
    if not isinstance(lean, dict):
        return json.dumps(lean_result, ensure_ascii=False, sort_keys=True)[:limit]
    text = "\n".join(
        str(lean.get(key, "")) for key in ("stdout", "stderr", "error") if lean.get(key)
    ).strip()
    return text[:limit]


def error_signature(feedback: str) -> str:
    """Stable compact Lean-error signature for recurrence/deadend memory."""
    text = feedback.strip()
    if not text:
        return ""
    lowered = text.lower()
    classes = [
        ("unknown identifier", "unknown_identifier"),
        ("unknown constant", "unknown_constant"),
        ("failed to synthesize", "failed_to_synthesize"),
        ("type mismatch", "type_mismatch"),
        ("unsolved goals", "unsolved_goals"),
        ("unknown tactic", "unknown_tactic"),
        ("invalid", "invalid"),
    ]
    for needle, label in classes:
        if needle in lowered:
            return f"lean_error:{label}"
    normalized = re.sub(r"\s+", " ", lowered)[:300]
    digest = hashlib.sha256(normalized.encode("utf-8")).hexdigest()[:16]
    return f"lean_error:{digest}"


def recommended_next_bee(signature: str) -> str:
    if any(marker in signature for marker in ("unknown_identifier", "unknown_constant", "failed_to_synthesize")):
        return "RetrieverBee"
    if any(marker in signature for marker in ("type_mismatch", "unsolved_goals")):
        return "SocratesBee"
    return "PauliBee"


def build_autoproof_trace(
    *,
    goal: str,
    imports: list[str],
    context: str,
    max_iterations: int,
    status: str,
    emitted_packet_kind: str,
    attempts: list[dict[str, object]],
) -> dict[str, object]:
    last_error = ""
    failed = [attempt for attempt in attempts if not attempt.get("lean_result", {}).get("accepted")]
    if failed:
        last_error = str(failed[-1].get("error_signature", ""))
    return {
        "kind": "AutoproofTracePacket",
        "authority": "proposal",
        "promotion_allowed": False,
        "target": {"goal": goal.strip(), "imports": imports, "context_present": bool(context.strip())},
        "budgets": {"max_iterations": max_iterations},
        "result": {"status": status, "emitted_packet_kind": emitted_packet_kind},
        "attempts": attempts,
        "frontier": {
            "last_error_signature": last_error,
            "next_recommended_bee": "none" if status == "verified" else recommended_next_bee(last_error),
            "new_information_needed": "none" if status == "verified" else "Pauli/Socratic/Retrieval packet before cross-task retry",
        },
    }


def make_local_leanstral_proposer(
    *,
    config: LeanstralConfig | None = None,
) -> Proposer:
    def local_proposer(prompt: ProofPrompt) -> dict[str, object]:
        return propose(
            mode="lean-tactic",
            task=prompt.as_task(),
            context=prompt.context,
            imports=prompt.imports,
            config=config,
        )

    return local_proposer


def run_autoproof(
    *,
    goal: str,
    imports: list[str] | None = None,
    context: str = "",
    max_iterations: int = 3,
    lean_timeout: int = 60,
    proposer: Proposer | None = None,
    lean_checker: LeanChecker = apply_tactic,
) -> dict[str, object]:
    imports = imports or ["Mathlib"]
    proposer = proposer or make_local_leanstral_proposer()
    iterations: list[dict[str, object]] = []
    trace_attempts: list[dict[str, object]] = []
    prior_candidate = ""
    feedback = ""
    last_signature = ""
    verified_tactic: str | None = None

    for idx in range(max(0, max_iterations)):
        prompt = ProofPrompt(
            kind="initial" if idx == 0 else "repair",
            goal=goal.strip(),
            imports=imports,
            context=context,
            prior_candidate=prior_candidate,
            lean_feedback=feedback,
        )
        proposal = proposer(prompt)
        candidate = sanitize_candidate(str(proposal.get("candidate", "")))
        if not candidate:
            sig = error_signature(str(proposal.get("error") or "empty candidate"))
            changed_strategy = bool(last_signature and sig == last_signature)
            iteration = {
                "iteration": idx + 1,
                "prompt_kind": prompt.kind,
                "proposal_status": proposal.get("status", "empty"),
                "candidate": "",
                "lean_status": "not_run",
                "lean_ok": False,
                "error": proposal.get("error") or "empty candidate",
                "error_signature": sig,
            }
            iterations.append(iteration)
            trace_attempts.append(
                {
                    "attempt_index": idx + 1,
                    "mode": "tactic" if idx == 0 else "repair",
                    "goal_before": goal.strip(),
                    "goal_after": "",
                    "candidate_text": "",
                    "lean_result": {"accepted": False, "status": "not_run", "feedback": str(iteration["error"])},
                    "error_signature": sig,
                    "strategy": "changed_strategy_after_repeated_error" if changed_strategy else ("initial_tactic" if idx == 0 else "lean_feedback_repair"),
                    "changed_strategy": changed_strategy,
                    "retrieved_lemmas": [],
                }
            )
            prior_candidate = ""
            feedback = str(iteration["error"])
            last_signature = sig
            continue

        lean_result = lean_checker(
            goal.strip(),
            candidate,
            imports=imports,
            context=context,
            timeout=lean_timeout,
        )
        lean_ok = bool(
            isinstance(lean_result, dict)
            and lean_result.get("status") == "success"
            and isinstance(lean_result.get("lean"), dict)
            and lean_result["lean"].get("ok") is True
        )
        lean_feedback = _lean_feedback(lean_result)
        sig = "" if lean_ok else error_signature(lean_feedback)
        changed_strategy = bool(sig and last_signature and sig == last_signature)
        iteration = {
            "iteration": idx + 1,
            "prompt_kind": prompt.kind,
            "proposal_status": proposal.get("status"),
            "candidate": candidate,
            "raw_candidate": proposal.get("raw_candidate", ""),
            "lean_status": lean_result.get("status") if isinstance(lean_result, dict) else "error",
            "lean_ok": lean_ok,
            "lean_feedback": lean_feedback,
            "error_signature": sig,
            "strategy": "changed_strategy_after_repeated_error" if changed_strategy else ("initial_tactic" if idx == 0 else "lean_feedback_repair"),
            "changed_strategy": changed_strategy,
        }
        iterations.append(iteration)
        trace_attempts.append(
            {
                "attempt_index": idx + 1,
                "mode": "tactic" if idx == 0 else "repair",
                "goal_before": goal.strip(),
                "goal_after": "proof_finished" if lean_ok else "",
                "candidate_text": candidate,
                "lean_result": {
                    "accepted": lean_ok,
                    "status": iteration["lean_status"],
                    "feedback": lean_feedback,
                },
                "error_signature": sig,
                "strategy": iteration["strategy"],
                "changed_strategy": changed_strategy,
                "retrieved_lemmas": [],
            }
        )
        if lean_ok:
            verified_tactic = candidate
            break
        prior_candidate = candidate
        feedback = str(iteration["lean_feedback"])
        last_signature = sig

    status = "verified" if verified_tactic else "failed"
    emitted_packet_kind = "TheoremCandidatePacket" if verified_tactic else "ResiduePacket"
    autoproof_trace = build_autoproof_trace(
        goal=goal,
        imports=imports,
        context=context,
        max_iterations=max_iterations,
        status=status,
        emitted_packet_kind=emitted_packet_kind,
        attempts=trace_attempts,
    )
    return {
        "schema": SCHEMA,
        "status": status,
        "authority": "proposal_with_lean_evidence",
        "promotion_allowed": False,
        "goal": goal.strip(),
        "imports": imports,
        "context": context,
        "max_iterations": max_iterations,
        "verified_tactic": verified_tactic,
        "iterations": iterations,
        "autoproof_trace": autoproof_trace,
    }


def parse_imports(values: list[str]) -> list[str]:
    imports: list[str] = []
    for value in values:
        for item in value.split(","):
            item = item.strip()
            if item:
                imports.append(item)
    return imports or ["Mathlib"]


def _fake_proposer_from_candidates(path: Path) -> Proposer:
    candidates = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(candidates, list):
        raise ValueError("fake candidates must be a JSON list")
    iterator = iter(candidates)

    def fake(prompt: ProofPrompt) -> dict[str, object]:
        try:
            candidate = next(iterator)
        except StopIteration:
            candidate = ""
        return {"status": "ok" if candidate else "empty", "candidate": candidate, "raw_candidate": candidate}

    return fake


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Bounded native Hermes loop: local Leanstral proposal -> Lean check -> repair."
    )
    parser.add_argument("--goal", required=True)
    parser.add_argument("--context", default="")
    parser.add_argument("--context-file", default=None)
    parser.add_argument("--import", dest="imports", action="append", default=[])
    parser.add_argument("--max-iterations", type=int, default=3)
    parser.add_argument("--lean-timeout", type=int, default=60)
    parser.add_argument("--endpoint", default="http://127.0.0.1:18889/v1")
    parser.add_argument("--model", default="leanstral-gguf")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--max-tokens", type=int, default=512)
    parser.add_argument("--temperature", type=float, default=0.0)
    parser.add_argument("--fake-candidates", default=None, help="Testing hook: JSON list of candidate tactics.")
    return parser


def main(argv: list[str] | None = None, *, lean_checker: LeanChecker = apply_tactic) -> int:
    args = build_arg_parser().parse_args(sys.argv[1:] if argv is None else argv)
    context = args.context
    if args.context_file:
        context = Path(args.context_file).read_text(encoding="utf-8")
    if args.fake_candidates:
        proposer = _fake_proposer_from_candidates(Path(args.fake_candidates))
    else:
        proposer = make_local_leanstral_proposer(
            config=LeanstralConfig(
                endpoint=args.endpoint,
                model=args.model,
                timeout=args.timeout,
                max_tokens=args.max_tokens,
                temperature=args.temperature,
            )
        )
    payload = run_autoproof(
        goal=args.goal,
        imports=parse_imports(args.imports),
        context=context,
        max_iterations=args.max_iterations,
        lean_timeout=args.lean_timeout,
        proposer=proposer,
        lean_checker=lean_checker,
    )
    print(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False))
    return 0 if payload["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
