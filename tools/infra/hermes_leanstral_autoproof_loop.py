#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from tools.infra.hermes_vibe_coding_agent import LeanstralConfig, propose, sanitize_candidate
from tools.infra.lean_interact_wrapper import apply_tactic

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
    prior_candidate = ""
    feedback = ""
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
            iteration = {
                "iteration": idx + 1,
                "prompt_kind": prompt.kind,
                "proposal_status": proposal.get("status", "empty"),
                "candidate": "",
                "lean_status": "not_run",
                "lean_ok": False,
                "error": proposal.get("error") or "empty candidate",
            }
            iterations.append(iteration)
            prior_candidate = ""
            feedback = str(iteration["error"])
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
        iteration = {
            "iteration": idx + 1,
            "prompt_kind": prompt.kind,
            "proposal_status": proposal.get("status"),
            "candidate": candidate,
            "raw_candidate": proposal.get("raw_candidate", ""),
            "lean_status": lean_result.get("status") if isinstance(lean_result, dict) else "error",
            "lean_ok": lean_ok,
            "lean_feedback": _lean_feedback(lean_result),
        }
        iterations.append(iteration)
        if lean_ok:
            verified_tactic = candidate
            break
        prior_candidate = candidate
        feedback = str(iteration["lean_feedback"])

    return {
        "schema": SCHEMA,
        "status": "verified" if verified_tactic else "failed",
        "authority": "proposal_with_lean_evidence",
        "promotion_allowed": False,
        "goal": goal.strip(),
        "imports": imports,
        "context": context,
        "max_iterations": max_iterations,
        "verified_tactic": verified_tactic,
        "iterations": iterations,
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
