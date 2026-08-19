#!/usr/bin/env python3
"""ImProver-style proof optimization probe for local Lean modules.

This is deliberately non-mutating.  It borrows ImProver's first optimization
idea, "rank proofs by a metric before rewriting", but keeps this repository's
Lean files untouched.  The output is a review packet that can be fed to a
future LLM/ImProver pass after the target module has a build gate.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DECL_RE = re.compile(r"^\s*(?:@[^\n]*\s*)?(?P<kind>theorem|lemma|example)\b(?P<head>.*)")


@dataclass
class ProofCandidate:
    file: str
    kind: str
    name: str
    start_line: int
    end_line: int
    proof_lines: int
    tactic_score: int
    authority_class: str
    authority_signals: list[str]
    proof_preview: str
    optimization_hints: list[str]


def leading_spaces(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def decl_name(kind: str, head: str, fallback: str) -> str:
    if kind == "example":
        return fallback
    chunks = head.strip().split()
    if not chunks:
        return fallback
    return chunks[0].split("{")[0].split("(")[0].split(":")[0]


def count_tactics(lines: list[str]) -> int:
    score = 0
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("--") or stripped in {"by", "|"}:
            continue
        score += 1
        score += stripped.replace("<;>", "").count(";")
    return score


def hints_for(lines: list[str]) -> list[str]:
    text = "\n".join(lines)
    hints: list[str] = []
    if "\n  exact " in text or "\n    exact " in text:
        hints.append("exact-heavy proof; check whether the theorem can be compressed to one exact term")
    if "calc" in text:
        hints.append("calc chain present; check whether owner rewrite lemmas or simpa can shorten it")
    if "constructor" in text or "constructor" in " ".join(line.strip() for line in lines):
        hints.append("constructor proof; candidate for exact structure literal or constructor combinator")
    if "rw [" in text:
        hints.append("rewrite-heavy proof; candidate for simp/simpa lemma set minimization")
    if "noncomm_ring" in text or "ring" in text:
        hints.append("ring tactic present; keep if it is the canonical algebraic closure step")
    if "sorry" in text or "admit" in text:
        hints.append("incomplete proof marker present; do not optimize until proof is closed")
    if not hints:
        hints.append("long proof candidate; inspect for repeated local lemmas or reusable owner theorem")
    return hints


MATHLIB_ROOT_SIGNALS = (
    "Mathlib.",
    "Submodule.starProjection",
    "orthogonalProjection",
    "IsStarProjection",
    "isStarProjection_iff",
    "ContinuousLinearMap.",
    "LinearMap.",
    "Commute",
    "pow_succ",
    "mul_assoc",
)

REPO_ROOT_SIGNALS = (
    "InfoGeometry.",
    "IsDrazinInverse",
    "IsMoorePenroseInverse",
    "Drazin.",
    "MoorePenrose.",
    "CertifiedInverseKernel.",
    "projection_is",
    "rightProjector_",
    "leftProjector_",
)

DEFERRED_INTERFACE_SIGNALS = (
    "Packet",
    "Context",
    "Interface",
    "interface",
    "certificate",
    "Certificate",
    "witness",
    "Witness",
    "Nonempty",
    "True",
    "by trivial",
)


def authority_class_for(block: list[str], imports: list[str], name: str) -> tuple[str, list[str]]:
    """Classify whether a candidate is proof-rooted or deferred-interface-shaped.

    This is deliberately conservative.  It does not prove authority; it prevents
    the optimizer queue from treating witness/certificate/interface wrappers as
    equivalent to genuine Mathlib/repo-rooted proof chains.
    """

    text = "\n".join(imports + block)
    signals: list[str] = []

    mathlib_hits = [sig for sig in MATHLIB_ROOT_SIGNALS if sig in text]
    repo_hits = [sig for sig in REPO_ROOT_SIGNALS if sig in text]
    interface_hits = [sig for sig in DEFERRED_INTERFACE_SIGNALS if sig in text or sig in name]

    if mathlib_hits:
        signals.append("mathlib:" + ",".join(mathlib_hits[:4]))
    if repo_hits:
        signals.append("repo:" + ",".join(repo_hits[:4]))
    if interface_hits:
        signals.append("interface:" + ",".join(interface_hits[:4]))

    has_root = bool(mathlib_hits or repo_hits)
    has_interface = bool(interface_hits)
    if has_root and has_interface:
        return "mixed_root_and_interface", signals
    if mathlib_hits:
        return "mathlib_rooted_proof_chain", signals
    if repo_hits:
        return "repo_rooted_proof_chain", signals
    if has_interface:
        if any(sig.lower() in {"certificate", "witness"} for sig in interface_hits):
            return "certificate_interface", signals
        return "deferred_interface", signals
    return "unclassified_local_proof", signals


def theorem_blocks(path: Path) -> Iterable[ProofCandidate]:
    lines = path.read_text(encoding="utf-8").splitlines()
    imports = [line for line in lines if line.startswith("import ")]
    i = 0
    while i < len(lines):
        match = DECL_RE.match(lines[i])
        if match is None:
            i += 1
            continue
        start = i
        decl_indent = leading_spaces(lines[i])
        j = i + 1
        while j < len(lines):
            stripped = lines[j].strip()
            if j > start and DECL_RE.match(lines[j]) and leading_spaces(lines[j]) <= decl_indent:
                break
            if j > start and stripped.startswith("/--") and leading_spaces(lines[j]) <= decl_indent:
                break
            if j > start and stripped.startswith("end ") and leading_spaces(lines[j]) <= decl_indent:
                break
            j += 1
        block = lines[start:j]
        if any(":= by" in line or line.strip() == "by" for line in block):
            proof_lines = [line for line in block if line.strip()]
            kind = match.group("kind")
            name = decl_name(kind, match.group("head"), f"example_at_{start + 1}")
            authority_class, authority_signals = authority_class_for(block, imports, name)
            preview = "\n".join(block[: min(len(block), 12)])
            yield ProofCandidate(
                file=str(path),
                kind=kind,
                name=name,
                start_line=start + 1,
                end_line=j,
                proof_lines=len(proof_lines),
                tactic_score=count_tactics(block),
                authority_class=authority_class,
                authority_signals=authority_signals,
                proof_preview=preview,
                optimization_hints=hints_for(block),
            )
        i = max(j, i + 1)


def iter_lean_files(paths: list[Path]) -> Iterable[Path]:
    for path in paths:
        if path.is_dir():
            yield from sorted(path.rglob("*.lean"))
        elif path.suffix == ".lean":
            yield path


def render_prompt(candidates: list[ProofCandidate]) -> str:
    lines = [
        "# Lean Proof Optimization Probe",
        "",
        "This is a non-mutating ImProver-style candidate packet.",
        "",
        "Rules for a rewrite agent:",
        "- Preserve theorem statements and names.",
        "- Do not introduce `sorry`, `admit`, axioms, or new witness fields.",
        "- Any proposed rewrite must pass a targeted `lake env lean <file>` gate before replacing source.",
        "- Prefer owner-root lemmas and existing canonical theorem surfaces over clever local golfing.",
        "",
        "Top candidates:",
    ]
    for cand in candidates:
        lines.extend(
            [
                "",
                f"## `{cand.name}`",
                f"- File: `{cand.file}:{cand.start_line}`",
                f"- Kind: `{cand.kind}`",
                f"- Tactic score: `{cand.tactic_score}`",
                f"- Nonempty proof lines: `{cand.proof_lines}`",
                f"- Authority class: `{cand.authority_class}`",
                f"- Authority signals: {', '.join(cand.authority_signals) if cand.authority_signals else 'none'}",
                f"- Hints: {'; '.join(cand.optimization_hints)}",
                "",
                "```lean",
                cand.proof_preview,
                "```",
            ]
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description="Rank Lean proof blocks for ImProver-style optimization")
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument("--min-score", type=int, default=5)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--md-out", type=Path)
    args = parser.parse_args()

    candidates: list[ProofCandidate] = []
    for lean_file in iter_lean_files(args.paths):
        candidates.extend(theorem_blocks(lean_file))
    candidates = [cand for cand in candidates if cand.tactic_score >= args.min_score]
    candidates.sort(key=lambda cand: (cand.tactic_score, cand.proof_lines), reverse=True)
    candidates = candidates[: args.limit]

    payload = {
        "schema": "info_geometry.lean_improver_probe.v1",
        "candidateCount": len(candidates),
        "candidates": [asdict(cand) for cand in candidates],
        "improverCompatibility": {
            "mode": "metric_probe_only",
            "metric": "tactic_score",
            "mutatesLeanSource": False,
            "requiresLLM": False,
        },
    }
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    prompt = render_prompt(candidates)
    if args.md_out is not None:
        args.md_out.parent.mkdir(parents=True, exist_ok=True)
        args.md_out.write_text(prompt, encoding="utf-8")
    if args.json_out is None and args.md_out is None:
        print(prompt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
