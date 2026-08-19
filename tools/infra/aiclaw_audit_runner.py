#!/usr/bin/env python3
"""aiClaw-queued Lean owner-file audit runner.

This is the safe replacement for the old browser-harness write-back loop.
It is intentionally advice-only with respect to repo source:

1. send one complete prompt through the repo-local aiClaw single-flight queue;
2. extract a complete Lean drop-in replacement candidate;
3. write the candidate under ``tmp/oracle_candidates``;
4. run ``lake env lean`` on the candidate;
5. report the candidate path and check result for a coding agent to inspect.

Lean remains the authority. ChatGPT/aiClaw is only a proposal source.  This
runner never overwrites an owner file; a coding agent must apply any accepted
repair with a normal reviewed patch.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.aiclaw_chat import DEFAULT_QUEUE_ROOT, ask_ai
from tools.infra.lean_audit_prompt import lean_candidate_reject_reason


DEFAULT_PLATFORM = os.environ.get("AICLAW_PLATFORM", "chatgpt")
DEFAULT_QUEUE_TIMEOUT = float(os.environ.get("AICLAW_QUEUE_TIMEOUT", "900"))

AUDIT_HEADER = """# Audit Proof

## System Prompt

Persona: Audit, a rigorous mathematical proof assistant and technical auditor specialized in Lean 4 formal verification.

Purpose:
- Repair one Lean 4 owner file as a complete drop-in replacement.
- Keep generated content dense, theorem-owner-local, and kernel-checkable.
- Never overwrite a source file unless the candidate compiles first.

Hard rules:
1. Output exactly one complete Lean 4 file, not a diff, not a patch, not snippets.
2. Use one fenced `lean4` code block under a `### Replacement` heading when possible.
3. No conversational prose inside the Lean code block.
4. Do not use `sorry`, `admit`, `axiom`, fake instances, `unsafe`, or vacuous `True` claims.
5. Do not create wrappers, deferred interfaces, certificate packets, `_True`, `_valid`, `_law`, `_proof`, or renamed placeholder surfaces.
6. Do not hide assumptions in structure fields or class fields. A proof is a theorem or lemma, not a data field.
7. Every lemma must contain real, non-vacuous mathematical content derived from Mathlib, repository imports, explicit theorem hypotheses, and verified tactics.
8. Keep the file small and mathlib-style: minimal imports, cohesive owner scope, short local helper lemmas only when they reduce the proof.

Required answer format:

### Replacement
```lean4
-- Full corrected Lean file content only.
```

### API
No API correction.
"""


def build_prompt(text: str) -> str:
    return AUDIT_HEADER + "\n\n" + text


TOP_LEVEL_PREFIXES = (
    "import ",
    "open ",
    "namespace ",
    "end ",
    "section",
    "noncomputable section",
    "universe",
    "variable ",
    "variables ",
    "class ",
    "structure ",
    "inductive ",
    "abbrev ",
    "def ",
    "theorem ",
    "lemma ",
    "example ",
    "instance ",
    "@[",
    "/-!",
)


def is_top_level_start(stripped: str) -> bool:
    return stripped.startswith(TOP_LEVEL_PREFIXES)


def looks_like_calc_step(stripped: str) -> bool:
    return (
        stripped.startswith("_")
        or " = " in stripped
        or " ≤ " in stripped
        or " < " in stripped
        or " ≃ " in stripped
        or " ↔ " in stripped
    )


def repair_column_zero_tactic_layout(code: str) -> str:
    """Indent common ChatGPT column-zero tactic/calc output.

    This is intentionally not a formatter.  It only handles the recurring
    broken shape where a whole-file oracle response emits tactic bodies at
    column zero after `:= by`.  The candidate still must pass Lean before any
    source file is overwritten.
    """
    out: list[str] = []
    in_by_proof = False
    in_calc = False
    after_calc_step_by = False

    for line in code.split("\n"):
        stripped = line.strip()
        column_zero = bool(stripped) and not line.startswith((" ", "\t"))

        if column_zero and is_top_level_start(stripped):
            in_by_proof = ":= by" in stripped
            in_calc = False
            after_calc_step_by = False
            out.append(line)
            continue

        if ":= by" in stripped:
            in_by_proof = True

        if in_by_proof and column_zero:
            if stripped == "calc":
                out.append("  " + stripped)
                in_calc = True
                after_calc_step_by = False
                continue
            if in_calc and looks_like_calc_step(stripped):
                out.append("    " + stripped)
                after_calc_step_by = ":= by" in stripped
                continue
            if in_calc and after_calc_step_by:
                out.append("      " + stripped)
                continue
            out.append("  " + stripped)
            continue

        out.append(line)

    return "\n".join(out)


def normalize_candidate(code: str) -> str:
    code = code.replace("\r\n", "\n").replace("\r", "\n").strip()
    code = repair_column_zero_tactic_layout(code)
    return code + "\n" if code else code


def extract_lean_code(text: str) -> str:
    text = (text or "").strip()
    blocks = re.findall(r"```(?:lean4|lean)?\s*\n(.*?)```", text, flags=re.DOTALL)
    if blocks:
        for block in blocks:
            candidate = normalize_candidate(block)
            if not lean_candidate_reject_reason(candidate):
                return candidate
        return ""
    candidate = normalize_candidate(text)
    return "" if lean_candidate_reject_reason(candidate) else candidate


def candidate_path(target_file: Path, repo_root: Path) -> Path:
    try:
        relative = target_file.resolve().relative_to(repo_root.resolve())
    except ValueError:
        relative = Path(target_file.name)
    safe_name = "__".join(relative.parts)
    out_dir = repo_root / "tmp" / "oracle_candidates"
    out_dir.mkdir(parents=True, exist_ok=True)
    return out_dir / f"{safe_name}.{os.getpid()}.lean"


def run_lean(path: Path, repo_root: Path, timeout: int = 90) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)],
        capture_output=True,
        text=True,
        timeout=timeout,
        cwd=repo_root,
    )


def ask_replacement(prompt: str, *, timeout: int, new: bool) -> str:
    result = ask_ai(
        platform=DEFAULT_PLATFORM,
        prompt=prompt,
        timeout=max(timeout, 30),
        wait=True,
        wait_timeout=max(timeout, 30),
        interval=2,
        new=new,
        quiet=True,
        queue=True,
        queue_root=DEFAULT_QUEUE_ROOT,
        queue_timeout=DEFAULT_QUEUE_TIMEOUT,
        hold_on_suspect=True,
    )
    content = str(result.get("content") or "").strip()
    if content.lower() in {"thinking", "thinking..."} or result.get("suspect_intermediate"):
        raise RuntimeError(
            "aiClaw returned an intermediate Thinking response; lane is held for read-only DOM recovery"
        )
    if not result.get("success", False):
        raise RuntimeError(f"aiClaw send failed: {content[:500]}")
    return extract_lean_code(content)


def try_candidate(candidate: str, *, label: str, target_file: Path, repo_root: Path) -> tuple[bool, str, str]:
    candidate = normalize_candidate(candidate)
    reject_reason = lean_candidate_reject_reason(candidate)
    if reject_reason:
        print(f"CANDIDATE_REJECTED {label}: {reject_reason}")
        return False, reject_reason, candidate
    path = candidate_path(target_file, repo_root)
    path.write_text(candidate, encoding="utf-8")
    print(f"CANDIDATE_SAVED {label}: {path} {len(candidate)} chars {candidate.count(chr(10))} lines")

    lean = run_lean(path, repo_root)
    if lean.returncode != 0:
        error = (lean.stderr or lean.stdout)[:4000]
        print(f"COMPILE_CANDIDATE_FAILED {label}: {error[:300]}...")
        return False, error, candidate

    print(f"CANDIDATE_COMPILES {label}: {path}")
    return True, "", candidate


def run_audit_and_save(target_file: Path, context: str, target_line: int, repo_root: Path) -> bool:
    target_file = target_file.resolve()
    repo_root = repo_root.resolve()

    replacement = ask_replacement(build_prompt(context), timeout=120, new=True)
    ok, error, last_candidate = try_candidate(
        replacement,
        label="attempt_0",
        target_file=target_file,
        repo_root=repo_root,
    )
    if ok:
        return True

    max_retries = int(os.environ.get("AICLAW_AUDIT_FIX_RETRIES", "2"))
    for attempt in range(max_retries):
        fix_prompt = (
            "The previous complete Lean 4 drop-in replacement failed to compile.\n"
            f"Target file: {target_file}\n"
            f"Original request target line: {target_line}\n\n"
            f"Failed candidate:\n```lean4\n{last_candidate[:20000]}\n```\n\n"
            f"Error:\n```\n{error[:1500]}\n```\n"
            "Output one complete corrected Lean 4 file as a drop-in replacement. Zero prose."
        )
        fixed = ask_replacement(build_prompt(fix_prompt), timeout=90, new=True)
        ok, error, last_candidate = try_candidate(
            fixed,
            label=f"attempt_{attempt + 1}",
            target_file=target_file,
            repo_root=repo_root,
        )
        if ok:
            print(f"CANDIDATE_FIXED (attempt {attempt + 1})")
            return True

    print("COMPILE_FAILED_ALL_ATTEMPTS")
    return False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target-file", required=True)
    parser.add_argument("--context-file", required=True)
    parser.add_argument("--target-line", type=int, default=1)
    parser.add_argument("--repo-root", default=str(REPO_ROOT))
    args = parser.parse_args(argv)

    context = Path(args.context_file).read_text(encoding="utf-8")
    ok = run_audit_and_save(
        Path(args.target_file),
        context,
        args.target_line,
        Path(args.repo_root),
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
