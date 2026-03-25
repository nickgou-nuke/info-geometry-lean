#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

MATERIALIZATION_BANNER = "/-- External proof-driver materialization of the selected candidate sketch. -/\n"
NAMESPACE_END = "\n\nend InfoGeometry.Unstable.AutoOptCycle\n"
PLACEHOLDER_PATTERNS = (
    (re.compile(r"\.\.\."), "replacement block still contains ellipsis placeholders"),
    (
        re.compile(r"local hypotheses specialized to the target declaration"),
        "replacement block still contains placeholder hypotheses",
    ),
    (
        re.compile(r"direct transport / invariance / closure statement feeding the frontier"),
        "replacement block still contains placeholder goal text",
    ),
    (re.compile(r":=\s*by\s*$", re.S), "replacement block ends with an empty `:= by` body"),
)


@dataclass(frozen=True)
class CommandResult:
    argv: list[str]
    returncode: int
    stdout_path: str
    stderr_path: str


@dataclass(frozen=True)
class RepairAttempt:
    backend: str
    creative_command: list[str] | None
    creative_result: CommandResult | None
    creative_prompt: str | None
    creative_output: str | None
    critical_command: list[str] | None
    critical_result: CommandResult | None
    critical_prompt: str | None
    critical_output: str | None
    review_verdict: str | None
    quarantine_recommendation: str | None
    repair_reason: str | None
    replacement_block: str | None
    applied: bool


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "LLM-backed correction driver for optimization-cycle failures. "
            "It can render creative/critical repair prompts, invoke optional external "
            "LLM wrappers, apply a reviewed replacement theorem block, and fall back "
            "to conservative built-in theorem-shape fixes when no reviewed repair survives."
        )
    )
    parser.add_argument("--context", required=True, help="Path to attempt context JSON")
    parser.add_argument("--build-stdout", required=True, help="Path to lake build stdout log")
    parser.add_argument("--build-stderr", required=True, help="Path to lake build stderr log")
    parser.add_argument("--quarantine-file", required=True, help="Path to quarantine Lean file")
    parser.add_argument(
        "--creative-command",
        default=os.environ.get("INFO_GEOMETRY_LLM_REPAIR_CREATIVE_COMMAND"),
        help=(
            "Optional external creative-repair command template. Supported placeholders: "
            "{context_json}, {worktree}, {module}, {relative_file}, {quarantine_file}, {attempt}, "
            "{run_dir}, {build_stdout}, {build_stderr}, {prompt_file}, {output_file}."
        ),
    )
    parser.add_argument(
        "--critical-command",
        default=os.environ.get("INFO_GEOMETRY_LLM_REPAIR_CRITICAL_COMMAND"),
        help=(
            "Optional external critical-repair command template. Supported placeholders: "
            "{context_json}, {worktree}, {module}, {relative_file}, {quarantine_file}, {attempt}, "
            "{run_dir}, {build_stdout}, {build_stderr}, {prompt_file}, {output_file}, {creative_output}."
        ),
    )
    parser.add_argument(
        "--max-log-chars",
        type=int,
        default=12000,
        help="Maximum trailing stdout/stderr characters to embed in generated prompts.",
    )
    parser.add_argument(
        "--disable-heuristic-fallback",
        action="store_true",
        help="Do not attempt the built-in known-safe theorem-shape fixes when no reviewed repair applies.",
    )
    return parser.parse_args()


def load_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def tail_text(text: str, max_chars: int) -> str:
    body = text.strip()
    if len(body) <= max_chars:
        return body
    return body[-max_chars:]


def extract_materialized_theorem_name(context: dict[str, Any]) -> str | None:
    candidate = context.get("selectedCandidate", {})
    for field in ("materialization_sketch", "signature_sketch"):
        sketch = str(candidate.get(field, ""))
        m = re.search(r"\b(?:theorem|def|lemma)\s+([A-Za-z0-9_']+)", sketch)
        if m:
            return m.group(1)
    return None


def locate_materialized_block(quarantine_text: str) -> tuple[int, int, str] | None:
    banner_start = quarantine_text.find(MATERIALIZATION_BANNER)
    if banner_start == -1:
        return None
    block_start = banner_start + len(MATERIALIZATION_BANNER)
    block_end = quarantine_text.find(NAMESPACE_END, block_start)
    if block_end == -1:
        raise SystemExit("quarantine file does not end with expected namespace marker")
    return block_start, block_end, quarantine_text[block_start:block_end].strip()


def replace_materialized_block(quarantine_text: str, replacement_block: str) -> str:
    located = locate_materialized_block(quarantine_text)
    if located is None:
        raise SystemExit("no materialized theorem block found in quarantine file")
    block_start, block_end, _ = located
    replacement = replacement_block.rstrip() + "\n"
    return quarantine_text[:block_start] + replacement + quarantine_text[block_end:]


def placeholder_reasons(text: str) -> list[str]:
    reasons: list[str] = []
    for pattern, message in PLACEHOLDER_PATTERNS:
        if pattern.search(text):
            reasons.append(message)
    return reasons


def capture_inline_value(text: str, labels: list[str]) -> str | None:
    for label in labels:
        match = re.search(rf"`{re.escape(label)}`\s*`([^`]+)`", text, flags=re.S)
        if match:
            return match.group(1).strip()
    return None


def capture_code_block(text: str, labels: list[str]) -> str | None:
    for label in labels:
        match = re.search(rf"`{re.escape(label)}`\s*```lean\n(.*?)```", text, flags=re.S)
        if match:
            return match.group(1).strip()
    return None


def capture_section(text: str, labels: list[str], next_labels: list[str]) -> str | None:
    starts: list[tuple[int, int]] = []
    for label in labels:
        match = re.search(rf"`{re.escape(label)}`", text, flags=re.S)
        if match:
            starts.append((match.start(), match.end()))
    if not starts:
        return None
    _, start_end = min(starts, key=lambda item: item[0])
    end_positions: list[int] = []
    for label in next_labels:
        match = re.search(rf"`{re.escape(label)}`", text[start_end:], flags=re.S)
        if match:
            end_positions.append(start_end + match.start())
    end = min(end_positions) if end_positions else len(text)
    return text[start_end:end].strip()


def normalize_yes_no(value: str | None) -> str | None:
    if value is None:
        return None
    normalized = value.strip().lower().replace("_", "-")
    if normalized in {"yes", "no"}:
        return normalized
    return value.strip().lower()


def parse_reviewed_repair(text: str) -> dict[str, Any]:
    verdict = capture_inline_value(text, ["repair verdict", "review verdict", "verdict"])
    recommendation = normalize_yes_no(
        capture_inline_value(text, ["quarantine recommendation", "quarantine_recommendation"]) 
    )
    reason = capture_section(
        text,
        ["repair reason", "review reason", "reason"],
        [
            "quarantine recommendation",
            "quarantine_recommendation",
            "replacement theorem block",
            "Lean-ready replacement block",
            "replacement Lean block",
            "reviewed Lean replacement",
            "blocked moves",
            "allowed helper lemmas",
        ],
    )
    replacement = capture_code_block(
        text,
        [
            "replacement theorem block",
            "Lean-ready replacement block",
            "replacement Lean block",
            "reviewed Lean replacement",
            "corrected theorem block",
        ],
    )
    if replacement is None:
        inline_none = capture_inline_value(text, ["replacement theorem block", "replacement Lean block"])
        if inline_none and inline_none.strip().lower() == "none":
            replacement = None
    return {
        "review_verdict": verdict.strip().lower() if verdict else None,
        "quarantine_recommendation": recommendation,
        "repair_reason": reason,
        "replacement_block": replacement,
    }


def run_capture(argv: list[str], cwd: Path, stdout_path: Path, stderr_path: Path) -> CommandResult:
    stdout_path.parent.mkdir(parents=True, exist_ok=True)
    stderr_path.parent.mkdir(parents=True, exist_ok=True)
    with stdout_path.open("w", encoding="utf-8") as stdout_handle, stderr_path.open(
        "w", encoding="utf-8"
    ) as stderr_handle:
        completed = subprocess.run(argv, cwd=cwd, stdout=stdout_handle, stderr=stderr_handle, text=True)
    return CommandResult(
        argv=argv,
        returncode=completed.returncode,
        stdout_path=str(stdout_path),
        stderr_path=str(stderr_path),
    )


def persist_output_from_stdout(output_path: Path, stdout_path: Path) -> str:
    if output_path.exists():
        text = output_path.read_text(encoding="utf-8").strip()
        if text:
            return text
    text = load_text(stdout_path).strip()
    if text:
        output_path.write_text(text + "\n", encoding="utf-8")
        return text
    return ""


def format_external_command(template: str, placeholders: dict[str, Any]) -> list[str]:
    formatted = template.format(**{key: str(value) for key, value in placeholders.items()})
    return shlex.split(formatted)


def render_creative_prompt(
    context: dict[str, Any],
    current_block: str,
    reviewed_sketch: str,
    build_stdout: str,
    build_stderr: str,
) -> str:
    candidate = context.get("selectedCandidate", {})
    chosen = context.get("chosenFrontier", {})
    target_names = [str(x) for x in chosen.get("primaryProduces", [])]
    return f"""# Failure Repair Creative Prompt

Use this prompt with a creative repair model.

Your role is to propose minimal Lean 4 edits that repair the current quarantine theorem after a failed `lake build`.

Constraints:
- Do not invent new axioms or `sorry`.
- Prefer the smallest local repair to the current materialized theorem block.
- Treat the reviewed sketch as the semantic anchor.
- Output proposal text only. Do not claim a proof is valid until Lean accepts it.

## Context
- run id: `{context.get('runId', '')}`
- attempt: `{context.get('attempt', '')}`
- module: `{context.get('module', '')}`
- frontier target: `{', '.join(target_names)}`
- reviewed candidate: `{candidate.get('name', '')}`

## Reviewed Candidate Sketch

```lean
{reviewed_sketch}
```

## Current Materialized Theorem Block

```lean
{current_block}
```

## Lean stdout tail

```
{build_stdout}
```

## Lean stderr tail

```
{build_stderr}
```

## Required output
Provide:
1. a short diagnosis of the failure,
2. one primary repair proposal,
3. at most two fallback ideas,
4. if possible, one exact replacement theorem block in fenced `lean` code.
"""


def render_critical_prompt(
    context: dict[str, Any],
    current_block: str,
    reviewed_sketch: str,
    build_stdout: str,
    build_stderr: str,
    creative_output: str,
) -> str:
    candidate = context.get("selectedCandidate", {})
    chosen = context.get("chosenFrontier", {})
    target_names = [str(x) for x in chosen.get("primaryProduces", [])]
    return f"""# Failure Repair Critical Prompt

Use this prompt with a critical Lean-aware repair model.

Treat the creative output as untrusted proposal text. Approve only a minimal replacement block that is concrete enough to write back into the quarantine file for another Lean build.

Constraints:
- No `sorry`, no axioms, no placeholder bodies.
- Prefer replacing only the materialized theorem block.
- Keep the repair anchored to the reviewed candidate sketch.
- If no safe replacement survives, reject.

## Context
- run id: `{context.get('runId', '')}`
- attempt: `{context.get('attempt', '')}`
- module: `{context.get('module', '')}`
- frontier target: `{', '.join(target_names)}`
- reviewed candidate: `{candidate.get('name', '')}`

## Reviewed Candidate Sketch

```lean
{reviewed_sketch}
```

## Current Materialized Theorem Block

```lean
{current_block}
```

## Lean stdout tail

```
{build_stdout}
```

## Lean stderr tail

```
{build_stderr}
```

## Creative Output

{creative_output}

## Required output
Use the exact field labels below.

`repair verdict`

`accept` or `reject`

`repair reason`

Short justification.

`quarantine recommendation`

`yes` or `no`

`replacement theorem block`

```lean
-- full replacement theorem/def block, or omit if rejecting
```
"""


def llm_backend_attempt(
    *,
    creative_template: str,
    critical_template: str,
    context: dict[str, Any],
    context_path: Path,
    quarantine_path: Path,
    run_dir: Path,
    current_block: str,
    reviewed_sketch: str,
    build_stdout_path: Path,
    build_stderr_path: Path,
    max_log_chars: int,
) -> tuple[RepairAttempt, list[str]]:
    reasons: list[str] = []
    attempt = int(context.get("attempt", 0) or 0)
    worktree = Path(str(context.get("worktreePath", quarantine_path.parent))).resolve()
    module = str(context.get("module", ""))
    relative_file = str(context.get("relativeFile", ""))
    build_stdout_text = tail_text(load_text(build_stdout_path), max_log_chars)
    build_stderr_text = tail_text(load_text(build_stderr_path), max_log_chars)

    creative_prompt_path = run_dir / f"failure-correction-{attempt}.creative.prompt.md"
    creative_output_path = run_dir / f"failure-correction-{attempt}.creative.output.md"
    critical_prompt_path = run_dir / f"failure-correction-{attempt}.critical.prompt.md"
    critical_output_path = run_dir / f"failure-correction-{attempt}.critical.output.md"

    creative_prompt = render_creative_prompt(
        context,
        current_block=current_block,
        reviewed_sketch=reviewed_sketch,
        build_stdout=build_stdout_text,
        build_stderr=build_stderr_text,
    )
    creative_prompt_path.write_text(creative_prompt, encoding="utf-8")

    placeholders = {
        "context_json": context_path,
        "worktree": worktree,
        "module": module,
        "relative_file": relative_file,
        "quarantine_file": quarantine_path,
        "attempt": attempt,
        "run_dir": run_dir,
        "build_stdout": build_stdout_path,
        "build_stderr": build_stderr_path,
        "prompt_file": creative_prompt_path,
        "output_file": creative_output_path,
        "creative_output": creative_output_path,
    }
    creative_argv = format_external_command(creative_template, placeholders)
    creative_result = run_capture(
        creative_argv,
        cwd=worktree,
        stdout_path=run_dir / f"failure-correction-{attempt}.creative.stdout.log",
        stderr_path=run_dir / f"failure-correction-{attempt}.creative.stderr.log",
    )
    creative_output = persist_output_from_stdout(creative_output_path, Path(creative_result.stdout_path))
    if not creative_output:
        reasons.append("creative repair command produced no output")

    critical_prompt = render_critical_prompt(
        context,
        current_block=current_block,
        reviewed_sketch=reviewed_sketch,
        build_stdout=build_stdout_text,
        build_stderr=build_stderr_text,
        creative_output=creative_output or "(empty creative output)",
    )
    critical_prompt_path.write_text(critical_prompt, encoding="utf-8")

    placeholders.update({"prompt_file": critical_prompt_path, "output_file": critical_output_path})
    critical_argv = format_external_command(critical_template, placeholders)
    critical_result = run_capture(
        critical_argv,
        cwd=worktree,
        stdout_path=run_dir / f"failure-correction-{attempt}.critical.stdout.log",
        stderr_path=run_dir / f"failure-correction-{attempt}.critical.stderr.log",
    )
    critical_output = persist_output_from_stdout(critical_output_path, Path(critical_result.stdout_path))
    parsed = parse_reviewed_repair(critical_output)

    applied = False
    replacement_block = parsed.get("replacement_block")
    verdict = parsed.get("review_verdict")
    recommendation = parsed.get("quarantine_recommendation")
    repair_reason = parsed.get("repair_reason")

    if not critical_output:
        reasons.append("critical repair command produced no output")
    if verdict != "accept":
        reasons.append("critical repair verdict is not accept")
    if recommendation != "yes":
        reasons.append("critical repair does not approve quarantine execution")
    if replacement_block is None:
        reasons.append("critical repair output does not provide a replacement theorem block")
    else:
        reasons.extend(placeholder_reasons(replacement_block))

    if replacement_block is not None and replacement_block.strip() == current_block.strip():
        reasons.append("critical repair replacement block is identical to the current materialized theorem")

    if not reasons and replacement_block is not None:
        updated = replace_materialized_block(load_text(quarantine_path), replacement_block)
        quarantine_path.write_text(updated, encoding="utf-8")
        applied = True

    return (
        RepairAttempt(
            backend="llm",
            creative_command=creative_argv,
            creative_result=creative_result,
            creative_prompt=str(creative_prompt_path),
            creative_output=str(creative_output_path),
            critical_command=critical_argv,
            critical_result=critical_result,
            critical_prompt=str(critical_prompt_path),
            critical_output=str(critical_output_path),
            review_verdict=verdict,
            quarantine_recommendation=recommendation,
            repair_reason=repair_reason,
            replacement_block=replacement_block,
            applied=applied,
        ),
        reasons,
    )


def apply_index_bridge_shape_fix(quarantine_text: str, theorem_name: str | None) -> tuple[str, bool]:
    if theorem_name is None:
        return quarantine_text, False

    body_pat = re.compile(
        rf"(theorem\s+{re.escape(theorem_name)}[\s\S]*?\(hF\s*:\s*X\.F\s*\*\s*X\.F\s*=\s*1\)\s*:\s*)([\s\S]*?)(\s*:=\s*by\s*\n\s*)simpa\s+using\s+InfoGeometry\.KK\.index_bridge_spectral\s*\(X\s*:=\s*X\)\s*hF",
        re.M,
    )

    m = body_pat.search(quarantine_text)
    if not m:
        return quarantine_text, False

    replacement = (
        m.group(1)
        + "_"
        + m.group(3)
        + "exact InfoGeometry.KK.index_bridge_spectral (X := X) hF"
    )
    fixed = quarantine_text[: m.start()] + replacement + quarantine_text[m.end() :]
    return fixed, True


def apply_theorem_hole_to_def_fix(quarantine_text: str, theorem_name: str | None) -> tuple[str, bool]:
    if theorem_name is None:
        return quarantine_text, False
    pat = re.compile(
        rf"\btheorem\s+{re.escape(theorem_name)}\b([\s\S]*?\(hF\s*:\s*X\.F\s*\*\s*X\.F\s*=\s*1\)\s*:)\s*_\s*:=\s*by\s*\n\s*exact\s+InfoGeometry\.KK\.index_bridge_spectral\s*\(X\s*:=\s*X\)\s*hF",
        re.M,
    )
    m = pat.search(quarantine_text)
    if not m:
        return quarantine_text, False
    replacement = (
        f"def {theorem_name}"
        + m.group(1).replace(":", " :=", 1)
        + "\n  InfoGeometry.KK.index_bridge_spectral (X := X) hF"
    )
    fixed = quarantine_text[: m.start()] + replacement + quarantine_text[m.end() :]
    return fixed, True


def heuristic_fallback(
    context: dict[str, Any],
    build_stdout: str,
    quarantine_path: Path,
) -> tuple[RepairAttempt, list[str]]:
    theorem_name = extract_materialized_theorem_name(context)
    quarantine_text = load_text(quarantine_path)
    needs_shape_fix = (
        "Type mismatch" in build_stdout
        and "KK.index_bridge_spectral X hF" in build_stdout
        and "IndexInvariantAlong" in build_stdout
    )
    needs_theorem_hole_fix = "Failed to infer type of theorem" in build_stdout and (theorem_name is not None)

    applied = False
    reasons: list[str] = []
    if needs_shape_fix:
        fixed_text, applied = apply_index_bridge_shape_fix(quarantine_text, theorem_name)
        if applied:
            quarantine_path.write_text(fixed_text, encoding="utf-8")
            reasons.append("applied index_bridge_spectral theorem-shape correction")
        else:
            reasons.append("matched failure class but theorem block pattern not found")
    elif needs_theorem_hole_fix:
        fixed_text, applied = apply_theorem_hole_to_def_fix(quarantine_text, theorem_name)
        if applied:
            quarantine_path.write_text(fixed_text, encoding="utf-8")
            reasons.append("converted underspecified theorem wrapper to def wrapper")
        else:
            reasons.append("matched theorem-hole failure class but wrapper pattern not found")
    else:
        reasons.append("no supported heuristic failure pattern detected in build output")

    return (
        RepairAttempt(
            backend="heuristic",
            creative_command=None,
            creative_result=None,
            creative_prompt=None,
            creative_output=None,
            critical_command=None,
            critical_result=None,
            critical_prompt=None,
            critical_output=None,
            review_verdict=None,
            quarantine_recommendation=None,
            repair_reason=None,
            replacement_block=None,
            applied=applied,
        ),
        reasons,
    )


def write_report(
    report_path: Path,
    *,
    context: dict[str, Any],
    quarantine_path: Path,
    build_stdout_path: Path,
    build_stderr_path: Path,
    attempt: RepairAttempt,
    reasons: list[str],
) -> None:
    theorem_name = extract_materialized_theorem_name(context)
    lines = [
        "# Failure Correction Report",
        "",
        f"- run id: `{context.get('runId', '')}`",
        f"- attempt: `{context.get('attempt', '')}`",
        f"- backend: `{attempt.backend}`",
        f"- applied: `{attempt.applied}`",
        f"- theorem: `{theorem_name or ''}`",
        f"- quarantine file: `{quarantine_path}`",
        f"- build stdout: `{build_stdout_path}`",
        f"- build stderr: `{build_stderr_path}`",
        f"- review verdict: `{attempt.review_verdict or ''}`",
        f"- quarantine recommendation: `{attempt.quarantine_recommendation or ''}`",
        "",
        "## Reasons",
    ]
    for reason in reasons or ["none"]:
        lines.append(f"- {reason}")
    lines.append("")
    if attempt.creative_prompt or attempt.critical_prompt:
        lines += ["## LLM Repair Artifacts", ""]
        if attempt.creative_prompt:
            lines.append(f"- creative prompt: `{attempt.creative_prompt}`")
        if attempt.creative_output:
            lines.append(f"- creative output: `{attempt.creative_output}`")
        if attempt.creative_result:
            lines.append(f"- creative return code: `{attempt.creative_result.returncode}`")
        if attempt.critical_prompt:
            lines.append(f"- critical prompt: `{attempt.critical_prompt}`")
        if attempt.critical_output:
            lines.append(f"- critical output: `{attempt.critical_output}`")
        if attempt.critical_result:
            lines.append(f"- critical return code: `{attempt.critical_result.returncode}`")
        if attempt.repair_reason:
            lines += ["", "## Critical Reason", "", attempt.repair_reason, ""]
    report_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    context_path = Path(args.context).resolve()
    build_stdout_path = Path(args.build_stdout).resolve()
    build_stderr_path = Path(args.build_stderr).resolve()
    quarantine_path = Path(args.quarantine_file).resolve()
    run_dir = context_path.parent

    context = load_json(context_path)
    build_stdout = load_text(build_stdout_path)
    build_stderr = load_text(build_stderr_path)
    quarantine_text = load_text(quarantine_path)
    located = locate_materialized_block(quarantine_text)
    report_path = context_path.with_suffix('.correction.report.md')

    reviewed_sketch = str(
        context.get('selectedCandidate', {}).get('materialization_sketch')
        or context.get('selectedCandidate', {}).get('signature_sketch')
        or ''
    ).strip()

    reasons: list[str] = []
    if located is None:
        attempt = RepairAttempt(
            backend='none',
            creative_command=None,
            creative_result=None,
            creative_prompt=None,
            creative_output=None,
            critical_command=None,
            critical_result=None,
            critical_prompt=None,
            critical_output=None,
            review_verdict=None,
            quarantine_recommendation=None,
            repair_reason=None,
            replacement_block=None,
            applied=False,
        )
        reasons.append('no materialized theorem block found in quarantine file')
    else:
        _, _, current_block = located
        attempt = RepairAttempt(
            backend='none',
            creative_command=None,
            creative_result=None,
            creative_prompt=None,
            creative_output=None,
            critical_command=None,
            critical_result=None,
            critical_prompt=None,
            critical_output=None,
            review_verdict=None,
            quarantine_recommendation=None,
            repair_reason=None,
            replacement_block=None,
            applied=False,
        )
        llm_configured = bool(args.creative_command and args.critical_command)
        if llm_configured:
            attempt, reasons = llm_backend_attempt(
                creative_template=args.creative_command,
                critical_template=args.critical_command,
                context=context,
                context_path=context_path,
                quarantine_path=quarantine_path,
                run_dir=run_dir,
                current_block=current_block,
                reviewed_sketch=reviewed_sketch or current_block,
                build_stdout_path=build_stdout_path,
                build_stderr_path=build_stderr_path,
                max_log_chars=max(args.max_log_chars, 1000),
            )
        else:
            reasons.append('no LLM repair backend configured; set INFO_GEOMETRY_LLM_REPAIR_CREATIVE_COMMAND and INFO_GEOMETRY_LLM_REPAIR_CRITICAL_COMMAND or pass both flags')

        if not attempt.applied and not args.disable_heuristic_fallback:
            fallback_attempt, fallback_reasons = heuristic_fallback(context, build_stdout, quarantine_path)
            if fallback_attempt.applied:
                attempt = fallback_attempt
                reasons.extend(fallback_reasons)
            else:
                reasons.extend(fallback_reasons)

    write_report(
        report_path,
        context=context,
        quarantine_path=quarantine_path,
        build_stdout_path=build_stdout_path,
        build_stderr_path=build_stderr_path,
        attempt=attempt,
        reasons=reasons,
    )

    print(f"[failure-correction] report: {report_path}")
    print(f"[failure-correction] backend: {attempt.backend}")
    print(f"[failure-correction] applied: {attempt.applied}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
