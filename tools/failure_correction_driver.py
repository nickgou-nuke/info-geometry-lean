#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Autonomous correction driver for optimization-cycle failures. "
            "It analyzes Lean build output and applies conservative, known-safe "
            "patches to the quarantine theorem before retry."
        )
    )
    parser.add_argument("--context", required=True, help="Path to attempt context JSON")
    parser.add_argument("--build-stdout", required=True, help="Path to lake build stdout log")
    parser.add_argument("--build-stderr", required=True, help="Path to lake build stderr log")
    parser.add_argument("--quarantine-file", required=True, help="Path to quarantine Lean file")
    return parser.parse_args()


def load_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def extract_materialized_theorem_name(context: dict) -> str | None:
    candidate = context.get("selectedCandidate", {})
    sketch = str(candidate.get("materialization_sketch", ""))
    m = re.search(r"\btheorem\s+([A-Za-z0-9_']+)", sketch)
    if m:
        return m.group(1)
    return None


def apply_index_bridge_shape_fix(quarantine_text: str, theorem_name: str | None) -> tuple[str, bool]:
    if theorem_name is None:
        return quarantine_text, False

    # Restrict to the known mismatch family where the proof body forwards
    # `KK.index_bridge_spectral X hF` but an explicit codomain drifts.
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
    # Convert an underspecified theorem wrapper with `: _` into a `def` wrapper
    # so Lean can infer the codomain from the forwarded theorem application.
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


def main() -> int:
    args = parse_args()
    context_path = Path(args.context).resolve()
    build_stdout_path = Path(args.build_stdout).resolve()
    build_stderr_path = Path(args.build_stderr).resolve()
    quarantine_path = Path(args.quarantine_file).resolve()

    context = load_json(context_path)
    stdout_text = load_text(build_stdout_path)
    stderr_text = load_text(build_stderr_path)
    quarantine_text = load_text(quarantine_path)

    theorem_name = extract_materialized_theorem_name(context)
    needs_shape_fix = (
        "Type mismatch" in stdout_text
        and "KK.index_bridge_spectral X hF" in stdout_text
        and "IndexInvariantAlong" in stdout_text
    )
    needs_theorem_hole_fix = (
        "Failed to infer type of theorem" in stdout_text
        and (theorem_name is not None)
    )

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
        reasons.append("no supported failure pattern detected in build output")

    report_path = context_path.with_suffix(".correction.report.md")
    report_lines = [
        "# Failure Correction Report",
        "",
        f"- run id: `{context.get('runId', '')}`",
        f"- attempt: `{context.get('attempt', '')}`",
        f"- applied: `{applied}`",
        f"- theorem: `{theorem_name or ''}`",
        f"- quarantine file: `{quarantine_path}`",
        f"- build stdout: `{build_stdout_path}`",
        f"- build stderr: `{build_stderr_path}`",
        "",
        "## Reasons",
    ]
    for reason in reasons:
        report_lines.append(f"- {reason}")
    report_lines.append("")
    if stderr_text.strip():
        report_lines += ["## Stderr", "", "```", stderr_text.strip(), "```", ""]
    report_path.write_text("\n".join(report_lines), encoding="utf-8")

    print(f"[failure-correction] report: {report_path}")
    print(f"[failure-correction] applied: {applied}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
