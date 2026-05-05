#!/usr/bin/env python3
"""Hive workflow policy checks inspired by Lean agent workflow packs.

This module is governance only.  It does not prove Lean code and it does not
promote packets.  It gives Hive workers a small, auditable contract for what a
workflow mode is allowed to do before Lean/build/audit authority gates run.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.hive_workflow_policy.v1"

WORKFLOW_MODES = {
    "draft",
    "formalize",
    "prove",
    "autoprove",
    "review",
    "refactor",
    "golf",
    "checkpoint",
    "doctor",
}

HEADER_IMMUTABLE_MODES = {"prove", "autoprove", "refactor", "golf"}
NO_EDIT_MODES = {"review", "doctor"}
CHECKPOINT_REQUIRED_MODES = {"checkpoint"}
PROOF_PRODUCTION_MODES = {"prove", "autoprove", "formalize"}

UNSOUND_MARKERS = ("sorry", "admit", "axiom")


@dataclass(frozen=True)
class PolicyViolation:
    code: str
    message: str
    severity: str = "error"

    def to_json(self) -> dict[str, str]:
        return {"code": self.code, "message": self.message, "severity": self.severity}


def normalize_mode(mode: Any) -> str:
    return str(mode or "").strip().lower().replace("_", "-")


def declaration_header(source: str) -> str:
    """Return a stable theorem/def/lemma header prefix before `:=` or `where`.

    This is intentionally syntactic.  It is a workflow guard, not a Lean parser.
    Lean remains the authority for actual declaration validity.
    """
    text = re.sub(r"\s+", " ", source or "").strip()
    if not text:
        return ""
    for sep in (" := ", " where "):
        if sep in text:
            return text.split(sep, 1)[0].strip()
    by_idx = text.find(" by ")
    if by_idx >= 0:
        return text[:by_idx].strip()
    return text


def changed_files(before: dict[str, str], after: dict[str, str]) -> list[str]:
    names = sorted(set(before) | set(after))
    return [name for name in names if before.get(name, "") != after.get(name, "")]


def unsound_marker_hits(text: str) -> list[str]:
    hits: list[str] = []
    for marker in UNSOUND_MARKERS:
        if re.search(rf"\b{re.escape(marker)}\b", text or ""):
            hits.append(marker)
    return hits


def check_workflow_policy(
    *,
    mode: str,
    before_files: dict[str, str],
    after_files: dict[str, str],
    theorem_before: str = "",
    theorem_after: str = "",
    targeted_build_passed: bool | None = None,
    project_build_passed: bool | None = None,
    axiom_audit_passed: bool | None = None,
    allow_unsound_markers: bool = False,
) -> dict[str, Any]:
    mode = normalize_mode(mode)
    violations: list[PolicyViolation] = []

    if mode not in WORKFLOW_MODES:
        violations.append(
            PolicyViolation("unknown_workflow_mode", f"unknown Hive workflow mode: {mode or '<empty>'}")
        )

    touched = changed_files(before_files, after_files)
    if mode in NO_EDIT_MODES and touched:
        violations.append(
            PolicyViolation(
                "no_edit_mode_modified_files",
                f"workflow mode `{mode}` is read-only but modified {len(touched)} file(s)",
            )
        )

    if mode in HEADER_IMMUTABLE_MODES:
        h_before = declaration_header(theorem_before)
        h_after = declaration_header(theorem_after)
        if h_before and h_after and h_before != h_after:
            violations.append(
                PolicyViolation(
                    "declaration_header_changed",
                    f"workflow mode `{mode}` must not change declaration headers",
                )
            )

    if mode in CHECKPOINT_REQUIRED_MODES:
        if targeted_build_passed is not True:
            violations.append(PolicyViolation("checkpoint_missing_targeted_build", "checkpoint requires targeted build pass"))
        if project_build_passed is not True:
            violations.append(PolicyViolation("checkpoint_missing_project_build", "checkpoint requires project build pass"))
        if axiom_audit_passed is not True:
            violations.append(PolicyViolation("checkpoint_missing_axiom_audit", "checkpoint requires axiom audit pass"))

    if not allow_unsound_markers:
        marker_files = []
        for file_name, text in after_files.items():
            hits = unsound_marker_hits(text)
            if hits:
                marker_files.append({"file": file_name, "markers": hits})
        if marker_files:
            violations.append(
                PolicyViolation(
                    "unsound_marker_present",
                    "after-state contains sorry/admit/axiom markers",
                )
            )

    return {
        "schema": SCHEMA,
        "mode": mode,
        "ok": not violations,
        "changed_files": touched,
        "guards": {
            "header_immutable": mode in HEADER_IMMUTABLE_MODES,
            "no_edit": mode in NO_EDIT_MODES,
            "checkpoint_required": mode in CHECKPOINT_REQUIRED_MODES,
            "proof_production": mode in PROOF_PRODUCTION_MODES,
        },
        "build_gates": {
            "targeted_build_passed": targeted_build_passed,
            "project_build_passed": project_build_passed,
            "axiom_audit_passed": axiom_audit_passed,
        },
        "violations": [v.to_json() for v in violations],
    }


def load_files_map(path: Path | None) -> dict[str, str]:
    if path is None:
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise SystemExit(f"{path} must contain a JSON object mapping file paths to text")
    return {str(k): str(v) for k, v in payload.items()}


def write_report(path: Path | None, report: dict[str, Any]) -> None:
    text = json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    if path is None:
        print(text, end="")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", required=True, choices=sorted(WORKFLOW_MODES))
    parser.add_argument("--before-files-json", type=Path)
    parser.add_argument("--after-files-json", type=Path)
    parser.add_argument("--theorem-before", default="")
    parser.add_argument("--theorem-after", default="")
    parser.add_argument("--targeted-build-passed", action="store_true")
    parser.add_argument("--project-build-passed", action="store_true")
    parser.add_argument("--axiom-audit-passed", action="store_true")
    parser.add_argument("--allow-unsound-markers", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args(list(argv) if argv is not None else None)

    report = check_workflow_policy(
        mode=args.mode,
        before_files=load_files_map(args.before_files_json),
        after_files=load_files_map(args.after_files_json),
        theorem_before=args.theorem_before,
        theorem_after=args.theorem_after,
        targeted_build_passed=args.targeted_build_passed,
        project_build_passed=args.project_build_passed,
        axiom_audit_passed=args.axiom_audit_passed,
        allow_unsound_markers=args.allow_unsound_markers,
    )
    write_report(args.json_out, report)
    return 0 if report["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
