#!/usr/bin/env python3
"""First-class Hive spec/submission lane for code-with-proof tasks.

This captures the protocol from "safe and hallucination-free coding AI":

* a target spec names declarations/signatures/stubs;
* a submission fills implementations/proofs;
* SafeVerify compares compiled target/submission environments;
* LeanParanoia audits proof-soundness/exploit surfaces;
* Hive promotion happens only after all gates agree.

The module is deliberately policy/data-contract code.  It does not replace
Lean, SafeVerify, LeanParanoia, or the build worker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable


SPEC_SCHEMA = "hive.packet.target_spec.v1"
SUBMISSION_SCHEMA = "hive.packet.submission.v1"
PROMOTION_SCHEMA = "hive.packet.spec_submission_promotion_gate.v1"

DEFAULT_ALLOWED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")
UNSOUND_MARKERS = ("sorry", "admit", "axiom")


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def unsound_marker_hits(text: str) -> list[str]:
    return [marker for marker in UNSOUND_MARKERS if re.search(rf"\b{re.escape(marker)}\b", text or "")]


def declaration_names_from_source(source: str) -> list[str]:
    names = []
    pattern = re.compile(r"\b(?:theorem|lemma|def|abbrev|opaque)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
    for match in pattern.finditer(source or ""):
        names.append(match.group(1))
    return names


def make_target_spec_packet(
    *,
    spec_id: str,
    target_file: str,
    target_source: str,
    allowed_axioms: Iterable[str] = DEFAULT_ALLOWED_AXIOMS,
    expected_declarations: Iterable[str] | None = None,
    target_olean: str | None = None,
) -> dict[str, Any]:
    expected = list(expected_declarations or declaration_names_from_source(target_source))
    packet = {
        "schema": SPEC_SCHEMA,
        "authority": "proposal",
        "spec_id": spec_id,
        "target_file": target_file,
        "target_olean": target_olean,
        "expected_declarations": expected,
        "allowed_axioms": list(allowed_axioms),
        "source_hash": stable_hash(target_source),
        "target_source": target_source,
        "unsound_markers": unsound_marker_hits(target_source),
        "authority_boundary": {
            "target_spec_is_contract": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    packet["packet_key"] = stable_hash(["target_spec", spec_id, target_file, packet["source_hash"]])
    return packet


def make_submission_packet(
    *,
    spec_id: str,
    submission_id: str,
    submission_file: str,
    submission_source: str,
    submission_olean: str | None = None,
    model: str | None = None,
    provenance: dict[str, Any] | None = None,
) -> dict[str, Any]:
    packet = {
        "schema": SUBMISSION_SCHEMA,
        "authority": "proposal",
        "spec_id": spec_id,
        "submission_id": submission_id,
        "submission_file": submission_file,
        "submission_olean": submission_olean,
        "model": model,
        "provenance": provenance or {},
        "source_hash": stable_hash(submission_source),
        "submission_source": submission_source,
        "declared_declarations": declaration_names_from_source(submission_source),
        "unsound_markers": unsound_marker_hits(submission_source),
        "authority_boundary": {
            "submission_is_candidate": True,
            "not_a_proof_until_lean_checked": True,
            "lean_remains_proof_authority": True,
        },
    }
    packet["packet_key"] = stable_hash(["submission", spec_id, submission_id, submission_file, packet["source_hash"]])
    return packet


def validate_spec_submission_pair(spec: dict[str, Any], submission: dict[str, Any]) -> list[dict[str, str]]:
    violations: list[dict[str, str]] = []
    if spec.get("schema") != SPEC_SCHEMA:
        violations.append({"code": "invalid_spec_schema", "message": "target spec packet has wrong schema"})
    if submission.get("schema") != SUBMISSION_SCHEMA:
        violations.append({"code": "invalid_submission_schema", "message": "submission packet has wrong schema"})
    if spec.get("spec_id") != submission.get("spec_id"):
        violations.append({"code": "spec_id_mismatch", "message": "target spec and submission have different spec_id"})
    if submission.get("unsound_markers"):
        violations.append({"code": "submission_unsound_markers", "message": "submission contains sorry/admit/axiom markers"})
    missing = sorted(set(spec.get("expected_declarations") or []) - set(submission.get("declared_declarations") or []))
    if missing:
        violations.append({"code": "missing_expected_declarations", "message": ",".join(missing)})
    return violations


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def load_audit_rows(path: Path | None) -> list[dict[str, Any]]:
    if path is None:
        return []
    if path.is_file() and path.suffix.lower() == ".jsonl":
        return list(iter_jsonl(path))
    if path.is_file() and path.suffix.lower() == ".json":
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, list):
            return [row for row in payload if isinstance(row, dict)]
        if isinstance(payload, dict):
            return [payload]
    return []


def promotion_gate(
    *,
    spec: dict[str, Any],
    submission: dict[str, Any],
    build_passed: bool,
    leanparanoia_rows: list[dict[str, Any]],
    safeverify_rows: list[dict[str, Any]],
    autograder_rows: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    violations = validate_spec_submission_pair(spec, submission)
    if not build_passed:
        violations.append({"code": "build_not_passed", "message": "submission build gate did not pass"})
    if not leanparanoia_rows:
        violations.append({"code": "missing_leanparanoia_audit", "message": "LeanParanoia audit rows are required"})
    elif any(not bool(row.get("success")) for row in leanparanoia_rows):
        violations.append({"code": "leanparanoia_failed", "message": "one or more LeanParanoia audit rows failed"})
    if not safeverify_rows:
        violations.append({"code": "missing_safeverify_audit", "message": "SafeVerify audit rows are required"})
    elif any(not bool(row.get("success")) for row in safeverify_rows):
        violations.append({"code": "safeverify_failed", "message": "one or more SafeVerify audit rows failed"})
    autograder_rows = autograder_rows or []
    if any(not bool(row.get("passed")) for row in autograder_rows):
        violations.append({"code": "autograder_failed", "message": "one or more Lean autograder reports failed"})

    packet = {
        "schema": PROMOTION_SCHEMA,
        "authority": "audit_checked" if not violations else "proposal",
        "spec_id": spec.get("spec_id"),
        "submission_id": submission.get("submission_id"),
        "target_spec_key": spec.get("packet_key"),
        "submission_key": submission.get("packet_key"),
        "build_passed": build_passed,
        "leanparanoia_records": len(leanparanoia_rows),
        "safeverify_records": len(safeverify_rows),
        "autograder_records": len(autograder_rows),
        "autograder_points": {
            "earned": sum(float(row.get("earned_points") or 0) for row in autograder_rows),
            "total": sum(float(row.get("total_points") or 0) for row in autograder_rows),
        },
        "promotion_allowed": not violations,
        "violations": violations,
        "authority_boundary": {
            "promotion_gate_is_policy": True,
            "does_not_replace_lean": True,
            "requires_build_paranoia_and_safeverify": True,
        },
    }
    packet["packet_key"] = stable_hash(
        [
            "spec_submission_gate",
            packet["spec_id"],
            packet["submission_id"],
            build_passed,
            [row.get("id") for row in leanparanoia_rows],
            [row.get("id") for row in safeverify_rows],
            [row.get("id") for row in autograder_rows],
        ]
    )
    return packet


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_spec = sub.add_parser("target-spec")
    p_spec.add_argument("--spec-id", required=True)
    p_spec.add_argument("--target-file", type=Path, required=True)
    p_spec.add_argument("--target-olean")
    p_spec.add_argument("--expected-declaration", action="append", default=[])
    p_spec.add_argument("--out", type=Path, required=True)

    p_sub = sub.add_parser("submission")
    p_sub.add_argument("--spec-id", required=True)
    p_sub.add_argument("--submission-id", required=True)
    p_sub.add_argument("--submission-file", type=Path, required=True)
    p_sub.add_argument("--submission-olean")
    p_sub.add_argument("--model")
    p_sub.add_argument("--out", type=Path, required=True)

    p_gate = sub.add_parser("promotion-gate")
    p_gate.add_argument("--spec-packet", type=Path, required=True)
    p_gate.add_argument("--submission-packet", type=Path, required=True)
    p_gate.add_argument("--build-passed", action="store_true")
    p_gate.add_argument("--leanparanoia-jsonl", type=Path)
    p_gate.add_argument("--safeverify-jsonl", type=Path)
    p_gate.add_argument("--autograder-jsonl", type=Path)
    p_gate.add_argument("--out", type=Path, required=True)

    args = parser.parse_args()
    if args.cmd == "target-spec":
        source = args.target_file.read_text(encoding="utf-8")
        packet = make_target_spec_packet(
            spec_id=args.spec_id,
            target_file=str(args.target_file),
            target_source=source,
            target_olean=args.target_olean,
            expected_declarations=args.expected_declaration or None,
        )
        write_json(args.out, packet)
        print(json.dumps({"schema": SPEC_SCHEMA + ".summary", "out": str(args.out)}, sort_keys=True))
        return 0
    if args.cmd == "submission":
        source = args.submission_file.read_text(encoding="utf-8")
        packet = make_submission_packet(
            spec_id=args.spec_id,
            submission_id=args.submission_id,
            submission_file=str(args.submission_file),
            submission_source=source,
            submission_olean=args.submission_olean,
            model=args.model,
        )
        write_json(args.out, packet)
        print(json.dumps({"schema": SUBMISSION_SCHEMA + ".summary", "out": str(args.out)}, sort_keys=True))
        return 0
    spec = load_json(args.spec_packet)
    submission = load_json(args.submission_packet)
    packet = promotion_gate(
        spec=spec,
        submission=submission,
        build_passed=bool(args.build_passed),
        leanparanoia_rows=load_audit_rows(args.leanparanoia_jsonl),
        safeverify_rows=load_audit_rows(args.safeverify_jsonl),
        autograder_rows=load_audit_rows(args.autograder_jsonl),
    )
    write_json(args.out, packet)
    print(json.dumps({"schema": PROMOTION_SCHEMA + ".summary", "promotion_allowed": packet["promotion_allowed"], "out": str(args.out)}, sort_keys=True))
    return 0 if packet["promotion_allowed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
