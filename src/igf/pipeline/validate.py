from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

from igf.policy.claim_scope import validate_claim_policy


SCHEMA_TO_FILE = {
    "ig.patch_run.v1": "ig_patch_run.v1.json",
    "ig.chiral_patch.v1.2": "ig_chiral_patch.v1.2.json",
    "ig.patch_spectral_signature.v1.2": "ig_patch_spectral_signature.v1.2.json",
    "ig.patch_member.v1": "ig_patch_member.v1.json",
    "ig.patch_edge.v1": "ig_patch_edge.v1.json",
}

ARTIFACT_FILES = {
    "ig_patch_runs.jsonl": "ig.patch_run.v1",
    "ig_chiral_patches.jsonl": "ig.chiral_patch.v1.2",
    "ig_patch_spectral_signatures.jsonl": "ig.patch_spectral_signature.v1.2",
    "ig_patch_members.jsonl": "ig.patch_member.v1",
    "ig_patch_edges.jsonl": "ig.patch_edge.v1",
}

POLICY_ARTIFACT_FILES = {
    "ig_patch_runs.jsonl",
    "ig_chiral_patches.jsonl",
    "ig_patch_spectral_signatures.jsonl",
}


def _load_schema(path: Path) -> Draft202012Validator:
    with path.open("r", encoding="utf-8") as f:
        schema = json.load(f)
    return Draft202012Validator(schema)


def validate_artifacts(artifact_dir: Path, schemas_dir: Path, *, strict: bool = False, max_errors: int = 200) -> dict[str, Any]:
    errors: list[dict[str, Any]] = []
    checked = 0

    validators: dict[str, Draft202012Validator] = {}
    for schema_id, schema_file in SCHEMA_TO_FILE.items():
        validators[schema_id] = _load_schema(schemas_dir / schema_file)

    for artifact_file, schema_id in ARTIFACT_FILES.items():
        path = artifact_dir / artifact_file
        if not path.exists():
            errors.append({"file": artifact_file, "line": 0, "error": "missing_artifact_file"})
            continue
        validator = validators[schema_id]
        with path.open("r", encoding="utf-8") as f:
            for idx, line in enumerate(f, start=1):
                line = line.strip()
                if not line:
                    continue
                checked += 1
                try:
                    obj = json.loads(line)
                except json.JSONDecodeError as exc:
                    errors.append({"file": artifact_file, "line": idx, "error": f"invalid_json: {exc}"})
                    continue
                row_schema_version = obj.get("schema_version")
                if strict and row_schema_version and row_schema_version != schema_id:
                    errors.append(
                        {
                            "file": artifact_file,
                            "line": idx,
                            "error": f"schema_version_mismatch row={row_schema_version} expected={schema_id}",
                        }
                    )
                if strict:
                    for e in validator.iter_errors(obj):
                        errors.append(
                            {
                                "file": artifact_file,
                                "line": idx,
                                "error": e.message,
                                "path": "/".join(str(p) for p in e.path),
                            }
                        )
                    if artifact_file in POLICY_ARTIFACT_FILES:
                        for policy_error in validate_claim_policy(obj):
                            errors.append(
                                {
                                    "file": artifact_file,
                                    "line": idx,
                                    "error": policy_error,
                                    "path": "claim_policy",
                                }
                            )
                if len(errors) >= max_errors:
                    return {
                        "ok": False,
                        "checked_rows": checked,
                        "error_count": len(errors),
                        "errors": errors,
                        "truncated": True,
                    }

    return {
        "ok": len(errors) == 0,
        "checked_rows": checked,
        "error_count": len(errors),
        "errors": errors[:200],
    }
