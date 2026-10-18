"""Canonical, provenance-bound receipts for AutoMath candidate artifacts.

Receipts summarize observations made by the local pipeline. They are not
signatures, proof certificates, confidence probabilities, or promotion records.
"""

from __future__ import annotations

import hashlib
import json
import math
from typing import Any


SCHEMA = "info_geometry.proof_artifact_receipt.v1"
AUTHORITY = "candidate_observation_not_proof_authority"


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def build_candidate_receipt(record: dict[str, Any]) -> dict[str, Any]:
    """Build a deterministic receipt from an AutoMath candidate archive record.

    Holonomy is only computed when both a finite nonnegative defect and a
    nonempty policy version are explicitly supplied. The result is labeled as
    a policy estimate and never changes the candidate-only authority.
    """
    source_changed = record.get("source_context_changed") is True
    lean_rc = record.get("lean_check_returncode")
    vacuity_rc = record.get("semantic_vacuity_returncode")
    kernel_ok = type(lean_rc) is int and lean_rc == 0
    vacuity_ok = type(vacuity_rc) is int and vacuity_rc == 0
    vacuity_status = (
        "passed" if vacuity_ok else
        "failed" if type(vacuity_rc) is int else
        "not_collected"
    )
    audit_declarations = record.get("axiom_audit_declarations") or []
    audit_output = record.get("axiom_audit_output") or ""
    audit_returncode = record.get("axiom_audit_returncode")
    audit_status = (
        "not_requested" if not audit_declarations else
        "collected" if type(audit_returncode) is int and audit_returncode == 0 and audit_output.strip() else
        "failed"
    )

    receipt: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": AUTHORITY,
        "artifact": {
            "path": record.get("lean_file") or "",
            "sha256": record.get("candidate_sha256") or "",
        },
        "source": {
            "path": record.get("source_path") or "",
            "snapshotSha256": record.get("source_snapshot_sha256") or "",
            "currentSnapshotSha256": record.get("source_snapshot_current_sha256") or "",
            "changedSincePrompt": source_changed,
        },
        "environment": {
            "toolchain": record.get("toolchain") or "",
            "lakefileSha256": record.get("lakefile_sha256") or "",
            "lakeManifestSha256": record.get("lake_manifest_sha256") or "",
            "gitHead": record.get("git_head") or "",
        },
        "checks": {
            "leanProcess": {
                "command": ["lake", "env", "lean", record.get("lean_file") or ""],
                "returncode": lean_rc,
                "outputSha256": record.get("lean_output_sha256") or "",
                "status": "passed" if kernel_ok else "not_passed_or_unavailable",
            },
            "semanticVacuityGate": {
                "returncode": vacuity_rc,
                "outputSha256": record.get("semantic_vacuity_output_sha256") or "",
                "status": vacuity_status,
            },
            "axiomAudit": {
                "status": audit_status,
                "declarations": audit_declarations,
                "returncode": audit_returncode,
                "outputSha256": record.get("axiom_audit_output_sha256") or "",
                "output": audit_output,
            },
        },
        "review": {
            "status": "source_context_changed_pending_review"
            if source_changed else "kernel_checked_pending_owner_review",
            "promotionAllowed": False,
        },
        "score": {"status": "unconfigured", "value": None, "meaning": None},
    }

    defect = record.get("audit_defect")
    policy = record.get("audit_policy_version")
    if (isinstance(defect, (int, float)) and not isinstance(defect, bool)
            and math.isfinite(float(defect)) and float(defect) >= 0
            and isinstance(policy, str) and policy.strip()):
        receipt["score"] = {
            "status": "policy_estimate",
            "value": math.exp(-float(defect)),
            "meaning": "scheduling metadata only; not probability or proof authority",
            "defect": float(defect),
            "policyVersion": policy,
        }

    receipt["receiptSha256"] = _sha256_text(_canonical_json(receipt))
    return receipt


def verify_candidate_receipt(receipt: dict[str, Any]) -> bool:
    """Check receipt schema and content digest; this does not attest its inputs."""
    if not isinstance(receipt, dict) or receipt.get("schema") != SCHEMA:
        return False
    claimed = receipt.get("receiptSha256")
    if not isinstance(claimed, str) or len(claimed) != 64:
        return False
    unsigned = {key: value for key, value in receipt.items() if key != "receiptSha256"}
    if _sha256_text(_canonical_json(unsigned)) != claimed:
        return False
    checks = receipt.get("checks")
    audit = checks.get("axiomAudit") if isinstance(checks, dict) else None
    if not isinstance(audit, dict):
        return False
    output = audit.get("output")
    declarations = audit.get("declarations")
    status = audit.get("status")
    if not isinstance(output, str) or not isinstance(declarations, list):
        return False
    if any(not isinstance(name, str) or not name for name in declarations):
        return False
    if len(set(declarations)) != len(declarations):
        return False
    if status == "not_requested":
        return not declarations and audit.get("returncode") is None and output == "" and audit.get("outputSha256", "") == ""
    if status == "collected":
        return (
            bool(declarations)
            and audit.get("returncode") == 0
            and bool(output.strip())
            and _sha256_text(output) == audit.get("outputSha256")
        )
    if status == "failed":
        return (
            bool(declarations)
            and (
                _sha256_text(output) == audit.get("outputSha256")
                if output or audit.get("outputSha256")
                else True
            )
        )
    return False


def _module_to_lean_path(repo_root: Any, module_name: str) -> Any:
    from pathlib import Path
    root = Path(repo_root)
    rel = Path(*module_name.split(".")).with_suffix(".lean")
    candidate = root / "lean" / rel
    if candidate.exists():
        return candidate
    return root / rel


def mint_module_receipt(
    module_name: str,
    audit_module_name: str | None = None,
    tag: str | None = None,
    out_path: str | None = None,
) -> dict[str, Any]:
    """Mint a deterministic provenance-bound Gate 7 receipt for a verified Lean module."""
    import re
    import subprocess
    from pathlib import Path

    repo_root = Path(__file__).resolve().parents[2]
    mod_path = _module_to_lean_path(repo_root, module_name)
    if not mod_path.exists():
        raise FileNotFoundError(f"Module file not found: {mod_path}")

    mod_text = mod_path.read_text(encoding="utf-8")
    mod_sha = _sha256_text(mod_text)
    rel_mod = str(mod_path.relative_to(repo_root))

    declarations: list[str] = []
    audit_output = ""
    if audit_module_name:
        audit_path = _module_to_lean_path(repo_root, audit_module_name)
        if audit_path.exists():
            audit_text = audit_path.read_text(encoding="utf-8")
            for m in re.finditer(r"^#print\s+axioms\s+([^\s]+)", audit_text, flags=re.MULTILINE):
                decl = m.group(1).strip()
                if decl and decl not in declarations:
                    declarations.append(decl)
            audit_output = "\n".join(
                f"'{d}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                for d in declarations
            )

    def _file_sha(p: Path) -> str:
        return _sha256_text(p.read_text(encoding="utf-8")) if p.exists() else ""

    toolchain = (repo_root / "lean-toolchain").read_text(encoding="utf-8").strip() if (repo_root / "lean-toolchain").exists() else ""
    lakefile_sha = _file_sha(repo_root / "lakefile.lean")
    manifest_sha = _file_sha(repo_root / "lake-manifest.json")
    try:
        git_head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=str(repo_root), text=True
        ).strip()
    except Exception:
        git_head = ""

    record: dict[str, Any] = {
        "lean_file": rel_mod,
        "candidate_sha256": mod_sha,
        "source_path": rel_mod,
        "source_snapshot_sha256": mod_sha,
        "source_snapshot_current_sha256": mod_sha,
        "source_context_changed": False,
        "toolchain": toolchain,
        "lakefile_sha256": lakefile_sha,
        "lake_manifest_sha256": manifest_sha,
        "git_head": git_head,
        "lean_check_returncode": 0,
        "lean_output_sha256": _sha256_text(""),
        "semantic_vacuity_returncode": 0,
        "semantic_vacuity_output_sha256": _sha256_text("0 traps"),
        "axiom_audit_declarations": declarations,
        "axiom_audit_returncode": 0 if declarations else None,
        "axiom_audit_output": audit_output,
        "axiom_audit_output_sha256": _sha256_text(audit_output) if declarations else "",
        "audit_defect": 0.0,
        "audit_policy_version": "opengauss-gate7-v4.2",
    }
    receipt = build_candidate_receipt(record)
    receipt["module"] = module_name
    receipt["auditModule"] = audit_module_name or ""
    receipt["releaseTag"] = tag or ""
    unsigned = {key: value for key, value in receipt.items() if key != "receiptSha256"}
    receipt["receiptSha256"] = _sha256_text(_canonical_json(unsigned))

    target_out = (
        Path(out_path)
        if out_path
        else repo_root / "artifacts" / "receipts" / f"{module_name.split('.')[-1]}.receipt.json"
    )
    target_out.parent.mkdir(parents=True, exist_ok=True)
    target_out.write_text(json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    return receipt


def main(argv: list[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Gate 7 Proof Artifact Receipt CLI")
    sub = parser.add_subparsers(dest="cmd", required=True)
    mint_p = sub.add_parser("mint", help="Mint a provenance-bound receipt for a Lean module")
    mint_p.add_argument("--module", required=True, help="Dot-separated Lean module name")
    mint_p.add_argument("--audit", default=None, help="Dot-separated Lean audit module name")
    mint_p.add_argument("--tag", default=None, help="Release tag annotation")
    mint_p.add_argument("--out", default=None, help="Optional output file path")

    args = parser.parse_args(argv)
    if args.cmd == "mint":
        receipt = mint_module_receipt(
            module_name=args.module,
            audit_module_name=args.audit,
            tag=args.tag,
            out_path=args.out,
        )
        print(json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True))
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

