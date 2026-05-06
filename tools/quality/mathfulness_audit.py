#!/usr/bin/env python3
"""Unified mathfulness audit for info-geometry-lean declarations.

This gate is intentionally conservative:

* Lean/DAG declaration presence is kernel/provenance evidence, not semantic
  depth by itself.  Theorem surfaces and definition/schema surfaces are
  classified separately.
* Graph support is navigation evidence only.
* Diagnostic/lightcone/Hodge/Drazin packets are never promoted as theorem
  evidence.
* A declaration is promotable only when theorem/certificate/owner-root evidence
  is present, the trust layer is clean, and the surface is not
  vacuous/surrogate.

The script consumes repo-local artifacts when available and degrades honestly
when optional audit reports are absent.  In gate mode, missing hard audit
reports are failures rather than silent absences.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+)?"
    r"(theorem|lemma|def|abbrev|structure|inductive|axiom|opaque)\s+"
    r"([A-Za-z0-9_'.]+)"
)
TRIVIAL_PROOF_RE = re.compile(
    r":=\s*(?:by\s+)?(?:trivial|rfl|Iff\.rfl|simp!?|simpa!?)\b"
)
SORRY_RE = re.compile(r"\b(sorry|admit)\b|admitAx|sorryAx")
UNSAFE_RE = re.compile(r"\bunsafe\b")
DIAGNOSTIC_NAME_RE = re.compile(
    r"(?:lightcone|spectral|hodge|dirac|drazin.*diagnostic|training|packet|schema)",
    re.IGNORECASE,
)
TRUE_TYPE_RE = re.compile(r":\s*True\b")
CERTIFICATE_RE = re.compile(r"(?:certificate|certified|checked|verified)", re.IGNORECASE)
OWNER_ROOT_RE = re.compile(r"(?:Owner|owner|Target|target|Bridge|bridge|Context|context)")
PROMOTABLE_CLASSES = {"kernel_theorem", "certificate_backed", "owner_rooted"}
DEFAULT_GATE_BLOCK_CLASSES = {
    "blocked",
    "audit_missing",
    "vacuous_or_surrogate",
    "graph_only",
    "diagnostic_only",
    "needs_review_named_bridge",
    "kernel_definition",
    "explicit_axiom",
    "needs_review_external_audit_failed",
}


def load_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    out: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for raw in handle:
            raw = raw.strip()
            if raw:
                out.append(json.loads(raw))
    return out


def rel(path: str | Path) -> str:
    p = Path(path)
    try:
        return str(p.resolve().relative_to(ROOT))
    except Exception:
        return str(path)


def repo_path(path_value: str | Path) -> Path:
    p = Path(path_value)
    return p if p.is_absolute() else ROOT / p


def source_block(file_path: Path, line: int) -> str:
    if not file_path.exists() or line <= 0:
        return ""
    lines = file_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    start = max(0, line - 1)
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if DECL_RE.match(lines[i]):
            end = i
            break
    return "\n".join(lines[start:end])


def significance_by_name(path: Path) -> dict[str, dict[str, Any]]:
    payload = load_json(path, [])
    if isinstance(payload, dict):
        rows = (
            payload.get("rows")
            or payload.get("theorems")
            or payload.get("declarations")
            or payload.get("items")
            or []
        )
    elif isinstance(payload, list):
        rows = payload
    else:
        rows = []
    return {str(row.get("name")): row for row in rows if row.get("name")}


def policy_lint_flags(path: Path) -> dict[str, set[str]]:
    data = load_json(path, {})
    flags: dict[str, set[str]] = {}
    if not isinstance(data, dict):
        return flags
    for key in (
        "suspect_theorems",
        "new_suspect_theorems",
        "new_prop_surfaces",
        "proposition_surfaces",
        "suspectTheorems",
        "suspects",
        "vacuous",
        "violations",
    ):
        rows = data.get(key, [])
        if not isinstance(rows, list):
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            name = row.get("name") or row.get("decl") or row.get("theorem")
            if name:
                flags.setdefault(str(name), set()).add(key)
    return flags


def paranoia_flags(path: Path) -> dict[str, dict[str, Any]]:
    flags: dict[str, dict[str, Any]] = {}
    for row in load_jsonl(path):
        theorem = row.get("theorem")
        if theorem:
            flags[str(theorem)] = row
    return flags


def classify(
    decl: dict[str, Any],
    sig: dict[str, Any] | None,
    policy_flags: set[str],
    paranoia: dict[str, Any] | None,
) -> tuple[str, bool, list[str]]:
    name = str(decl.get("name", ""))
    kind = str(decl.get("kind", ""))
    file_path = repo_path(str(decl.get("file", "")))
    line = int(decl.get("line") or 0)
    block = source_block(file_path, line)
    flat_block = re.sub(r"\s+", " ", block)
    reasons: list[str] = []

    if SORRY_RE.search(block):
        reasons.append("blocked:sorry_or_admit_in_source_block")
        return "blocked", False, reasons
    if UNSAFE_RE.search(block):
        reasons.append("blocked:unsafe_in_source_block")
        return "blocked", False, reasons

    if kind == "axiom":
        reasons.append("explicit_axiom:requires_policy_approval_not_theorem")
        return "explicit_axiom", False, reasons

    if DIAGNOSTIC_NAME_RE.search(name) or DIAGNOSTIC_NAME_RE.search(rel(file_path)):
        reasons.append("diagnostic_only:name_or_file_marks_diagnostic_surface")
        return "diagnostic_only", False, reasons

    if policy_flags:
        reasons.append("vacuous_or_surrogate:policy_lint=" + ",".join(sorted(policy_flags)))
        return "vacuous_or_surrogate", False, reasons

    if TRUE_TYPE_RE.search(flat_block) and TRIVIAL_PROOF_RE.search(flat_block) and kind in {"theorem", "lemma"}:
        reasons.append("vacuous_or_surrogate:true_only_trivial_certificate")
        return "vacuous_or_surrogate", False, reasons

    if TRIVIAL_PROOF_RE.search(flat_block) and kind in {"theorem", "lemma"}:
        role = str((sig or {}).get("structural_role", ""))
        reverse_theorem_users = int((sig or {}).get("reverse_theorem_users") or 0)
        if reverse_theorem_users == 0 and role in {"isolated_theorem", "declaration", ""}:
            reasons.append("vacuous_or_surrogate:trivial_proof_without_theorem_users")
            return "vacuous_or_surrogate", False, reasons
        reasons.append("kernel_theorem:trivial_proof_but_graph_used")

    if paranoia is not None and not bool(paranoia.get("success")):
        reasons.append("needs_review_external_audit_failed:leanparanoia_not_clean")
        return "needs_review_external_audit_failed", False, reasons

    if CERTIFICATE_RE.search(name) and kind in {"theorem", "lemma", "def", "structure"}:
        reasons.append("needs_review_named_bridge:certificate_name_without_verified_certificate")
        return "needs_review_named_bridge", False, reasons

    if OWNER_ROOT_RE.search(name) and kind in {"theorem", "lemma", "def", "abbrev", "structure"}:
        reasons.append("needs_review_named_bridge:owner_or_bridge_name_without_owner_proof")
        return "needs_review_named_bridge", False, reasons

    if kind in {"theorem", "lemma"}:
        if sig is None:
            reasons.append("kernel_theorem:no_graph_significance_row")
        else:
            reasons.append("kernel_theorem:decl_index_and_graph_row_present")
        return "kernel_theorem", True, reasons

    if kind in {"def", "abbrev", "structure", "inductive", "opaque"}:
        reasons.append("kernel_definition:compiled_declaration_not_theorem")
        return "kernel_definition", False, reasons

    reasons.append("graph_only:unclassified_or_non_owner_surface")
    return "graph_only", False, reasons


def main() -> int:
    parser = argparse.ArgumentParser(description="Classify declaration mathfulness evidence.")
    parser.add_argument("--decls", type=Path, default=ROOT / "artifacts/dag/index/decls.jsonl")
    parser.add_argument("--significance", type=Path, default=ROOT / "reports/theorem-significance.json")
    parser.add_argument("--policy-lint", type=Path, default=ROOT / "reports/dag/canonical-policy-lint.json")
    parser.add_argument("--frontier-gate", type=Path, default=ROOT / "reports/dag/frontier-gate-report.json")
    parser.add_argument("--pauli-seal", type=Path, default=ROOT / "reports/pauli-seal-audit.json")
    parser.add_argument("--leanparanoia", type=Path, default=None)
    parser.add_argument("--prefix", action="append", default=[])
    parser.add_argument("--file-prefix", action="append", default=[])
    parser.add_argument("--gate", action="store_true", help="Exit nonzero if selected declarations contain blocked/nonpromotable gate classes.")
    parser.add_argument(
        "--fail-class",
        action="append",
        default=[],
        help="Classification that fails --gate. Defaults to blocked/vacuous/graph_only/diagnostic_only.",
    )
    parser.add_argument("--json-out", type=Path, default=ROOT / "reports/dag/mathfulness-audit.json")
    parser.add_argument("--md-out", type=Path, default=ROOT / "reports/dag/mathfulness-audit.md")
    args = parser.parse_args()

    decls = load_jsonl(args.decls)
    sig = significance_by_name(args.significance)
    policy = policy_lint_flags(args.policy_lint)
    paranoia = paranoia_flags(args.leanparanoia) if args.leanparanoia else {}
    frontier_present = args.frontier_gate.exists()
    pauli_present = args.pauli_seal.exists()
    global_failures: list[str] = []
    if args.gate:
        required_inputs = {
            "decls": args.decls,
            "frontier_gate": args.frontier_gate,
            "pauli_seal": args.pauli_seal,
            "policy_lint": args.policy_lint,
        }
        for label, path in required_inputs.items():
            if not path.exists():
                global_failures.append(f"missing_required_audit_input:{label}")

    selected: list[dict[str, Any]] = []
    for decl in decls:
        name = str(decl.get("name", ""))
        file_rel = rel(str(decl.get("file", "")))
        if args.prefix and not any(name.startswith(p) for p in args.prefix):
            continue
        if args.file_prefix and not any(file_rel.startswith(p) for p in args.file_prefix):
            continue
        selected.append(decl)

    rows = []
    counts: Counter[str] = Counter()
    promotable_count = 0
    for decl in selected:
        name = str(decl.get("name", ""))
        cls, promotable, reasons = classify(
            decl,
            sig.get(name),
            policy.get(name, set()),
            paranoia.get(name),
        )
        counts[cls] += 1
        promotable_count += int(promotable)
        rows.append(
            {
                "name": name,
                "kind": decl.get("kind"),
                "file": rel(str(decl.get("file", ""))),
                "line": decl.get("line"),
                "classification": cls,
                "promotable": promotable,
                "not_promotable": not promotable,
                "reasons": reasons,
                "graph": {
                    "has_significance_row": name in sig,
                    "structural_role": (sig.get(name) or {}).get("structural_role"),
                    "reverse_theorem_users": (sig.get(name) or {}).get("reverse_theorem_users"),
                    "graph_grounded_signal": (sig.get(name) or {}).get("graph_grounded_signal"),
                },
            }
        )

    report = {
        "schema": "info_geometry.mathfulness_audit.v1",
        "authority_boundary": {
            "graph_is_navigation_not_truth": True,
            "diagnostics_are_priors_not_proofs": True,
            "lean_kernel_remains_proof_authority": True,
            "true_certificate_is_not_substantive_bridge": True,
            "prompt_packet_is_not_proof": True,
        },
        "promotion_rule": "verdict in {kernel_theorem, certificate_backed, owner_rooted} && trust_clean && !vacuous_or_surrogate && !graph_only && !diagnostic_only",
        "global_failures": global_failures,
        "inputs": {
            "decls": str(args.decls),
            "significance": str(args.significance),
            "policy_lint": str(args.policy_lint),
            "frontier_gate": str(args.frontier_gate),
            "pauli_seal": str(args.pauli_seal),
            "leanparanoia": str(args.leanparanoia) if args.leanparanoia else None,
        },
        "input_presence": {
            "decls": args.decls.exists(),
            "significance": args.significance.exists(),
            "policy_lint": args.policy_lint.exists(),
            "frontier_gate": frontier_present,
            "pauli_seal": pauli_present,
            "leanparanoia": bool(args.leanparanoia and args.leanparanoia.exists()),
        },
        "filters": {
            "prefix": args.prefix,
            "file_prefix": args.file_prefix,
            "gate": args.gate,
        },
        "summary": {
            "total": len(rows),
            "promotable": promotable_count,
            "blocked_or_nonpromotable": len(rows) - promotable_count,
            "by_classification": dict(sorted(counts.items())),
        },
        "rows": rows,
    }

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.md_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    md = [
        "# Mathfulness Audit",
        "",
        "> Graph evidence establishes provenance and navigation only. Mathematical admission requires a Lean owner theorem, constructive certificate, or approved mathlib/local theorem root.",
        "> Names such as Bridge, Owner, Verified, or Certificate are review hints only; names do not promote declarations.",
        "",
        f"Total declarations: {len(rows)}",
        f"Promotable: {promotable_count}",
        f"Blocked/non-promotable: {len(rows) - promotable_count}",
        "",
        "## Classification counts",
        "",
    ]
    for key, value in sorted(counts.items()):
        md.append(f"- `{key}`: {value}")
    md += ["", "## Non-promotable rows", ""]
    for row in rows:
        if not row["promotable"]:
            md.append(f"- `{row['classification']}` `{row['name']}`: {'; '.join(row['reasons'])}")
    args.md_out.write_text("\n".join(md) + "\n", encoding="utf-8")

    print(json.dumps(report["summary"], indent=2, ensure_ascii=False))
    if args.gate:
        fail_classes = set(args.fail_class) if args.fail_class else set(DEFAULT_GATE_BLOCK_CLASSES)
        failures = [row for row in rows if row["classification"] in fail_classes]
        if not rows:
            global_failures.append("no_selected_declarations")
        if failures or global_failures:
            print(
                json.dumps(
                    {
                        "gate": "failed",
                        "fail_classes": sorted(fail_classes),
                        "global_failures": global_failures,
                        "failure_count": len(failures),
                        "first_failures": failures[:10],
                    },
                    indent=2,
                    ensure_ascii=False,
                )
            )
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
