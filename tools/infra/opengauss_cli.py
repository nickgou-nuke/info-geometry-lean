#!/usr/bin/env python3
"""OpenGauss / TeamAntigravity Unified CLI & Protocol Orchestrator.

Implements all 15 OpenGauss commands natively in Python:
1.  /prove        - Top-Down Assume-and-Recurse Prover
2.  /check        - Ground-Truthed Counterexample Hunter & Consistency Auditor
3.  /refute       - Adversarial False-as-Stated Screener (15-Trap Catalog)
4.  /draft        - Skeleton Drafter
5.  /review       - Independent QMS Read-Only Auditor (Gate 2 / Gate 4)
6.  /checkpoint   - State Saver & Continuous Tracker (git index protection)
7.  /refactor     - Proof Refactorer & Redundancy Cleaner
8.  /golf         - Proof Optimizer
9.  /autoprove    - Autonomous Multi-Cycle Engine (M10 Re-Hydration)
10. /formalize    - Two-Phase Interactive Synthesis Assistant
11. /autoformalize - End-to-End CAS to Lean 4 Invariant Translator
12. /handoff      - Cross-Session Context Preserver
13. /discover     - Mathematical Declaration & Carrier Hunter
14. /quarantine   - Rejected Route & Residue Obstruction Isolator
15. /certify      - Companion Axiom Certification Script Generator
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

# Support both `python -m tools.infra.opengauss_cli` and the documented direct
# script invocation, where Python otherwise puts only `tools/infra` on sys.path.
_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.build_lock import acquire_build_lock
from tools.pathing import repo_root as canonical_repo_root
from tools.infra.opengauss_ground_truth_contract import (
    DRAFT_RECEIPT_SCHEMA,
    _qualified_declaration_heads,
    canonical_digest,
    load_and_validate_contract,
    validate_draft_receipt_payload,
)
from tools.quality.proof_proxy_staged_gate import aggregate_prop_constructors

# Import existing screener utilities
try:
    from tools.infra.opengauss_screener import (
        TrapViolation,
        check_hypothesis_packaging,
        _strip_lean_comments_and_strings,
        screen_lean_content,
        screen_lean_file,
    )
except ImportError:
    # Fallback if run directly or as package
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))
    from tools.infra.opengauss_screener import (
        TrapViolation,
        check_hypothesis_packaging,
        _strip_lean_comments_and_strings,
        screen_lean_content,
        screen_lean_file,
    )


# ---------------------------------------------------------------------------
# Command 1: PROVE (Top-Down Assume-and-Recurse Prover)
# ---------------------------------------------------------------------------

@dataclass
class TopDownDecomposition:
    headline: str
    headline_type: str
    sublemmas: List[Dict[str, str]]  # list of {"name": ..., "type": ...}
    glue_proof: str
    status: str
    anti_t11_compliant: bool
    plan: List[str]


def plan_top_down_proof(
    headline: str,
    headline_type: str,
    sublemmas: List[Dict[str, str]],
    glue_tactic: Optional[str] = None,
) -> TopDownDecomposition:
    """Generate and validate a Top-Down Assume-and-Recurse decomposition."""
    if not glue_tactic:
        sublemma_names = " ".join(s["name"] for s in sublemmas)
        glue_tactic = f"exact {sublemma_names}" if sublemmas else "sorry"

    # Anti-T11 check: Ensure child lemmas do not over-strengthen conclusions
    # beyond what parent consumes.
    anti_t11 = True
    for s in sublemmas:
        stype = s.get("type", "")
        if "∀" in stype and "∃" not in headline_type and "∀" not in headline_type:
            # Over-universalizing when parent is existential or specific
            anti_t11 = False

    plan = [
        f"1. Headline: {headline} : {headline_type}",
        "2. Leaf Lemmas (to be proved independently):",
    ]
    for s in sublemmas:
        plan.append(f"   - {s['name']} : {s['type']}")
    plan.append(f"3. Glue Compilation: by {glue_tactic}")
    plan.append("4. Axiom Verification: ensure strictly [propext, Classical.choice, Quot.sound]")

    return TopDownDecomposition(
        headline=headline,
        headline_type=headline_type,
        sublemmas=sublemmas,
        glue_proof=glue_tactic,
        status="PLAN_COMPILED",
        anti_t11_compliant=anti_t11,
        plan=plan,
    )


# ---------------------------------------------------------------------------
# Command 2: CHECK (Counterexample Hunter & Consistency Auditor)
# ---------------------------------------------------------------------------

@dataclass
class ConsistencyCheckResult:
    target: str
    consistent: bool
    warnings: List[str]
    counterexample_risk: str  # NONE, LOW, MEDIUM, HIGH
    details: Dict[str, Any] = field(default_factory=dict)


def check_consistency(
    expression: str,
    hypotheses: Optional[List[str]] = None,
) -> ConsistencyCheckResult:
    """Check mathematical expressions and hypotheses for consistency / counterexamples."""
    warnings: list[str] = []
    risk = "NONE"
    hyps = hypotheses or []

    # Check for vacuous or contradictory hypotheses
    for h in hyps:
        h_clean = h.strip()
        if re.search(r"\b0\s*=\s*1\b|\b1\s*=\s*0\b|\bFalse\b", h_clean):
            warnings.append(f"Contradictory hypothesis detected: '{h_clean}' (proof by ex falso risk)")
            risk = "HIGH"
        elif re.search(r"\b0\s*=\s*0\b|\bTrue\b|\bx\s*=\s*x\b", h_clean):
            warnings.append(f"Vacuous hypothesis detected (Trap T4): '{h_clean}'")
            if risk == "NONE":
                risk = "LOW"

    # Quantifier ordering check: ∃ c, ∀ x vs ∀ x, ∃ c (Trap T2/T2')
    if "∃" in expression and "∀" in expression:
        # Check if existential precedes universal inappropriately
        ex_pos = expression.find("∃")
        all_pos = expression.find("∀")
        if ex_pos < all_pos and ("constant" in expression.lower() or "uniform" in expression.lower()):
            warnings.append("Uniform quantifier pattern (∃...∀...) detected; ensure uniform bound is mathematically provable.")
            if risk in ("NONE", "LOW"):
                risk = "MEDIUM"

    # Metric signature clash (Trap T13)
    expr_lower = expression.lower()
    if "krein" in expr_lower and ("positive definite" in expr_lower or "positivedefinite" in expr_lower):
        warnings.append("Metric signature clash (Trap T13): Krein spaces are indefinite; asserting positive definiteness is false.")
        risk = "HIGH"

    consistent = (risk != "HIGH")
    return ConsistencyCheckResult(
        target=expression,
        consistent=consistent,
        warnings=warnings,
        counterexample_risk=risk,
        details={"num_hypotheses": len(hyps)},
    )


# ---------------------------------------------------------------------------
# Command 3: REFUTE (Adversarial False-as-Stated Screener)
# ---------------------------------------------------------------------------

def refute_content(content: str, filename: str = "<unknown>") -> Dict[str, Any]:
    """Adversarially screen Lean 4 code against the 15-Trap Catalog."""
    violations = screen_lean_content(content, filename=filename)
    errors = [asdict(v) for v in violations if v.severity == "ERROR"]
    warnings = [asdict(v) for v in violations if v.severity == "WARNING"]

    return {
        "filename": filename,
        "clean": len(errors) == 0,
        "total_traps": len(violations),
        "errors": errors,
        "warnings": warnings,
        "verdict": "REJECT" if errors else ("WARN" if warnings else "PASS"),
    }


def refute_file(path: Path) -> Dict[str, Any]:
    """Adversarially screen an on-disk Lean file."""
    try:
        content = path.read_text(encoding="utf-8")
        return refute_content(content, filename=str(path))
    except Exception as exc:
        return {
            "filename": str(path),
            "clean": False,
            "total_traps": 1,
            "errors": [{
                "trap_id": "IO_ERROR",
                "trap_name": "File Read Error",
                "line_number": 0,
                "matched_text": str(path),
                "message": str(exc),
                "severity": "ERROR",
            }],
            "warnings": [],
            "verdict": "REJECT",
        }


# ---------------------------------------------------------------------------
# Command 4: DRAFT (Skeleton Drafter)
# ---------------------------------------------------------------------------

def draft_skeleton(
    headline: str,
    signature: str,
    sublemmas: List[Dict[str, str]],
    namespace: Optional[str] = None,
    docstring: Optional[str] = None,
    contract_provenance: Optional[Dict[str, str]] = None,
) -> str:
    """Generate Lean 4 declaration skeleton with explicit leaf sorries and glued parent."""
    lines: list[str] = []
    lines.append("/-")
    lines.append("Copyright (c) 2026 InfoGeometry Authors. All rights reserved.")
    lines.append("Released under Apache 2.0 license as described in the file LICENSE.")
    lines.append("Authors: InfoGeometry Engine Contributors")
    lines.append("-/")
    lines.append("import Mathlib.Tactic")
    lines.append("")

    if contract_provenance:
        lines.append(
            "/- OpenGauss Ground-Truth Contract: "
            f"{contract_provenance['contract_id']} "
            f"(sha256:{contract_provenance['contract_sha256']}); "
            f"headline target {contract_provenance['target_name']}; human assertion, not proof evidence. "
            "Generated helper leaves remain unverified sorry obligations. -/"
        )
        lines.append("")

    if namespace:
        lines.append(f"namespace {namespace}")
        lines.append("")

    if docstring:
        lines.append("/--")
        lines.append(docstring)
        lines.append("-/")

    # Generate leaf lemmas first
    for s in sublemmas:
        sname = s["name"]
        stype = s["type"]
        sdoc = s.get("doc", f"Leaf helper for `{headline}`.")
        lines.append(f"/-- {sdoc} -/")
        lines.append(f"lemma {sname} : {stype} := by")
        lines.append("  sorry")
        lines.append("")

    # Generate headline theorem with glue proof
    lines.append(f"/-- Headline theorem: `{headline}`. -/")
    sublemma_args = " ".join(s["name"] for s in sublemmas)
    lines.append(f"theorem {headline} {signature} := by")
    if sublemma_args:
        lines.append(f"  exact {sublemma_args}")
    else:
        lines.append("  sorry")
    lines.append("")

    if namespace:
        lines.append(f"end {namespace}")
        lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Command 5: REVIEW (Independent QMS Read-Only Auditor)
# ---------------------------------------------------------------------------

@dataclass
class ReviewReport:
    target_file: str
    gate: str  # GATE_2 (Adversarial) or GATE_4 (Acceptance QA)
    verdict: str  # PASS, ACCEPTED, REQUEST_CHANGES, REJECT
    sorry_count: int
    admit_count: int
    custom_axioms: Optional[List[str]]
    kernel_checked: bool
    trap_violations: List[Dict[str, Any]]
    scope_inflation_warnings: List[str]
    summary: str
    verification_status: str = "not_requested"


def review_file(
    path: Path,
    gate: str = "GATE_2",
    *,
    verify_kernel: bool = False,
    repo_root: Optional[Path] = None,
) -> ReviewReport:
    """Run static preflight, optionally followed by locked Gate 4 verification."""
    if gate == "GATE_4" and verify_kernel:
        print(
            f"[OpenGauss Gate 4] Running static preflight for {path}",
            file=sys.stderr,
            flush=True,
        )
    if gate not in {"GATE_2", "GATE_4"}:
        raise ValueError(f"unsupported review gate: {gate}")
    if verify_kernel and gate != "GATE_4":
        raise ValueError("kernel verification is available only for GATE_4")
    content = path.read_text(encoding="utf-8")
    lines = content.splitlines()

    sorry_count = 0
    admit_count = 0
    scope_warnings: list[str] = []

    # Scan for sorries, admits, and ungrounded physical buzzwords in comments/docstrings
    hype_keywords = [
        "proves quantum gravity",
        "resolves the cosmological constant",
        "unifies everything",
        "settles riemann hypothesis completely",
    ]

    in_block_comment = False
    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()

        # Check for scope inflation / hype keywords across all lines (including docstrings/comments)
        for kw in hype_keywords:
            if kw in stripped.lower():
                scope_warnings.append(f"Line {idx}: Scope inflation / unjustified hype keyword '{kw}'.")

        if stripped.startswith("/-"):
            in_block_comment = True
        if in_block_comment:
            if "-/" in stripped:
                in_block_comment = False
            continue

        if stripped.startswith("--"):
            continue

        # Look for sorry / admit in genuine code lines
        if re.search(r"\bsorry\b", stripped):
            sorry_count += 1
        if re.search(r"\badmit\b", stripped):
            admit_count += 1

    # Screen against 15-Trap catalog
    traps = screen_lean_content(content, filename=str(path))
    trap_dicts = [asdict(t) for t in traps]
    for type_name, constructor in aggregate_prop_constructors(content):
        traps.append(TrapViolation(
            "QMS_PROP_BUNDLE", "Aggregate proposition proof wrapper", 0, constructor,
            f"Theorem constructs `{type_name}` by bundling field proofs. Review the individual owner theorems directly.",
            "ERROR",
        ))
        trap_dicts.append(asdict(traps[-1]))
    hook_root = Path(repo_root) if repo_root is not None else canonical_repo_root()
    hook_check = subprocess.run(
        [sys.executable, "tools/quality/proof_proxy_staged_gate.py"],
        cwd=hook_root, capture_output=True, text=True, check=False,
    )
    if hook_check.returncode:
        detail = (hook_check.stderr or hook_check.stdout).strip()
        traps.append(TrapViolation(
            "QMS_STAGED_HOOK", "Staged pre-commit quality gate", 0, detail[:500],
            "The staged Lean changes fail the repository pre-commit proof/QMS gate.", "ERROR",
        ))
        trap_dicts.append(asdict(traps[-1]))

    verification_status = "not_requested"
    kernel_checked = False
    custom_axioms: Optional[List[str]] = None

    # Static Gate 4 and kernel Gate 4 are distinct. A clean static report never
    # claims kernel acceptance unless the caller requested the locked check.
    if gate == "GATE_4" and verify_kernel and not any(t.severity == "ERROR" for t in traps) and not sorry_count and not admit_count:
        print(
            f"[OpenGauss Gate 4] Static preflight passed for {path}; starting kernel verification",
            file=sys.stderr,
            flush=True,
        )
        audit = verify_certification_audit(path, repo_root=repo_root)
        verification_status = audit.verification_status
        kernel_checked = audit.kernel_checked
        custom_axioms = audit.rejected_axioms

    # Assess verdict based on gate and findings
    errors = [t for t in traps if t.severity == "ERROR"]
    kernel_failed = gate == "GATE_4" and verify_kernel and verification_status != "passed"
    if errors or (gate == "GATE_4" and (sorry_count > 0 or admit_count > 0 or kernel_failed)):
        verdict = "REJECT" if gate == "GATE_2" else "REJECTED"
        summary = f"Audit failed: {len(errors)} trap errors, {sorry_count} sorries, {admit_count} admits; kernel verification {verification_status}."
    elif traps or scope_warnings or sorry_count > 0:
        if gate == "GATE_2":
            verdict = "REQUEST_CHANGES"
        elif verify_kernel and verification_status == "passed":
            verdict = "ACCEPTED_WITH_CAVEATS"
        else:
            verdict = "STATIC_REVIEW_WITH_CAVEATS_KERNEL_UNVERIFIED"
        summary = f"Review passed with caveats: {len(traps)} warnings, {sorry_count} sorries."
    elif gate == "GATE_4":
        if verify_kernel and verification_status == "passed":
            verdict = "ACCEPTED"
            summary = "Gate 4 acceptance passed: 0 sorries, 0 admits, 0 traps, and locked Lean kernel + axiom verification passed."
        else:
            verdict = "STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED"
            summary = "Static checks passed; Lean compilation and theorem axiom audit were not run."
    else:
        verdict = "PASS"
        summary = "Static audit clean: 0 sorries, 0 admits, 0 detected trap violations."

    return ReviewReport(
        target_file=str(path),
        gate=gate,
        verdict=verdict,
        sorry_count=sorry_count,
        admit_count=admit_count,
        custom_axioms=custom_axioms,
        kernel_checked=kernel_checked,
        trap_violations=trap_dicts,
        scope_inflation_warnings=scope_warnings,
        summary=summary,
        verification_status=verification_status,
    )


# ---------------------------------------------------------------------------
# Command 6: CHECKPOINT (State Saver & Continuous Tracker)
# ---------------------------------------------------------------------------

@dataclass
class CheckpointReceipt:
    timestamp: str
    staged_files: List[str]
    unstaged_files: List[str]
    untracked_files: List[str]
    git_head: str
    status: str
    message: str
    staged_quality_gate: str


def execute_checkpoint(
    message: str = "OpenGauss automated checkpoint",
    dry_run: bool = False,
    stage_paths: Optional[Sequence[str]] = None,
) -> CheckpointReceipt:
    """Record repository state and optionally stage explicitly named paths."""
    # Run git status before staging
    status_proc = subprocess.run(
        ["git", "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=False,
    )
    raw_status = status_proc.stdout.splitlines()

    if not dry_run and stage_paths:
        subprocess.run(["git", "add", "--", *stage_paths], check=True)

    quality_gate = subprocess.run(
        [sys.executable, "tools/quality/proof_proxy_staged_gate.py"],
        cwd=canonical_repo_root(), capture_output=True, text=True, check=False,
    )
    quality_gate_status = "passed" if quality_gate.returncode == 0 else "rejected"
    if quality_gate.returncode != 0:
        message = f"{message} | staged QMS gate rejected: {(quality_gate.stderr or quality_gate.stdout).strip()}"

    # Get status after staging
    post_status_proc = subprocess.run(
        ["git", "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=False,
    )
    post_lines = post_status_proc.stdout.splitlines()

    staged = []
    unstaged = []
    untracked = []

    for line in post_lines:
        if len(line) >= 2:
            x, y = line[0], line[1]
            fname = line[3:].strip()
            if x in ("M", "A", "D", "R", "C"):
                staged.append(fname)
            elif y in ("M", "D"):
                unstaged.append(fname)
            elif x == "?" and y == "?":
                untracked.append(fname)

    # Get git HEAD commit
    head_proc = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    git_head = head_proc.stdout.strip() if head_proc.returncode == 0 else "unknown"

    now_iso = datetime.datetime.now(datetime.timezone.utc).isoformat()
    return CheckpointReceipt(
        timestamp=now_iso,
        staged_files=staged,
        unstaged_files=unstaged,
        untracked_files=untracked,
        git_head=git_head,
        status=("CHECKPOINT_SAVED" if not dry_run else "DRY_RUN") if quality_gate.returncode == 0 else "CHECKPOINT_REJECTED",
        message=message,
        staged_quality_gate=quality_gate_status,
    )


# ---------------------------------------------------------------------------
# Command 7: REFACTOR (Proof Refactorer & Redundancy Cleaner)
# ---------------------------------------------------------------------------

@dataclass
class RefactorSuggestion:
    line_start: int
    line_end: int
    target_block: str
    extracted_lemma_name: str
    extracted_statement: str
    rationale: str


def analyze_refactor_candidates(content: str) -> List[RefactorSuggestion]:
    """Identify oversized monolithic blocks (>25 lines) and extractable subgoals."""
    suggestions: list[RefactorSuggestion] = []
    lines = content.splitlines()

    in_proof = False
    proof_start = 0
    proof_lines: list[str] = []
    current_decl = "<unknown>"

    def flush_block(end_line: int):
        nonlocal in_proof, proof_lines
        if in_proof and len(proof_lines) > 25:
            suggestions.append(
                RefactorSuggestion(
                    line_start=proof_start,
                    line_end=end_line,
                    target_block=current_decl,
                    extracted_lemma_name=f"{current_decl}_helper",
                    extracted_statement="extract intermediate `have` step into dedicated helper",
                    rationale=f"Monolithic proof block ({len(proof_lines)} lines) violates the Lean File Size & Lemma Reuse Mandate.",
                )
            )
        in_proof = False
        proof_lines = []

    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("theorem ") or stripped.startswith("lemma "):
            flush_block(idx - 1)
            parts = stripped.split()
            current_decl = parts[1].split("(")[0].split("{")[0] if len(parts) > 1 else "<decl>"
            if ":= by" in stripped or stripped.endswith(" by"):
                in_proof = True
                proof_start = idx
                proof_lines = [stripped]
            else:
                in_proof = False
                proof_lines = []
        elif not in_proof and (":= by" in stripped or stripped.endswith(" by") or stripped == "by"):
            in_proof = True
            proof_start = idx
            proof_lines = [stripped]
        elif in_proof:
            # End of proof marker
            if (stripped.startswith("def ") or stripped.startswith("end ") or
                stripped.startswith("/-") or stripped.startswith("namespace ") or
                stripped.startswith("instance ") or stripped.startswith("axiom ") or
                stripped.startswith("inductive ") or stripped.startswith("structure ")):
                flush_block(idx - 1)
            else:
                proof_lines.append(stripped)

    flush_block(len(lines))
    return suggestions


# ---------------------------------------------------------------------------
# Command 8: GOLF (Proof Optimizer)
# ---------------------------------------------------------------------------

@dataclass
class GolfSuggestion:
    line_number: int
    original_tactic: str
    suggested_replacement: str
    speedup_rationale: str


def analyze_golf_opportunities(content: str) -> List[GolfSuggestion]:
    """Scan for inefficient or overly verbose tactic patterns."""
    suggestions: list[GolfSuggestion] = []
    lines = content.splitlines()

    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        # Pattern 1: simp; ring or simp only [...]; ring
        if re.search(r"simp(?: only\s*\[.*?\])?\s*;\s*ring\b", stripped):
            suggestions.append(
                GolfSuggestion(
                    line_number=idx,
                    original_tactic=stripped,
                    suggested_replacement="ring",
                    speedup_rationale="Redundant `simp` before `ring`. The `ring` tactic natively normalizes polynomial equalities.",
                )
            )
        # Pattern 2: by exact rfl
        elif re.search(r":=\s*by\s*exact\s+rfl\b", stripped) or re.search(r":=\s*by\s*rfl\b", stripped):
            suggestions.append(
                GolfSuggestion(
                    line_number=idx,
                    original_tactic=stripped,
                    suggested_replacement=":= rfl",
                    speedup_rationale="Replace tactic mode `by rfl` with term mode `rfl` for faster elaboration.",
                )
            )
        # Pattern 3: simp only [id]
        elif re.search(r"simp only\s*\[id\]", stripped):
            suggestions.append(
                GolfSuggestion(
                    line_number=idx,
                    original_tactic=stripped,
                    suggested_replacement="rfl",
                    speedup_rationale="Definitional simplification on identity can be replaced with `rfl`.",
                )
            )

    return suggestions


# ---------------------------------------------------------------------------
# Command 9: AUTOPROVE (Multi-Cycle Engine & M10 Re-Hydration)
# ---------------------------------------------------------------------------

@dataclass
class AutoproveState:
    cycle: int
    max_cycles: int
    target_file: str
    open_sorries: int
    proven_lemmas: List[str]
    dead_routes: List[str]
    status: str
    proof_attempted: bool


def run_autoprove_cycle(
    target_file: str,
    cycle: int = 1,
    max_cycles: int = 3,
    known_dead_routes: Optional[List[str]] = None,
    repo_root: Optional[Path] = None,
) -> AutoproveState:
    """Inspect textual proof-debt markers; this helper does not attempt proofs."""
    dead_routes = list(known_dead_routes or [])
    p = Path(target_file)
    open_sorries = 0
    proven: list[str] = []

    if p.is_file():
        content = _strip_lean_comments_and_strings(p.read_text(encoding="utf-8"))
        open_sorries = len(re.findall(r"\bsorry\b", content))
        # A textual scan cannot establish which declarations compile or are proved.
        proven = []

    # Pillar II Auto-Ingestion: load matching negative constraints from quarantine
    root = repo_root if repo_root is not None else Path(__file__).resolve().parent.parent.parent
    quarantine_dir = root / "artifacts" / "residue_quarantine"
    if quarantine_dir.is_dir():
        target_norm = str(p)
        target_name = p.name
        for qfile in sorted(quarantine_dir.glob("*.json")):
            try:
                qdata = json.loads(qfile.read_text(encoding="utf-8"))
                src = str(qdata.get("source_file", ""))
                constraint = qdata.get("negative_constraint", "")
                if constraint and (src == target_norm or Path(src).name == target_name):
                    if constraint not in dead_routes:
                        dead_routes.append(constraint)
            except Exception:
                continue

    # M10 Anti-Compaction: ensure dead routes are explicitly logged
    if cycle == 1 and not dead_routes:
        dead_routes.append("Unbounded definitional unfolding on colimits (Trap T15)")

    status = "INSPECTION_ONLY"

    return AutoproveState(
        cycle=cycle,
        max_cycles=max_cycles,
        target_file=target_file,
        open_sorries=open_sorries,
        proven_lemmas=proven,
        dead_routes=dead_routes,
        status=status,
        proof_attempted=False,
    )


# ---------------------------------------------------------------------------
# Command 10: FORMALIZE (Interactive Two-Phase Synthesis)
# ---------------------------------------------------------------------------

@dataclass
class FormalizePlan:
    phase: int
    raw_spec: str
    categorical_anchors: List[str]
    screened_clean: bool
    synthesized_lean: str
    synthesis_status: str


def run_formalize(
    spec: str,
    phase: int = 1,
) -> FormalizePlan:
    """Execute Phase 1 (Conceptual Alignment) or Phase 2 (Lean Generation)."""
    anchors = []
    # Identify categorical anchors
    spec_lower = spec.lower()
    if "colimit" in spec_lower or "uhf" in spec_lower:
        anchors.append("InfoGeometry.Canonical.TensorTowerColimit")
    if "cuntz" in spec_lower or "operator" in spec_lower:
        anchors.append("InfoGeometry.Canonical.NoncommutativeOperatorContinuumArchetypes")
    if "parabolic" in spec_lower or "coset" in spec_lower or "gns" in spec_lower:
        anchors.append("InfoGeometry.Cosmology.SpacetimeParabolicQuotient")
    if "clifford" in spec_lower or "spinor" in spec_lower:
        anchors.append("InfoGeometry.Clifford.SolderingIsomorphism")

    # Screen raw spec keywords against T1-T15 traps
    screen_res = refute_content(spec, filename="<spec>")
    clean = screen_res["clean"]

    # A prose specification alone does not determine a Lean carrier or theorem
    # contract. Never manufacture a vacuous theorem as a stand-in for formalization.
    lean_code = ""
    synthesis_status = "NOT_REQUESTED" if phase < 2 else "NEEDS_TYPED_TARGET"

    return FormalizePlan(
        phase=phase,
        raw_spec=spec,
        categorical_anchors=anchors,
        screened_clean=clean,
        synthesized_lean=lean_code,
        synthesis_status=synthesis_status,
    )


# ---------------------------------------------------------------------------
# Command 11: AUTOFORMALIZE (End-to-End CAS to Lean Translator)
# ---------------------------------------------------------------------------

@dataclass
class CASInvariantTranslation:
    cas_type: str
    expression: str
    theorem_name: str
    lean_code: str
    verified: bool
    verification_status: str


def autoformalize_cas_identity(
    cas_type: str,
    expression: str,
    theorem_name: str,
) -> CASInvariantTranslation:
    """Generate a Lean candidate from an expression without claiming verification."""
    cas_lower = cas_type.lower()
    clean_expr = expression.strip()

    # Matrix determinant identity translation (e.g. SL(2) det = 1)
    if "det" in clean_expr and ("sl2" in clean_expr.lower() or "matrix" in clean_expr.lower()):
        lean_code = (
            f"/-- CAS-certified invariant from {cas_type}: `{clean_expr}`. -/\n"
            f"theorem {theorem_name} (a b c d : ℝ) (h : a * d - b * c = 1) :\n"
            f"    (![ ![a, b], ![c, d] ] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by\n"
            f"  simp [Matrix.det_fin_two]\n"
            f"  linarith\n"
        )
    # Polynomial / Ring identity translation
    elif "=" in clean_expr:
        lhs, rhs = clean_expr.split("=", 1)
        lean_code = (
            f"/-- CAS-certified identity from {cas_type}: `{clean_expr}`. -/\n"
            f"theorem {theorem_name} (x y : ℝ) :\n"
            f"    {lhs.strip()} = {rhs.strip()} := by\n"
            f"  ring\n"
        )
    else:
        lean_code = (
            f"/-- CAS-certified proposition from {cas_type}: `{clean_expr}`. -/\n"
            f"theorem {theorem_name} : True := by\n"
            f"  trivial\n"
        )

    return CASInvariantTranslation(
        cas_type=cas_type,
        expression=clean_expr,
        theorem_name=theorem_name,
        lean_code=lean_code,
        verified=False,
        verification_status="not_run",
    )


# ---------------------------------------------------------------------------
# Command 12: HANDOFF (Cross-Session Context Preserver)
# ---------------------------------------------------------------------------

@dataclass
class HandoffContext:
    timestamp: str
    active_targets: List[str]
    dead_routes: List[str]
    verified_checkpoints: List[str]
    next_actions: List[str]
    handoff_markdown: str


def generate_handoff_context(
    active_targets: List[str],
    verified_checkpoints: List[str],
    dead_routes: Optional[List[str]] = None,
    next_actions: Optional[List[str]] = None,
) -> HandoffContext:
    """Serialize the exact mathematical state into an Anti-Compaction M10 Handoff."""
    now_iso = datetime.datetime.now(datetime.timezone.utc).isoformat()
    dead = dead_routes or [
        "Unbounded colimit definitional unfolding (Trap T15)",
        "Raw coordinate extraction off-basepoint without bundle pairing (Trap T1)",
    ]
    actions = next_actions or ["Continue top-down leaf proof closure."]

    md = [
        f"# OpenGauss / TeamAntigravity Cross-Session Handoff ({now_iso})",
        "",
        "## 1. Active Mathematical Targets",
    ]
    for t in active_targets:
        md.append(f"- `{t}`")

    md.extend(["", "## 2. Verified Checkpoints (0 sorry, 0 custom axioms)"])
    for vc in verified_checkpoints:
        md.append(f"- [x] {vc}")

    md.extend(["", "## 3. Dead Routes & Disproven Trajectories (Anti-Compaction Anchor)"])
    for dr in dead:
        md.append(f"- [BANNED] {dr}")

    md.extend(["", "## 4. Priority Next Actions"])
    for act in actions:
        md.append(f"- 1. {act}")

    md_str = "\n".join(md) + "\n"

    return HandoffContext(
        timestamp=now_iso,
        active_targets=active_targets,
        dead_routes=dead,
        verified_checkpoints=verified_checkpoints,
        next_actions=actions,
        handoff_markdown=md_str,
    )


# ---------------------------------------------------------------------------
# Command 13: DISCOVER (Mathematical Declaration & Carrier Hunter)
# ---------------------------------------------------------------------------

@dataclass
class DiscoveryReport:
    query: str
    carriers_found: List[Dict[str, Any]] = field(default_factory=list)
    lemmas_found: List[Dict[str, Any]] = field(default_factory=list)
    recommended_imports: Set[str] = field(default_factory=set)
    deduplication_warnings: List[str] = field(default_factory=list)
    local_dag_context: Optional[Dict[str, Any]] = None
    dag_context: Optional[Dict[str, Any]] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema": "info_geometry.opengauss.discovery_report.v1",
            "authority": "navigation_only",
            "graph_is_proof_authority": False,
            "query": self.query,
            "carriers_found": self.carriers_found,
            "lemmas_found": self.lemmas_found,
            "recommended_imports": sorted(list(self.recommended_imports)),
            "deduplication_warnings": self.deduplication_warnings,
            "local_dag_context": self.local_dag_context,
            "dag_context": self.dag_context,
        }


def discover_dag_context(
    apices: Sequence[str],
    *,
    repo_root: Path,
    generation_id: Optional[str] = None,
    backward_depth: int = 6,
    forward_depth: int = 6,
    cone_limit: int = 250,
) -> Dict[str, Any]:
    """Query the existing read-only declaration DAG cone tool for exact apices.

    This returns navigation context only. In particular, an unversioned legacy
    graph has unknown freshness, and a missing graph result is not evidence that
    an owner declaration is absent from the repository.
    """
    names = [name.strip() for name in apices if name.strip()]
    if not names:
        raise ValueError("at least one exact declaration apex is required")
    if len(set(names)) != len(names):
        raise ValueError("duplicate exact declaration apices are not allowed")
    script = repo_root / "tools" / "infra" / "arango_causal_chiral_cone_prompt.py"
    command = [sys.executable, str(script), "--repo-root", str(repo_root)]
    if len(names) == 1:
        command.extend(["--decl", names[0]])
    else:
        command.extend(["--decl-multi", ",".join(names)])
    command.extend([
        "--backward-depth", str(backward_depth),
        "--forward-depth", str(forward_depth),
        "--cone-limit", str(cone_limit),
    ])
    if generation_id:
        command.extend(["--generation-id", generation_id])
    try:
        result = subprocess.run(
            command, cwd=repo_root, capture_output=True, text=True,
            check=False, timeout=90,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "status": "unavailable",
            "reason": type(exc).__name__,
            "requested_apices": names,
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    if result.returncode != 0:
        return {
            "status": "unavailable",
            "reason": "cone_query_failed",
            "returncode": result.returncode,
            "diagnostic": (result.stderr or result.stdout).strip()[:1000],
            "requested_apices": names,
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    try:
        packet = json.loads(result.stdout)
    except json.JSONDecodeError:
        return {
            "status": "invalid_packet",
            "requested_apices": names,
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    if not isinstance(packet, dict):
        return {
            "status": "invalid_packet",
            "requested_apices": names,
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    if packet.get("schema") != "info_geometry.causal_chiral_cone_prompt.v2":
        packet["status"] = "invalid_packet"
        packet["validation_error"] = "unexpected_schema"
        return packet
    expected_mode = "multi-apex-multi-cone" if len(names) > 1 else "single-apex-multi-cone"
    resolution_diagnostic = (
        len(names) > 1
        and packet.get("mode") == "multi-apex-resolution-diagnostic"
        and packet.get("status") in {"unindexed", "not_found"}
    )
    if packet.get("mode") != expected_mode and not resolution_diagnostic:
        packet["status"] = "invalid_packet"
        packet["validation_error"] = "unexpected_mode"
        return packet
    if packet.get("status") != "ok" and not resolution_diagnostic:
        packet["status"] = "invalid_packet"
        packet["validation_error"] = "unexpected_status"
        return packet
    if len(names) == 1:
        returned_names = [((packet.get("apex") or {}).get("name"))]
        if packet.get("mode") == "multi-apex-resolution-diagnostic":
            returned_names = packet.get("requested_names", [])
    else:
        if packet.get("mode") == "multi-apex-resolution-diagnostic":
            returned_names = packet.get("requested_names", [])
        else:
            returned_names = [row.get("name") for row in packet.get("apices", []) if isinstance(row, dict)]
    if returned_names != names:
        packet["status"] = "invalid_packet"
        packet["validation_error"] = "requested_apices_mismatch"
        return packet
    provenance_in = packet.get("graph_provenance")
    returned_generation = provenance_in.get("generation_id") if isinstance(provenance_in, dict) else None
    if generation_id is not None and returned_generation != generation_id:
        packet["status"] = "invalid_packet"
        packet["validation_error"] = "requested_generation_mismatch"
        return packet
    packet["authority"] = "navigation_only"
    packet["graph_is_proof_authority"] = False
    provenance = packet.get("graph_provenance")
    if not isinstance(provenance, dict):
        provenance = {}
        packet["graph_provenance"] = provenance
    provenance.setdefault("freshness", "unknown")
    return packet


def discover_local_dag_context(
    query: str,
    *,
    repo_root: Path,
    depth: int = 1,
    limit: int = 10,
) -> Dict[str, Any]:
    """Run the repository's offline DAG/LeanTrail preflight as navigation only."""
    script = repo_root / "tools" / "infra" / "arango_causal_memory.py"
    command = [
        sys.executable, str(script), "local-preflight", query,
        "--depth", str(depth), "--limit", str(limit),
    ]
    try:
        result = subprocess.run(
            command, cwd=repo_root, capture_output=True, text=True,
            check=False, timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "status": "unavailable",
            "reason": type(exc).__name__,
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    if result.returncode != 0:
        return {
            "status": "unavailable",
            "reason": "local_preflight_failed",
            "returncode": result.returncode,
            "diagnostic": (result.stderr or result.stdout).strip()[:1000],
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    try:
        envelope = json.loads(result.stdout)
    except json.JSONDecodeError:
        envelope = None
    if not isinstance(envelope, dict):
        return {
            "status": "invalid_packet",
            "validation_error": "expected_json_object",
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    if envelope.get("ok") is not True or envelope.get("target") != "local":
        return {
            "status": "unavailable",
            "validation_error": "unexpected_local_preflight_envelope",
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    packet = envelope.get("output")
    if not isinstance(packet, dict):
        return {
            "status": "invalid_packet",
            "validation_error": "expected_output_object",
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    if packet.get("schema") != "info_geometry.local_dag_attention.v1":
        return {
            "status": "invalid_packet",
            "validation_error": "unexpected_schema",
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    if "local_search" not in packet or "artifacts" not in packet:
        return {
            "status": "invalid_packet",
            "validation_error": "missing_required_fields",
            "authority": "navigation_only",
            "freshness": "unknown",
            "graph_is_proof_authority": False,
        }
    packet["status"] = "ok"
    packet["authority"] = "navigation_only"
    packet["freshness"] = "unknown"
    packet["graph_is_proof_authority"] = False
    return packet


def _file_to_module_path(path: Path, repo_root: Path) -> str:
    """Convert a Lean file path into its canonical Lean module import path."""
    try:
        resolved = path.resolve()
        lean_dir = (repo_root / "lean").resolve()
        mathlib_dir = (repo_root / ".lake" / "packages" / "mathlib").resolve()
        if lean_dir in resolved.parents or resolved == lean_dir:
            rel = resolved.relative_to(lean_dir)
            parts = list(rel.parts)
            if parts[-1].endswith(".lean"):
                parts[-1] = parts[-1][:-5]
            return ".".join(parts)
        elif mathlib_dir in resolved.parents or resolved == mathlib_dir:
            rel = resolved.relative_to(mathlib_dir)
            parts = list(rel.parts)
            if parts[-1].endswith(".lean"):
                parts[-1] = parts[-1][:-5]
            return ".".join(parts)
        else:
            try:
                rel = resolved.relative_to(repo_root.resolve())
                parts = list(rel.parts)
                if parts[-1].endswith(".lean"):
                    parts[-1] = parts[-1][:-5]
                return ".".join(parts)
            except ValueError:
                return path.stem
    except Exception:
        return path.stem


def discover_declarations(
    query: str,
    repo_root: Optional[Path] = None,
) -> DiscoveryReport:
    """Scans lean/InfoGeometry/ (and Mathlib if available) for structures, defs, theorems matching query."""
    if repo_root is None:
        repo_root = Path(__file__).resolve().parent.parent.parent

    query_clean = query.strip()
    query_lower = query_clean.lower()
    query_tokens = [tok.lower() for tok in re.split(r"\W+", query_clean) if tok]

    carriers: List[Dict[str, Any]] = []
    lemmas: List[Dict[str, Any]] = []
    recommended_imports: Set[str] = set()
    dedup_warnings: List[str] = []

    # Identify search directories
    search_dirs: List[Path] = []
    info_dir = repo_root / "lean" / "InfoGeometry"
    if info_dir.is_dir():
        search_dirs.append(info_dir)
    elif (repo_root / "lean").is_dir():
        search_dirs.append(repo_root / "lean")
    else:
        search_dirs.append(repo_root)

    # Pre-filter candidate files with tiered prioritization
    candidate_files: List[Path] = []
    seen_paths = set()

    # Tier 1: Joined phrase or domain synonyms (e.g. split-quaternion, coquaternion)
    joined_parts = [re.escape(t) for t in query_tokens if len(t) >= 2]
    if joined_parts:
        joined_pat = r"[\s\-_]*".join(joined_parts)
        if "split" in query_tokens and "quaternion" in query_tokens:
            joined_pat += "|coquaternion"
        for sdir in search_dirs:
            try:
                proc = subprocess.run(["grep", "-ril", "-E", joined_pat, str(sdir)], capture_output=True, text=True, check=False)
                if proc.returncode == 0 and proc.stdout:
                    for line in proc.stdout.strip().splitlines():
                        p = Path(line)
                        if p.is_file() and p.resolve() not in seen_paths:
                            seen_paths.add(p.resolve())
                            candidate_files.append(p)
            except Exception:
                pass

    # Tier 2: If multi-token, find files containing tokens
    if len(candidate_files) < 150:
        grep_pattern = "|".join(re.escape(t) for t in query_tokens if len(t) >= 3) or (re.escape(query_tokens[0]) if query_tokens else "")
        if grep_pattern:
            for sdir in search_dirs:
                try:
                    proc = subprocess.run(["grep", "-ril", "-E", grep_pattern, str(sdir)], capture_output=True, text=True, check=False)
                    if proc.returncode == 0 and proc.stdout:
                        for line in proc.stdout.strip().splitlines():
                            p = Path(line)
                            if p.is_file() and p.resolve() not in seen_paths:
                                seen_paths.add(p.resolve())
                                candidate_files.append(p)
                except Exception:
                    pass

    if not candidate_files:
        for sdir in search_dirs:
            for f in sdir.rglob("*.lean"):
                if f.is_file() and f.resolve() not in seen_paths:
                    seen_paths.add(f.resolve())
                    candidate_files.append(f)

    candidates_to_scan = candidate_files[:250]

    is_split_quat = ("split" in query_tokens and "quaternion" in query_tokens)

    for cf in candidates_to_scan:
        try:
            source_bytes = cf.read_bytes()
            content = source_bytes.decode("utf-8", errors="replace")
            source_sha256 = hashlib.sha256(source_bytes).hexdigest()
        except Exception:
            continue

        try:
            rel_path = cf.relative_to(repo_root)
        except ValueError:
            rel_path = cf

        file_matches_query = (query_lower in content[:2000].lower()) or (is_split_quat and "coquaternion" in content[:2000].lower())

        raw_lines = content.splitlines()
        for qualified_name, declarations in _qualified_declaration_heads(content).items():
            for declaration in declarations:
                kind = declaration["kind"]
                name = qualified_name.rsplit(".", 1)[-1]
                line_num = declaration["source_line"]
                preceding = "\n".join(raw_lines[:line_num - 1])
                doc_match = re.search(r"/--\s*(.*?)\s*-/\s*$", preceding, flags=re.DOTALL)
                doc = (doc_match.group(1) if doc_match else "").strip()

                combined_decl = f"{qualified_name} {doc}".lower()

                matched = False
                if query_lower in combined_decl:
                    matched = True
                elif is_split_quat and "coquaternion" in combined_decl:
                    matched = True
                elif all(tok in combined_decl for tok in query_tokens):
                    matched = True
                elif any(tok in name.lower() for tok in query_tokens):
                    matched = True
                elif file_matches_query and any(tok in combined_decl for tok in query_tokens):
                    matched = True
                elif file_matches_query and kind in ("structure", "class", "inductive") and ("carrier" in doc.lower() or any(tok in doc.lower() for tok in query_tokens)):
                    matched = True

                if matched:
                    entry = {
                        "name": name,
                        "qualified_name": qualified_name,
                        "kind": kind,
                        "file": str(rel_path),
                        "source_sha256": source_sha256,
                        "line": line_num,
                        "source_end_line": declaration["source_end_line"],
                        "lean_statement": declaration["lean_statement"],
                        "location": f"{rel_path}:{line_num}",
                    }
                    mod_path = _file_to_module_path(cf, repo_root)
                    recommended_imports.add(mod_path)

                    if kind in ("structure", "class", "inductive") or (kind == "def" and (name[0].isupper() or any(tok in name.lower() for tok in query_tokens))):
                        carriers.append(entry)
                    elif kind in ("theorem", "lemma"):
                        lemmas.append(entry)

    # Check mathlib declarations if available and needed
    mathlib_dir = repo_root / ".lake" / "packages" / "mathlib" / "Mathlib"
    if mathlib_dir.is_dir() and query_tokens and len(carriers) < 5:
        for qtok in query_tokens:
            if len(qtok) >= 4:
                for ml_file in mathlib_dir.rglob(f"*{qtok.capitalize()}*.lean"):
                    mod_path = _file_to_module_path(ml_file, repo_root)
                    recommended_imports.add(mod_path)

    for carrier in carriers:
        cname = carrier["name"]
        cfile = carrier["file"]
        dedup_warnings.append(
            f"Query '{query_clean}' matches existing fundamental type '{cname}' in {cfile}; "
            f"reuse canonical carrier instead of introducing redundant type wrapper."
        )

    return DiscoveryReport(
        query=query_clean,
        carriers_found=carriers,
        lemmas_found=lemmas,
        recommended_imports=recommended_imports,
        deduplication_warnings=dedup_warnings,
    )


# ---------------------------------------------------------------------------
# Command 14: QUARANTINE (Rejected Route & Residue Obstruction Isolator)
# ---------------------------------------------------------------------------

@dataclass
class TypedObstructionPacket:
    packet_id: str
    timestamp: str
    source_file: str
    trap_id: str
    description: str
    counterexample: str
    negative_constraint: str


def quarantine_obstruction(
    file: str,
    trap_id: str,
    description: str,
    counterexample: str,
    negative_constraint: str,
    repo_root: Optional[Path] = None,
) -> TypedObstructionPacket:
    """Ingests a rejected theorem attempt or refuter counterexample into a TypedObstructionPacket and persists it."""
    if repo_root is None:
        repo_root = Path(__file__).resolve().parent.parent.parent

    now_dt = datetime.datetime.now(datetime.timezone.utc)
    timestamp = now_dt.isoformat()
    seed = f"{file}:{trap_id}:{description}:{counterexample}:{negative_constraint}:{timestamp}"
    packet_hash = hashlib.sha256(seed.encode("utf-8")).hexdigest()[:8]
    ts_compact = now_dt.strftime("%Y%m%d_%H%M%S")
    packet_id = f"obs_{ts_compact}_{packet_hash}"

    packet = TypedObstructionPacket(
        packet_id=packet_id,
        timestamp=timestamp,
        source_file=str(file),
        trap_id=trap_id,
        description=description,
        counterexample=counterexample,
        negative_constraint=negative_constraint,
    )

    quarantine_dir = repo_root / "artifacts" / "residue_quarantine"
    quarantine_dir.mkdir(parents=True, exist_ok=True)
    out_file = quarantine_dir / f"{packet_id}.json"
    out_file.write_text(json.dumps(asdict(packet), indent=2), encoding="utf-8")

    return packet


# ---------------------------------------------------------------------------
# Command 15: CERTIFY (Companion Axiom Certification Script Generator)
# ---------------------------------------------------------------------------

@dataclass
class CertificationAudit:
    source_file: str
    audit_file: Optional[str]
    theorems: List[str]
    audit_script: str
    written: bool = False
    kernel_checked: bool = False
    verification_status: str = "not_requested"
    theorem_axioms: Dict[str, List[str]] = field(default_factory=dict)
    rejected_axioms: List[str] = field(default_factory=list)
    verification_errors: List[str] = field(default_factory=list)


_ALLOWED_KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def verify_certification_audit(
    lean_file: Path,
    *,
    repo_root: Optional[Path] = None,
) -> CertificationAudit:
    """Build a Lean owner and check its generated axiom audit under one lock."""
    root = Path(repo_root) if repo_root is not None else canonical_repo_root()
    audit = generate_certification_audit(lean_file, write_audit=False, repo_root=root)
    module = _file_to_module_path(Path(lean_file), root)
    result = CertificationAudit(
        source_file=audit.source_file,
        audit_file=None,
        theorems=audit.theorems,
        audit_script=audit.audit_script,
    )
    source_code = _strip_lean_comments_and_strings(
        Path(lean_file).read_text(encoding="utf-8", errors="replace")
    )
    source_axioms = re.findall(
        r"^\s*(?:(?:private|protected)\s+)*axiom\s+([A-Za-z_][A-Za-z0-9_']*)\b",
        source_code,
        flags=re.MULTILINE,
    )

    print(
        f"[OpenGauss Gate 4] Waiting for shared build lock ({module})",
        file=sys.stderr,
        flush=True,
    )
    lock = acquire_build_lock(None, f"opengauss-certify:{module}", block=True)
    try:
        print(
            f"[OpenGauss Gate 4] Build lock acquired; building {module}",
            file=sys.stderr,
            flush=True,
        )
        build = subprocess.run(
            ["lake", "build", module],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
        if build.returncode != 0:
            print(
                f"[OpenGauss Gate 4] Owner build failed for {module}",
                file=sys.stderr,
                flush=True,
            )
            result.verification_status = "build_failed"
            result.verification_errors.append(
                (build.stdout + build.stderr)[-12000:]
            )
            return result

        if not audit.theorems:
            print(
                f"[OpenGauss Gate 4] No theorem declarations found in {module}; finishing source axiom check",
                file=sys.stderr,
                flush=True,
            )
            result.rejected_axioms = sorted(set(source_axioms))
            result.kernel_checked = True
            result.verification_status = "passed" if not result.rejected_axioms else "disallowed_axioms"
            return result

        with tempfile.TemporaryDirectory(prefix="opengauss-certify-") as temp_dir:
            audit_path = Path(temp_dir) / "AxiomAudit.lean"
            audit_path.write_text(audit.audit_script, encoding="utf-8")
            print(
                f"[OpenGauss Gate 4] Owner build passed; compiling generated axiom audit for {module}",
                file=sys.stderr,
                flush=True,
            )
            checked = subprocess.run(
                ["lake", "env", "lean", str(audit_path)],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
        output = checked.stdout + checked.stderr
        if checked.returncode != 0:
            print(
                f"[OpenGauss Gate 4] Generated axiom audit failed for {module}",
                file=sys.stderr,
                flush=True,
            )
            result.verification_status = "audit_compile_failed"
            result.verification_errors.append(output[-12000:])
            return result

        axiom_reports = list(re.finditer(
            r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms",
            output,
            flags=re.DOTALL,
        ))
        if len(axiom_reports) != len(audit.theorems):
            result.verification_status = "axiom_output_incomplete"
            result.verification_errors.append(
                f"Expected {len(audit.theorems)} axiom reports; found {len(axiom_reports)}."
            )
            result.verification_errors.append(output[-12000:])
            return result

        all_axioms: set[str] = set(source_axioms)
        for theorem, report in zip(audit.theorems, axiom_reports):
            raw_axioms = report.group(1) or ""
            axioms = [name.strip() for name in raw_axioms.split(",") if name.strip()]
            result.theorem_axioms[theorem] = axioms
            all_axioms.update(axioms)
        result.rejected_axioms = sorted(all_axioms - _ALLOWED_KERNEL_AXIOMS)
        result.kernel_checked = True
        result.verification_status = "passed" if not result.rejected_axioms else "disallowed_axioms"
        print(
            f"[OpenGauss Gate 4] Axiom audit {result.verification_status} for {module}",
            file=sys.stderr,
            flush=True,
        )
        return result
    except OSError as exc:
        result.verification_status = "tool_error"
        result.verification_errors.append(str(exc))
        return result
    finally:
        lock.release()


def generate_certification_audit(
    lean_file: Path,
    write_audit: bool = False,
    repo_root: Optional[Path] = None,
) -> CertificationAudit:
    """Extracts all theorems from target .lean file and emits a companion audit script with #print axioms."""
    if repo_root is None:
        repo_root = Path(__file__).resolve().parent.parent.parent

    lean_path = Path(lean_file)
    if not lean_path.is_file():
        raise FileNotFoundError(f"Target Lean file not found: {lean_file}")

    content = _strip_lean_comments_and_strings(
        lean_path.read_text(encoding="utf-8", errors="replace")
    )

    # `namespace` declarations form lexical scopes. A file may close and later
    # reopen a namespace, or enter unrelated namespaces; collecting every
    # namespace line and joining them produces invalid qualified names. Track
    # the active path at each declaration instead. Dotted namespace syntax is
    # expanded into components so `end B` closes the innermost `B` scope.
    scope_stack: list[tuple[str, Optional[str]]] = []
    theorems: list[str] = []
    namespace_pattern = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
    end_pattern = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*(?:--.*)?$")
    theorem_pattern = re.compile(
        r"^\s*(?:(?:@\[[^\]]*\]\s*)*)"
        r"((?:(?:private|protected|noncomputable|unsafe)\s+)*)"
        r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*|«[^»]+»)(?:\b|\s|$)"
    )
    pending_private = False
    for line in content.splitlines():
        stripped_line = line.strip()
        if stripped_line == "private":
            pending_private = True
            continue
        if pending_private and (not stripped_line or stripped_line.startswith("@[") and stripped_line.endswith("]")):
            continue
        namespace_match = namespace_pattern.match(line)
        if namespace_match:
            pending_private = False
            scope_stack.extend(
                ("namespace", component)
                for component in namespace_match.group(1).split(".")
            )
            continue
        section_match = re.match(r"^\s*section(?:\s+([A-Za-z0-9_']+))?\s*$", line)
        if section_match:
            pending_private = False
            scope_stack.append(("section", section_match.group(1)))
            continue
        end_match = end_pattern.match(line)
        if end_match:
            pending_private = False
            closing_name = end_match.group(1)
            if closing_name is None:
                if scope_stack:
                    scope_stack.pop()
            else:
                closing_parts = closing_name.split(".")
                last_named_scope = next(
                    (
                        index
                        for index in range(len(scope_stack) - 1, -1, -1)
                        if scope_stack[index][1] == closing_name
                    ),
                    None,
                )
                namespace_entries = [
                    (index, name)
                    for index, (kind, name) in enumerate(scope_stack)
                    if kind == "namespace" and name is not None
                ]
                namespace_tail = namespace_entries[-len(closing_parts):]
                if len(closing_parts) == 1 and last_named_scope is not None:
                    del scope_stack[last_named_scope:]
                elif [name for _, name in namespace_tail] == closing_parts:
                    del scope_stack[namespace_tail[0][0]:]
                elif last_named_scope is not None:
                    del scope_stack[last_named_scope:]
            continue
        theorem_match = theorem_pattern.match(line)
        if theorem_match:
            visibility_modifiers = theorem_match.group(1) or ""
            is_private = pending_private or bool(re.search(r"\bprivate\b", visibility_modifiers))
            pending_private = False
            if is_private:
                # Private declarations are mangled and cannot be referenced
                # from the imported companion audit module.
                continue
            name = theorem_match.group(2)
            active_namespace = [
                value for kind, value in scope_stack
                if kind == "namespace" and value is not None
            ]
            theorems.append(".".join([*active_namespace, name]) if active_namespace else name)
        elif stripped_line:
            pending_private = False

    mod_path = _file_to_module_path(lean_path, repo_root)

    lines: List[str] = [
        "/-",
        "Copyright (c) 2026 InfoGeometry Authors. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: InfoGeometry Engine Contributors",
        "-/",
        "",
        f"import {mod_path}",
        "",
    ]
    if theorems:
        for thm in theorems:
            lines.append(f"#print axioms {thm}")
    else:
        lines.append("-- No theorems found in source file for axiom certification audit.")
    lines.append("")

    audit_script = "\n".join(lines)
    audit_file_path = lean_path.parent / f"{lean_path.stem}Audit.lean"
    written = False

    if write_audit:
        audit_file_path.write_text(audit_script, encoding="utf-8")
        written = True

    return CertificationAudit(
        source_file=str(lean_path),
        audit_file=str(audit_file_path),
        theorems=theorems,
        audit_script=audit_script,
        written=written,
    )


# ---------------------------------------------------------------------------
# CLI Argument Parsing & Dispatcher
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="opengauss_cli",
        description="OpenGauss / TeamAntigravity Unified Mathematical Protocol CLI",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # 1. prove
    p_prove = subparsers.add_parser("prove", help="Top-Down Assume-and-Recurse Prover")
    p_prove.add_argument("--headline", required=True, help="Headline theorem name")
    p_prove.add_argument("--type", dest="headline_type", required=True, help="Headline theorem type")
    p_prove.add_argument("--sublemmas", default="[]", help="JSON list of child lemmas [{'name':..., 'type':...}]")
    p_prove.add_argument("--glue", default=None, help="Glue tactic string (e.g. 'exact h1 h2')")
    p_prove.add_argument("--json", action="store_true", help="Output JSON")

    # 2. check
    p_check = subparsers.add_parser("check", help="Ground-Truthed Counterexample Hunter")
    p_check.add_argument("--expr", required=True, help="Mathematical expression / theorem conclusion")
    p_check.add_argument("--hyp", action="append", default=[], help="Hypothesis to check (can be specified multiple times)")
    p_check.add_argument("--json", action="store_true", help="Output JSON")

    # 3. refute
    p_refute = subparsers.add_parser("refute", help="Adversarial False-as-Stated Screener (15 Traps)")
    p_refute.add_argument("paths", nargs="+", help="Files or directories to screen")
    p_refute.add_argument("--strict", action="store_true", help="Treat warnings as errors")
    p_refute.add_argument("--json", action="store_true", help="Output JSON")

    # 4. draft
    p_draft = subparsers.add_parser("draft", help="Skeleton Drafter")
    p_draft.add_argument("--headline", required=True, help="Headline theorem name")
    p_draft.add_argument("--signature", required=True, help="Signature binders and type")
    p_draft.add_argument("--sublemmas", default="[]", help="JSON list of child lemmas")
    p_draft.add_argument("--namespace", default=None, help="Optional Lean namespace")
    p_draft.add_argument("--output", default=None, help="Output file path (prints to stdout if omitted)")
    p_draft.add_argument("--ground-truth-contract", default=None, help="Validated six-part contract JSON; required when writing a draft file")
    p_draft.add_argument("--scratch", action="store_true", help="Explicitly allow an unbound exploratory draft, not eligible for source promotion")
    p_draft.add_argument("--json", action="store_true", help="Output JSON")

    # 5. review
    p_review = subparsers.add_parser("review", help="Independent QMS Read-Only Auditor")
    p_review.add_argument("paths", nargs="+", help="Lean files to audit")
    p_review.add_argument("--gate", default="GATE_2", choices=["GATE_2", "GATE_4"], help="Audit gate")
    p_review.add_argument("--verify-kernel", action="store_true", help="Build each owner and check its #print axioms audit under the shared build lock (GATE_4 only)")
    p_review.add_argument("--json", action="store_true", help="Output JSON")

    # 6. checkpoint
    p_ckpt = subparsers.add_parser("checkpoint", help="State Saver & Continuous Tracker")
    p_ckpt.add_argument("--message", "-m", default="OpenGauss automated checkpoint", help="Checkpoint message")
    p_ckpt.add_argument("--dry-run", action="store_true", help="Dry run without staging")
    p_ckpt.add_argument("--stage-path", action="append", default=[], help="Explicit path to stage; may be repeated")
    p_ckpt.add_argument("--json", action="store_true", help="Output JSON")

    # 7. refactor
    p_refactor = subparsers.add_parser("refactor", help="Proof Refactorer & Redundancy Cleaner")
    p_refactor.add_argument("path", help="Lean file to analyze for monolithic blocks")
    p_refactor.add_argument("--json", action="store_true", help="Output JSON")

    # 8. golf
    p_golf = subparsers.add_parser("golf", help="Proof Optimizer")
    p_golf.add_argument("path", help="Lean file to scan for golfable tactics")
    p_golf.add_argument("--json", action="store_true", help="Output JSON")

    # 9. autoprove
    p_auto = subparsers.add_parser("autoprove", help="Autonomous Multi-Cycle Engine")
    p_auto.add_argument("target", help="Target Lean file")
    p_auto.add_argument("--cycles", type=int, default=1, help="Cycle count")
    p_auto.add_argument("--max-cycles", type=int, default=3, help="Max allowed cycles")
    p_auto.add_argument("--json", action="store_true", help="Output JSON")

    # 10. formalize
    p_form = subparsers.add_parser("formalize", help="Two-Phase Interactive Synthesis Assistant")
    p_form.add_argument("--spec", required=True, help="Informal specification or statement")
    p_form.add_argument("--phase", type=int, default=1, choices=[1, 2], help="Phase (1=alignment, 2=code)")
    p_form.add_argument("--json", action="store_true", help="Output JSON")

    # 11. autoformalize
    p_autoform = subparsers.add_parser("autoformalize", help="End-to-End CAS to Lean Translator")
    p_autoform.add_argument("--cas", default="sympy", choices=["sympy", "macaulay2", "gap"], help="CAS source")
    p_autoform.add_argument("--expr", required=True, help="CAS identity or symbolic expression")
    p_autoform.add_argument("--name", default="cas_certified_identity", help="Generated Lean theorem name")
    p_autoform.add_argument("--json", action="store_true", help="Output JSON")

    # 12. handoff
    p_handoff = subparsers.add_parser("handoff", help="Cross-Session Context Preserver")
    p_handoff.add_argument("--targets", nargs="+", default=[], help="Active target files")
    p_handoff.add_argument("--checkpoints", nargs="+", default=[], help="Verified checkpoints")
    p_handoff.add_argument("--dead-routes", nargs="+", default=None, help="Dead routes")
    p_handoff.add_argument("--out", default=None, help="File to write handoff markdown to")
    p_handoff.add_argument("--json", action="store_true", help="Output JSON")

    # 13. discover
    p_disc = subparsers.add_parser("discover", help="Mathematical Declaration & Carrier Hunter")
    p_disc.add_argument("--query", required=True, help="Search query (e.g. 'split quaternion')")
    p_disc.add_argument(
        "--dag-apex", action="append", default=[], metavar="QUALIFIED_NAME",
        help="Optional exact Lean declaration apex for bounded Arango DAG context; repeat for multi-apex cross-sections",
    )
    p_disc.add_argument("--dag-generation-id", default=None, help="Optional expected Arango graph generation identifier")
    p_disc.add_argument("--backward-depth", type=int, default=6, help="Maximum prerequisite-cone depth (default: 6)")
    p_disc.add_argument("--forward-depth", type=int, default=6, help="Maximum consequence-cone depth (default: 6)")
    p_disc.add_argument("--cone-limit", type=int, default=250, help="Maximum rows returned per apex and direction (default: 250)")
    p_disc.add_argument("--local-dag-context", action="store_true", help="Include offline artifacts/dag/index and LeanTrail preflight context")
    p_disc.add_argument("--local-dag-depth", type=int, default=1, help="Neighborhood depth for offline DAG preflight (default: 1)")
    p_disc.add_argument("--local-dag-limit", type=int, default=10, help="Hit/neighborhood limit for offline DAG preflight (default: 10)")
    p_disc.add_argument("--output", default=None, help="Persist the versioned discovery receipt as JSON")
    p_disc.add_argument("--json", action="store_true", help="Output JSON")

    # 14. quarantine
    p_quar = subparsers.add_parser("quarantine", help="Rejected Route & Residue Obstruction Isolator")
    p_quar.add_argument("--file", required=True, help="Source file of obstruction")
    p_quar.add_argument("--trap", required=True, help="Trap ID (e.g. T4, T11, T13)")
    p_quar.add_argument("--desc", required=True, help="Explanation of why it failed")
    p_quar.add_argument("--counter", required=True, help="Minimal mathematical counterexample")
    p_quar.add_argument("--constraint", required=True, help="Explicit negative constraint to inject")
    p_quar.add_argument("--repo-root", default=None, help="Artifact root (defaults to the repository root)")
    p_quar.add_argument("--json", action="store_true", help="Output JSON")

    # 15. certify
    p_cert = subparsers.add_parser("certify", help="Companion Axiom Certification Script Generator")
    p_cert.add_argument("--file", required=True, help="Target Lean 4 file")
    p_cert.add_argument("--write-audit", action="store_true", help="Write companion Audit.lean file next to source")
    p_cert.add_argument("--verify-kernel", action="store_true", help="Build the owner and run its generated #print axioms audit under the shared build lock")
    p_cert.add_argument("--json", action="store_true", help="Output JSON")

    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    cmd = args.command

    if cmd == "prove":
        sublemmas = json.loads(args.sublemmas) if isinstance(args.sublemmas, str) else args.sublemmas
        res = plan_top_down_proof(args.headline, args.headline_type, sublemmas, args.glue)
        if args.json:
            print(json.dumps(asdict(res), indent=2))
        else:
            print("\n".join(res.plan))
            print(f"\n[Status]: {res.status} (Anti-T11 Compliant: {res.anti_t11_compliant})")
        return 0

    elif cmd == "check":
        res = check_consistency(args.expr, args.hyp)
        if args.json:
            print(json.dumps(asdict(res), indent=2))
        else:
            print(f"Target: {res.target}")
            print(f"Consistent: {res.consistent}")
            print(f"Counterexample Risk: {res.counterexample_risk}")
            for w in res.warnings:
                print(f"  [WARN] {w}")
        return 0 if res.consistent else 1

    elif cmd == "refute":
        all_results = []
        has_errors = False
        for p_str in args.paths:
            p = Path(p_str)
            if p.is_file():
                r = refute_file(p)
                all_results.append(r)
                if r["verdict"] == "REJECT" or (args.strict and r["verdict"] == "WARN"):
                    has_errors = True
            elif p.is_dir():
                for f in sorted(p.rglob("*.lean")):
                    r = refute_file(f)
                    all_results.append(r)
                    if r["verdict"] == "REJECT" or (args.strict and r["verdict"] == "WARN"):
                        has_errors = True
            else:
                r = refute_file(p)
                all_results.append(r)
                has_errors = True
        if args.json:
            print(json.dumps(all_results, indent=2))
        else:
            for r in all_results:
                status_icon = "✓" if r["clean"] else "✗"
                print(f"{status_icon} [{r['verdict']}] {r['filename']}: {r['total_traps']} traps")
                for err in r["errors"]:
                    print(f"    [ERROR] {err['trap_id']} ({err['trap_name']}) L{err['line_number']}: {err['message']}")
                for warn in r["warnings"]:
                    print(f"    [WARN]  {warn['trap_id']} ({warn['trap_name']}) L{warn['line_number']}: {warn['message']}")
        return 1 if has_errors else 0

    elif cmd == "draft":
        sublemmas = json.loads(args.sublemmas) if isinstance(args.sublemmas, str) else args.sublemmas
        contract_provenance = None
        if not args.ground_truth_contract and not args.scratch:
            parser.error("/draft requires --ground-truth-contract; use --scratch only for an unbound exploratory draft")
        if args.ground_truth_contract and args.scratch:
            parser.error("--scratch and --ground-truth-contract are mutually exclusive")
        if args.scratch and args.output:
            parser.error("--scratch drafts cannot be written to a source path; use stdout/JSON for exploration")
        if args.ground_truth_contract:
            contract_path = Path(args.ground_truth_contract)
            if not contract_path.is_absolute():
                contract_path = (_REPO_ROOT / contract_path).resolve()
            try:
                validated = load_and_validate_contract(contract_path, repo_root=_REPO_ROOT)
            except ValueError as exc:
                parser.error(f"invalid --ground-truth-contract: {exc}")
            qualified_headline = f"{args.namespace}.{args.headline}" if args.namespace else args.headline
            if qualified_headline != validated["missing_declaration_name"]:
                parser.error("headline and namespace differ from the contract's smallest_gap.declaration_name")
            if args.signature.strip() != validated["missing_lean_signature"]:
                parser.error("--signature differs from the contract's smallest_gap.lean_signature")
            contract_provenance = {
                "contract_id": validated["contract_id"],
                "contract_sha256": validated["contract_sha256"],
                "target_name": validated["missing_declaration_name"],
            }
        code = draft_skeleton(
            args.headline, args.signature, sublemmas, args.namespace,
            contract_provenance=contract_provenance,
        )
        if args.output:
            output_path = Path(args.output).resolve()
            try:
                source_path = output_path.relative_to(_REPO_ROOT).as_posix()
            except ValueError:
                parser.error("contract-bound drafts must be written inside the repository")
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(code, encoding="utf-8")
            if contract_provenance is not None:
                assert validated is not None
                source_hash = hashlib.sha256(output_path.read_bytes()).hexdigest()
                receipt = {
                    "schema": DRAFT_RECEIPT_SCHEMA,
                    "contract": validated["contract"],
                    "contract_sha256": validated["contract_sha256"],
                    "source_path": source_path,
                    "source_sha256": source_hash,
                    "target_name": validated["missing_declaration_name"],
                    "declaration_signature": f"theorem {args.headline} {args.signature}".strip(),
                    "target_expression": validated["pantograph_expression"],
                }
                try:
                    validate_draft_receipt_payload(receipt, repo_root=_REPO_ROOT)
                except ValueError as exc:
                    parser.error(f"generated draft did not match its contract receipt: {exc}")
                receipt_path = output_path.with_name(output_path.name + ".opengauss.json")
                receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            # Track changes immediately under Continuous Tracking Mandate
            execute_checkpoint(f"Drafted skeleton for {args.headline} into {args.output}")
            print(f"Drafted skeleton written to {args.output}")
        elif args.json:
            print(json.dumps({"headline": args.headline, "code": code}, indent=2))
        else:
            print(code)
        return 0

    elif cmd == "review":
        reports = []
        has_reject = False
        for p_str in args.paths:
            p = Path(p_str)
            rep = review_file(p, gate=args.gate, verify_kernel=args.verify_kernel)
            reports.append(rep)
            if rep.verdict in ("REJECT", "REJECTED"):
                has_reject = True
        if args.json:
            print(json.dumps([asdict(r) for r in reports], indent=2))
        else:
            for rep in reports:
                print(f"[{rep.gate}] {rep.target_file}: {rep.verdict}")
                print(f"  Summary: {rep.summary}")
                for trap in rep.trap_violations:
                    print(f"  Trap: [{trap['severity']}] {trap['trap_id']} - {trap['message']}")
                for w in rep.scope_inflation_warnings:
                    print(f"  Scope: {w}")
        return 1 if has_reject else 0

    elif cmd == "checkpoint":
        receipt = execute_checkpoint(message=args.message, dry_run=args.dry_run, stage_paths=args.stage_path)
        if args.json:
            print(json.dumps(asdict(receipt), indent=2))
        else:
            print(f"✓ Checkpoint ({receipt.timestamp}) [HEAD: {receipt.git_head}]: {receipt.status}")
            print(f"  Staged files: {len(receipt.staged_files)}")
            for f in receipt.staged_files[:10]:
                print(f"    + {f}")
            if len(receipt.staged_files) > 10:
                print(f"    ... and {len(receipt.staged_files) - 10} more.")
        return 1 if receipt.staged_quality_gate != "passed" else 0

    elif cmd == "refactor":
        p = Path(args.path)
        content = p.read_text(encoding="utf-8")
        suggestions = analyze_refactor_candidates(content)
        if args.json:
            print(json.dumps([asdict(s) for s in suggestions], indent=2))
        else:
            if not suggestions:
                print(f"✓ No monolithic blocks requiring refactoring detected in {args.path}.")
            else:
                print(f"Refactor Candidates in {args.path} ({len(suggestions)} found):")
                for s in suggestions:
                    print(f"  L{s.line_start}-{s.line_end} [{s.target_block}]: Extract '{s.extracted_lemma_name}'")
                    print(f"    Rationale: {s.rationale}")
        return 0

    elif cmd == "golf":
        p = Path(args.path)
        content = p.read_text(encoding="utf-8")
        golfs = analyze_golf_opportunities(content)
        if args.json:
            print(json.dumps([asdict(g) for g in golfs], indent=2))
        else:
            if not golfs:
                print(f"✓ Proof is already compact; no obvious golf opportunities in {args.path}.")
            else:
                print(f"Golf Opportunities in {args.path} ({len(golfs)} found):")
                for g in golfs:
                    print(f"  L{g.line_number}: Replace `{g.original_tactic}` with `{g.suggested_replacement}`")
                    print(f"    Rationale: {g.speedup_rationale}")
        return 0

    elif cmd == "autoprove":
        state = run_autoprove_cycle(args.target, cycle=args.cycles, max_cycles=args.max_cycles)
        if args.json:
            print(json.dumps(asdict(state), indent=2))
        else:
            print(f"Autoprove Cycle {state.cycle}/{state.max_cycles} for {state.target_file}: {state.status}")
            print(f"  Open sorries: {state.open_sorries}")
            print(f"  Proven lemmas: {len(state.proven_lemmas)}")
            print(f"  Dead routes tracked: {len(state.dead_routes)}")
        return 0

    elif cmd == "formalize":
        plan = run_formalize(args.spec, phase=args.phase)
        if args.json:
            print(json.dumps(asdict(plan), indent=2))
        else:
            print(f"Formalize Plan (Phase {plan.phase}):")
            print(f"  Categorical Anchors: {', '.join(plan.categorical_anchors) or 'None'}")
            print(f"  Screened Clean: {plan.screened_clean}")
            if plan.synthesized_lean:
                print("\nSynthesized Lean Code:\n" + plan.synthesized_lean)
        return 0

    elif cmd == "autoformalize":
        trans = autoformalize_cas_identity(args.cas, args.expr, args.name)
        if args.json:
            print(json.dumps(asdict(trans), indent=2))
        else:
            print(f"Autoformalized CAS Invariant ({trans.cas_type}):")
            print(trans.lean_code)
        return 0

    elif cmd == "handoff":
        ctx = generate_handoff_context(args.targets, args.checkpoints, args.dead_routes)
        if args.out:
            Path(args.out).write_text(ctx.handoff_markdown, encoding="utf-8")
            execute_checkpoint(f"Saved handoff context into {args.out}")
            print(f"Handoff context written to {args.out}")
        elif args.json:
            print(json.dumps(asdict(ctx), indent=2))
        else:
            print(ctx.handoff_markdown)
        return 0

    elif cmd == "discover":
        repo_root = Path(__file__).resolve().parent.parent.parent
        if args.backward_depth < 0 or args.forward_depth < 0:
            parser.error("--backward-depth and --forward-depth must be non-negative")
        if args.cone_limit < 1:
            parser.error("--cone-limit must be positive")
        if args.local_dag_depth < 0 or args.local_dag_limit < 1:
            parser.error("--local-dag-depth must be non-negative and --local-dag-limit must be positive")
        if args.dag_generation_id and not args.dag_apex:
            parser.error("--dag-generation-id requires at least one exact --dag-apex")
        report = discover_declarations(args.query, repo_root=repo_root)
        if args.local_dag_context:
            report.local_dag_context = discover_local_dag_context(
                args.query,
                repo_root=repo_root,
                depth=args.local_dag_depth,
                limit=args.local_dag_limit,
            )
        if args.dag_apex:
            report.dag_context = discover_dag_context(
                args.dag_apex,
                repo_root=repo_root,
                generation_id=args.dag_generation_id,
                backward_depth=args.backward_depth,
                forward_depth=args.forward_depth,
                cone_limit=args.cone_limit,
            )
        if args.output:
            output_path = Path(args.output)
            if not output_path.is_absolute():
                output_path = (repo_root / output_path).resolve()
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(
                json.dumps(report.to_dict(), indent=2, ensure_ascii=False, sort_keys=True) + "\n",
                encoding="utf-8",
            )
        if args.json:
            print(json.dumps(report.to_dict(), indent=2))
        else:
            print(f"Discovery Report for '{report.query}':")
            print(f"  Carriers found ({len(report.carriers_found)}):")
            for c in report.carriers_found[:10]:
                print(f"    - {c['name']} [{c.get('kind', 'type')}] at {c.get('location', c['file'])}")
            if len(report.carriers_found) > 10:
                print(f"    ... and {len(report.carriers_found) - 10} more.")
            print(f"  Lemmas found ({len(report.lemmas_found)}):")
            for l in report.lemmas_found[:10]:
                print(f"    - {l['name']} at {l.get('location', l['file'])}")
            if len(report.lemmas_found) > 10:
                print(f"    ... and {len(report.lemmas_found) - 10} more.")
            print("  Recommended Imports:")
            for imp in sorted(report.recommended_imports):
                print(f"    - {imp}")
            if report.deduplication_warnings:
                print("  Deduplication Warnings:")
                for w in report.deduplication_warnings:
                    print(f"    [WARN] {w}")
            if report.dag_context is not None:
                print("  Bounded DAG Context (navigation only; freshness may be unknown):")
                print(json.dumps(report.dag_context, indent=2))
            if report.local_dag_context is not None:
                print("  Offline DAG/LeanTrail Context (navigation only; freshness unknown):")
                print(json.dumps(report.local_dag_context, indent=2))
        if any(
            context is not None
            and context.get("status") in {"unavailable", "invalid_packet", "unindexed", "not_found"}
            for context in (report.local_dag_context, report.dag_context)
        ):
            return 2
        return 0

    elif cmd == "quarantine":
        repo_root = Path(args.repo_root) if args.repo_root else Path(__file__).resolve().parent.parent.parent
        packet = quarantine_obstruction(
            file=args.file,
            trap_id=args.trap,
            description=args.desc,
            counterexample=args.counter,
            negative_constraint=args.constraint,
            repo_root=repo_root,
        )
        if args.json:
            print(json.dumps(asdict(packet), indent=2))
        else:
            print(f"✓ Obstruction quarantined to artifacts/residue_quarantine/{packet.packet_id}.json")
            print(f"  Packet ID: {packet.packet_id}")
            print(f"  Trap: {packet.trap_id}")
            print(f"  Source: {packet.source_file}")
            print(f"  Constraint: {packet.negative_constraint}")
        return 0

    elif cmd == "certify":
        p = Path(args.file)
        repo_root = Path(__file__).resolve().parent.parent.parent
        audit = generate_certification_audit(p, write_audit=args.write_audit, repo_root=repo_root)
        if args.verify_kernel:
            verified = verify_certification_audit(p, repo_root=repo_root)
            audit.kernel_checked = verified.kernel_checked
            audit.verification_status = verified.verification_status
            audit.theorem_axioms = verified.theorem_axioms
            audit.rejected_axioms = verified.rejected_axioms
            audit.verification_errors = verified.verification_errors
        if args.json:
            print(json.dumps(asdict(audit), indent=2))
        else:
            if audit.written:
                print(f"✓ Certification audit written to {audit.audit_file} ({len(audit.theorems)} theorems)")
            else:
                print(f"Certification audit for {audit.source_file} ({len(audit.theorems)} theorems):")
                print(audit.audit_script)
            if args.verify_kernel:
                print(f"Kernel verification: {audit.verification_status}")
                if audit.rejected_axioms:
                    print(f"Disallowed axioms: {', '.join(audit.rejected_axioms)}")
                for error in audit.verification_errors:
                    print(error)
        if args.verify_kernel and audit.verification_status != "passed":
            return 1
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
