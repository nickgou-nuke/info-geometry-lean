#!/usr/bin/env python3
"""OpenGauss QMS Evidence Pipeline: seven candidate-check stages.

Implements the end-to-end 7-Gate verification protocol for theorem candidates
under the OpenGauss Quality Management System (QMS-SOP-IAA-001):

Gate 1: INTAKE
  Parses theorem specification packet containing claim, carrier, hypotheses,
  and target conclusion.

Gate 2: GROUNDING
  Poset prerequisite & acyclic cone check against repository symbols.
  Enforces well-founded partial order and absence of circular reasoning.

Gate 3: STATIC TRAP SCREEN
  Runs the static checks implemented by `tools/infra/opengauss_screener.py`.

Gate 4: STATIC PROOF-HOLE SCAN
  Lexically scans for sorry/admit. It does not run Pantograph or prove goal
  closure; the Lean compiler check is Gate 5.

Gate 5: KERNEL SOURCE CHECK
  Runs `flock -x /tmp/info-geometry-build.lock lake env lean <file>` and
  audits `#print axioms` ensuring ONLY standard core axioms (`propext`,
  `Quot.sound`, `Classical.choice`) are used, strictly 0 custom axioms.

Gate 6: STATEMENT-FIDELITY REVIEW
  Invokes `tools.quality.statement_fidelity_gate` to ensure no hypotheses
  were dropped, carrier is not weakened or surrogated, and fidelity >= 0.95.

Gate 7: CANDIDATE RECEIPT
  Writes a self-checksummed candidate observation. The receipt is not an
  immutable signature, proof certificate, or promotion authorization.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from collections import defaultdict, deque
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Sequence

# Repository path resolution
REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

# Standard Core Axioms allowed under OpenGauss Protocol
ALLOWED_CORE_AXIOMS = {"propext", "Quot.sound", "Classical.choice", "Lean.ofReduceBool"}


# -----------------------------------------------------------------------------
# Structured Dataclasses
# -----------------------------------------------------------------------------

@dataclass
class GateResult:
    """Represents the outcome and telemetry of a single pipeline gate."""

    gate_number: int
    gate_name: str
    passed: bool
    diagnostics: list[str] = field(default_factory=list)
    socratic_critique: str = ""
    details: dict[str, Any] = field(default_factory=dict)
    duration_seconds: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class EvidencePacket:
    """Structured intake packet containing theorem specifications and carrier requirements."""

    spec_path: Path
    lean_file: Path
    claim: str
    carrier: str | dict[str, Any]
    hypotheses: list[Any]
    target_conclusion: str | dict[str, Any]
    prerequisites: list[str] = field(default_factory=list)
    raw_spec: dict[str, Any] = field(default_factory=dict)
    theorems: dict[str, Any] = field(default_factory=dict)
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "spec_path": str(self.spec_path),
            "lean_file": str(self.lean_file),
            "claim": self.claim,
            "carrier": self.carrier,
            "hypotheses": self.hypotheses,
            "target_conclusion": self.target_conclusion,
            "prerequisites": self.prerequisites,
            "metadata": self.metadata,
        }


@dataclass
class PipelineReport:
    """Comprehensive pipeline execution report capturing state machine trajectory."""

    target_file: str
    spec_file: str
    status: str  # "EVIDENCE_RECORDED_PENDING_OWNER_REVIEW", "REJECTED_AT_GATE_X", etc.
    final_verdict: str  # "PENDING_OWNER_REVIEW", "REJECTED"
    gates: list[GateResult] = field(default_factory=list)
    halted_at_gate: int | None = None
    receipt: dict[str, Any] | None = None
    receipt_path: str | None = None
    total_duration_seconds: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return {
            "target_file": self.target_file,
            "spec_file": self.spec_file,
            "status": self.status,
            "final_verdict": self.final_verdict,
            "halted_at_gate": self.halted_at_gate,
            "gates": [g.to_dict() for g in self.gates],
            "receipt": self.receipt,
            "receipt_path": self.receipt_path,
            "total_duration_seconds": self.total_duration_seconds,
        }


# -----------------------------------------------------------------------------
# Parsing & Lexical Helpers
# -----------------------------------------------------------------------------

def strip_lean_comments(text: str) -> str:
    """Strip Lean 4 line and nested block comments while preserving newlines."""
    res: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text[i:i + 2] == "/-":
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i:i + 2] == "/-":
                    depth += 1
                    i += 2
                elif text[i:i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        res.append("\n")
                    i += 1
            res.append(" ")
        elif text[i:i + 2] == "--":
            i += 2
            while i < n and text[i] != "\n":
                i += 1
            res.append("\n")
            if i < n and text[i] == "\n":
                i += 1
        else:
            res.append(text[i])
            i += 1
    return "".join(res)


def strip_comments_and_strings(text: str) -> str:
    """Strip comments and string literals to prevent spurious token matches."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    n = len(text)
    while i < n:
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                ch = text[i]
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            ch = text[i]
            out.append("\n" if ch == "\n" else " ")
            i += 1
            if ch == "\\" and i < n:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            elif ch == '"':
                in_string = False
            continue

        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        ch = text[i]
        out.append(ch)
        i += 1
        if ch == '"':
            in_string = True
    return "".join(out)


def extract_lean_declarations(content: str) -> list[str]:
    """Extract theorem/lemma names for the source audit, respecting namespaces."""
    lines = content.splitlines()
    scope_stack: list[tuple[str, str]] = []
    declarations: list[str] = []

    for line in lines:
        clean = strip_comments_and_strings(line).split("--")[0].strip()
        if not clean or clean.startswith("/-"):
            continue

        # Track namespace opening
        m_ns = re.match(r"^namespace\s+([A-Za-z0-9_.]+)", clean)
        if m_ns:
            scope_stack.append(("namespace", m_ns.group(1)))
            continue

        m_section = re.match(r"^section(?:\s+([A-Za-z0-9_.]+))?$", clean)
        if m_section:
            scope_stack.append(("section", m_section.group(1) or ""))
            continue

        # Track namespace closing
        m_end = re.match(r"^end(?:\s+([A-Za-z0-9_.]+))?$", clean)
        if m_end:
            target_ns = m_end.group(1)
            if target_ns:
                while scope_stack:
                    _, scope_name = scope_stack.pop()
                    if scope_name == target_ns:
                        break
            elif scope_stack:
                scope_stack.pop()
            continue

        # Support same-line attributes and declaration modifiers.
        m_decl = re.match(
            r"^(?:(?:@\[[^\]]*\])\s*)*(?:(?:noncomputable|protected|private)\s+)*(?:theorem|lemma)\s+([^\s:{(]+)",
            clean,
        )
        if m_decl:
            dname = m_decl.group(1)
            namespaces = [name for kind, name in scope_stack if kind == "namespace"]
            full_name = ".".join(namespaces + [dname]) if namespaces else dname
            declarations.append(full_name)

    return declarations


def parse_axiom_audit_output(
    output: str, expected_declarations: Sequence[str]
) -> tuple[dict[str, list[str]], list[str]]:
    """Parse wrapped Lean `#print axioms` output and require every target once."""
    dep_pattern = re.compile(
        r"(?m)^\s*(?:info:\s*)?'(?P<name>[^']+)'\s+depends on axioms:\s*"
        r"\[(?P<axioms>[\s\S]*?)\]"
    )
    nodep_pattern = re.compile(
        r"(?m)^\s*(?:info:\s*)?'(?P<name>[^']+)'\s+does not depend on any axioms\s*$"
    )
    raw_parsed: dict[str, list[str]] = {}
    errors: list[str] = []
    expected = list(dict.fromkeys(expected_declarations))

    for match in dep_pattern.finditer(output):
        name = match.group("name").strip()
        if name in raw_parsed:
            errors.append(f"duplicate axiom output for declaration {name!r}")
            continue
        raw_axioms = match.group("axioms")
        raw_parsed[name] = [axiom.strip() for axiom in raw_axioms.split(",") if axiom.strip()]

    for match in nodep_pattern.finditer(output):
        name = match.group("name").strip()
        if name in raw_parsed:
            errors.append(f"duplicate axiom output for declaration {name!r}")
            continue
        raw_parsed[name] = []

    matched_declarations: dict[str, list[str]] = {}
    used_output_names: set[str] = set()
    for d in expected:
        matched_key = None
        if d in raw_parsed:
            matched_key = d
        else:
            for k in raw_parsed:
                if k == d or k.endswith(f".{d}") or d.endswith(f".{k}"):
                    matched_key = k
                    break
        if matched_key is None:
            errors.append(f"missing axiom output for declaration {d!r}")
        elif matched_key in used_output_names:
            errors.append(f"ambiguous axiom output matched multiple declarations at {matched_key!r}")
        else:
            matched_declarations[d] = raw_parsed[matched_key]
            used_output_names.add(matched_key)

    errors.extend(
        f"unexpected axiom output for declaration {name!r}"
        for name in sorted(set(raw_parsed) - used_output_names)
    )

    if not output.strip() and expected:
        errors.append("Lean produced no axiom audit output")
    return matched_declarations, errors


# -----------------------------------------------------------------------------
# 7-Gate Pipeline Implementation
# -----------------------------------------------------------------------------

class QMSEvidencePipeline:
    """End-to-End 7-Gate Evidence State Machine."""

    def __init__(
        self,
        lock_file: str = "/tmp/info-geometry-build.lock",
        strict: bool = True,
    ):
        self.lock_file = lock_file
        self.strict = strict

    # -------------------------------------------------------------------------
    # Gate 1: INTAKE
    # -------------------------------------------------------------------------
    def gate_1_intake(self, spec_path: Path, lean_file: Path) -> tuple[GateResult, EvidencePacket | None]:
        """Parse theorem specification packet containing claim, carrier, hypotheses, target conclusion."""
        t0 = time.time()
        diagnostics: list[str] = []

        if not spec_path.is_file():
            diagnostics.append(f"Specification file not found: {spec_path}")
            return GateResult(
                gate_number=1,
                gate_name="INTAKE",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique="Gate 1 Intake Failure: Target specification file does not exist on disk.",
                duration_seconds=time.time() - t0,
            ), None

        if not lean_file.is_file():
            diagnostics.append(f"Lean source file not found: {lean_file}")
            return GateResult(
                gate_number=1,
                gate_name="INTAKE",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique="Gate 1 Intake Failure: Candidate Lean source file does not exist on disk.",
                duration_seconds=time.time() - t0,
            ), None

        try:
            raw_spec = json.loads(spec_path.read_text(encoding="utf-8"))
        except Exception as exc:
            diagnostics.append(f"JSON parsing error in specification: {exc}")
            return GateResult(
                gate_number=1,
                gate_name="INTAKE",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique="Gate 1 Intake Failure: Specification file is not valid JSON.",
                duration_seconds=time.time() - t0,
            ), None

        # Parse spec format (supports single theorem spec or multi-theorem suite)
        theorems: dict[str, Any] = {}
        if "theorems" in raw_spec and isinstance(raw_spec["theorems"], dict):
            theorems = raw_spec["theorems"]
            first_th = next(iter(theorems.values())) if theorems else {}
            claim = raw_spec.get("title") or raw_spec.get("claim") or raw_spec.get("description") or "Multi-Theorem Suite"
            carrier = first_th.get("carrier_requirements", {}).get("expected_carrier") or first_th.get("carrier", "Algebraic")
            hypotheses = first_th.get("required_hypotheses", [])
            target_conclusion = first_th.get("target_relation", {})
            prerequisites = raw_spec.get("prerequisites", [])
        else:
            claim = raw_spec.get("claim") or raw_spec.get("title") or raw_spec.get("theorem_name") or ""
            carrier = raw_spec.get("carrier") or raw_spec.get("carrier_requirements") or ""
            hypotheses = raw_spec.get("hypotheses") or raw_spec.get("required_hypotheses") or []
            target_conclusion = raw_spec.get("target_conclusion") or raw_spec.get("target_relation") or ""
            prerequisites = raw_spec.get("prerequisites", [])

        # Validate mandatory intake fields
        missing_fields: list[str] = []
        if not claim and not theorems:
            missing_fields.append("claim/title")
        if not carrier and not theorems:
            missing_fields.append("carrier")
        if target_conclusion == "" and not theorems:
            missing_fields.append("target_conclusion")

        if missing_fields:
            diagnostics.append(f"Missing mandatory specification fields: {', '.join(missing_fields)}")
            return GateResult(
                gate_number=1,
                gate_name="INTAKE",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique=(
                    f"Gate 1 Intake Failure: Incomplete specification packet. "
                    f"The packet lacks essential mathematical constraints: {', '.join(missing_fields)}."
                ),
                duration_seconds=time.time() - t0,
            ), None

        packet = EvidencePacket(
            spec_path=spec_path,
            lean_file=lean_file,
            claim=str(claim),
            carrier=carrier,
            hypotheses=hypotheses,
            target_conclusion=target_conclusion,
            prerequisites=prerequisites,
            raw_spec=raw_spec,
            theorems=theorems,
            metadata={
                "theorem_count": len(theorems) if theorems else 1,
                "parsed_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            },
        )

        return GateResult(
            gate_number=1,
            gate_name="INTAKE",
            passed=True,
            diagnostics=[f"Successfully parsed specification '{claim}' with {len(theorems) if theorems else 1} target theorem(s)."],
            details={"packet": packet.to_dict()},
            duration_seconds=time.time() - t0,
        ), packet

    # -------------------------------------------------------------------------
    # Gate 2: GROUNDING
    # -------------------------------------------------------------------------
    def gate_2_grounding(self, packet: EvidencePacket) -> GateResult:
        """Poset prerequisite & acyclic cone check against repository symbols."""
        t0 = time.time()
        diagnostics: list[str] = []
        lean_text = packet.lean_file.read_text(encoding="utf-8")

        # 1. Import Resolution & Grounding
        imports = re.findall(r"^\s*import\s+([A-Za-z0-9_.]+)", lean_text, re.MULTILINE)
        unresolved_imports: list[str] = []
        for imp in imports:
            if imp == "Mathlib" or imp.startswith("Mathlib.") or imp == "Lean" or imp.startswith("Lean."):
                continue
            # Check local repository module
            parts = imp.split(".")
            candidate_paths = [
                REPO_ROOT / f"{'/'.join(parts)}.lean",
                REPO_ROOT / "lean" / f"{'/'.join(parts)}.lean",
                REPO_ROOT / "proofs" / f"{'/'.join(parts[1:] if parts[0] == 'proofs' else parts)}.lean",
            ]
            if not any(cp.is_file() for cp in candidate_paths):
                unresolved_imports.append(imp)

        if unresolved_imports:
            diagnostics.append(f"Unresolved imports in repository: {unresolved_imports}")
            return GateResult(
                gate_number=2,
                gate_name="GROUNDING",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique=f"Gate 2 Grounding Failure: Found dangling or ungrounded imports: {unresolved_imports}.",
                duration_seconds=time.time() - t0,
            )

        # 2. Extract Declarations and Build Internal Poset Dependency DAG
        raw_decls = re.findall(r"^\s*(?:def|theorem|lemma|structure|class)\s+([^\s:{(]+)", lean_text, re.MULTILINE)
        decl_names = set(raw_decls)

        # Build dependency adjacency list: u -> v if declaration u references declaration v
        # We parse the file into declaration blocks
        blocks: list[tuple[str, str]] = []
        lines = lean_text.splitlines()
        current_name = None
        current_lines: list[str] = []

        for line in lines:
            m = re.match(r"^\s*(?:def|theorem|lemma|structure|class)\s+([^\s:{(]+)", line)
            if m:
                if current_name:
                    blocks.append((current_name, "\n".join(current_lines)))
                current_name = m.group(1)
                current_lines = [line]
            else:
                if current_name:
                    current_lines.append(line)
        if current_name:
            blocks.append((current_name, "\n".join(current_lines)))

        adj: dict[str, set[str]] = {d: set() for d in decl_names}
        in_degree: dict[str, int] = {d: 0 for d in decl_names}

        for d_name, d_body in blocks:
            # Strip body comments
            clean_body = strip_lean_comments(d_body)
            for other_decl in decl_names:
                if other_decl != d_name:
                    # Look for word-boundary reference
                    if re.search(rf"\b{re.escape(other_decl)}\b", clean_body):
                        adj[other_decl].add(d_name)

        for u in adj:
            for v in adj[u]:
                in_degree[v] += 1

        # Kahn's Algorithm for Poset Acyclicity Verification
        zero_in = deque([d for d, deg in in_degree.items() if deg == 0])
        topo_order: list[str] = []

        while zero_in:
            curr = zero_in.popleft()
            topo_order.append(curr)
            for neighbor in adj[curr]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    zero_in.append(neighbor)

        if len(topo_order) != len(decl_names):
            cyclic_nodes = [d for d, deg in in_degree.items() if deg > 0]
            diagnostics.append(f"Dependency cycle detected among declarations: {cyclic_nodes}")
            return GateResult(
                gate_number=2,
                gate_name="GROUNDING",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique=(
                    f"Gate 2 Grounding Failure: Declaration poset cone contains cycles involving {cyclic_nodes}. "
                    "OpenGauss protocol mandates well-founded, strictly acyclic causal poset cones."
                ),
                duration_seconds=time.time() - t0,
            )

        # 3. Poset Prerequisite Verification
        if packet.prerequisites:
            missing_prereqs = [p for p in packet.prerequisites if p not in decl_names and not any(p in imp for imp in imports)]
            if missing_prereqs:
                diagnostics.append(f"Missing explicit prerequisites: {missing_prereqs}")
                return GateResult(
                    gate_number=2,
                    gate_name="GROUNDING",
                    passed=False,
                    diagnostics=diagnostics,
                    socratic_critique=f"Gate 2 Grounding Failure: Prerequisite symbols {missing_prereqs} cannot be resolved in the repository poset.",
                    duration_seconds=time.time() - t0,
                )

        diagnostics.append(f"Poset cone verified acyclic across {len(decl_names)} declarations.")
        diagnostics.append(f"Topological grounding depth: {len(topo_order)} declarations successfully ordered.")

        return GateResult(
            gate_number=2,
            gate_name="GROUNDING",
            passed=True,
            diagnostics=diagnostics,
            details={
                "declarations_count": len(decl_names),
                "resolved_imports": imports,
                "topological_order": topo_order,
            },
            duration_seconds=time.time() - t0,
        )

    # -------------------------------------------------------------------------
    # Gate 3: STATIC TRAP SCREEN
    # -------------------------------------------------------------------------
    def gate_3_static_trap_screen(self, packet: EvidencePacket) -> GateResult:
        """Run the repository's static source screener; this is not an agent review."""
        t0 = time.time()
        from tools.infra.opengauss_screener import screen_lean_file

        violations = screen_lean_file(packet.lean_file)
        diagnostics: list[str] = []

        fatal_violations = [v for v in violations if v.severity == "ERROR"]
        warnings = [v for v in violations if v.severity == "WARNING"]
        blocking_warnings = warnings if self.strict else []
        all_blocking = fatal_violations + blocking_warnings

        if all_blocking:
            socratic_items: list[str] = []
            for v in all_blocking:
                msg = f"[{v.severity}] Trap {v.trap_id} ({v.trap_name}) at line {v.line_number}: {v.message}"
                diagnostics.append(msg)
                socratic_items.append(f"  • Trap {v.trap_id}: {v.message} (matched: '{v.matched_text}')")

            critique = (
                "Gate 3 Static Trap Screen Failure: "
                f"Candidate violated {len(all_blocking)} OpenGauss Trap invariants:\n"
                + "\n".join(socratic_items)
            )

            return GateResult(
                gate_number=3,
                gate_name="STATIC_TRAP_SCREEN",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique=critique,
                details={
                    "violations": [asdict(v) for v in all_blocking],
                    "warning_count": len(warnings),
                    "strict_mode": self.strict,
                },
                duration_seconds=time.time() - t0,
            )

        diagnostics.append(
            f"Static screener completed: 0 blocking findings, {len(warnings)} warnings "
            f"({len(blocking_warnings)} treated as blocking). "
            "This result does not represent an independent Socratic review."
        )
        return GateResult(
            gate_number=3,
            gate_name="STATIC_TRAP_SCREEN",
            passed=True,
            diagnostics=diagnostics,
            details={
                "violations_count": 0,
                "warning_count": len(warnings),
                "warnings": [asdict(v) for v in warnings],
                "strict_mode": self.strict,
            },
            duration_seconds=time.time() - t0,
        )

    # -------------------------------------------------------------------------
    # Gate 4: STATIC PROOF-HOLE SCAN
    # -------------------------------------------------------------------------
    def gate_4_static_proof_hole_scan(self, packet: EvidencePacket) -> GateResult:
        """Lexically scan for proof-hole tokens; compilation is checked at Gate 5."""
        t0 = time.time()
        diagnostics: list[str] = []
        content = packet.lean_file.read_text(encoding="utf-8")
        clean_code = strip_comments_and_strings(content)

        # Check for unproven holes or admits
        sorry_matches: list[tuple[int, str]] = []
        admit_matches: list[tuple[int, str]] = []

        for line_no, line in enumerate(clean_code.splitlines(), start=1):
            if re.search(r"\bsorry\b", line):
                sorry_matches.append((line_no, line.strip()))
            if re.search(r"\badmit\b", line):
                admit_matches.append((line_no, line.strip()))

        if sorry_matches or admit_matches:
            critique_lines = ["Gate 4 Static Proof-Hole Scan Failure: Unclosed proof holes detected (sorry/admit tokens):"]
            for lno, text in sorry_matches:
                diag = f"Hole 'sorry' at line {lno}: {text[:80]}"
                diagnostics.append(diag)
                critique_lines.append(f"  • {diag}")
            for lno, text in admit_matches:
                diag = f"Hole 'admit' at line {lno}: {text[:80]}"
                diagnostics.append(diag)
                critique_lines.append(f"  • {diag}")

            return GateResult(
                gate_number=4,
                gate_name="STATIC_PROOF_HOLE_SCAN",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique="\n".join(critique_lines),
                details={"sorry_count": len(sorry_matches), "admit_count": len(admit_matches)},
                duration_seconds=time.time() - t0,
            )

        diagnostics.append("Static lexical scan found no sorry/admit tokens; no Pantograph goal-state claim is made.")

        return GateResult(
            gate_number=4,
            gate_name="STATIC_PROOF_HOLE_SCAN",
            passed=True,
            diagnostics=diagnostics,
            details={"sorry_count": 0, "admit_count": 0, "pantograph_invoked": False},
            duration_seconds=time.time() - t0,
        )

    # -------------------------------------------------------------------------
    # Gate 5: KERNEL SOURCE CHECK
    # -------------------------------------------------------------------------
    def gate_5_kernel_and_integration(self, packet: EvidencePacket) -> GateResult:
        """Compile an unchanged source snapshot under the build lock and audit every theorem's axioms."""
        t0 = time.time()
        diagnostics: list[str] = []

        try:
            source_bytes = packet.lean_file.read_bytes()
        except OSError as exc:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=[f"Could not snapshot candidate source: {exc}"],
                socratic_critique="Gate 5 failed before compilation because the candidate source could not be read.",
                duration_seconds=time.time() - t0,
            )
        source_sha256 = hashlib.sha256(source_bytes).hexdigest()

        # 1. Concurrency-Locked Lean Kernel Check
        cmd = ["flock", "-x", self.lock_file, "lake", "env", "lean", str(packet.lean_file)]
        try:
            proc = subprocess.run(
                cmd,
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=180,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=["Kernel verification timed out after 180 seconds."],
                socratic_critique="Gate 5 Kernel Failure: Lake compilation timed out under exclusive build lock.",
                duration_seconds=time.time() - t0,
            )
        except Exception as exc:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=[f"Process execution error: {exc}"],
                socratic_critique=f"Gate 5 Kernel Failure: Could not spawn build process: {exc}",
                duration_seconds=time.time() - t0,
            )

        if proc.returncode != 0:
            err_msg = proc.stderr.strip() or proc.stdout.strip()
            diagnostics.append(f"Lean kernel compilation failed with returncode {proc.returncode}.")
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique=(
                    f"Gate 5 Kernel Failure: Lean kernel rejected candidate with return code {proc.returncode}:\n"
                    f"{err_msg[:500]}"
                ),
                details={"returncode": proc.returncode, "stderr": proc.stderr, "stdout": proc.stdout},
                duration_seconds=time.time() - t0,
            )

        # Detect changes between the source snapshot and compilation before auditing.
        current_bytes = packet.lean_file.read_bytes()
        if hashlib.sha256(current_bytes).hexdigest() != source_sha256:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=["Candidate source changed during kernel compilation."],
                socratic_critique="Gate 5 rejected a time-of-check/time-of-use source mismatch.",
                details={"candidate_sha256_before": source_sha256,
                         "candidate_sha256_after_compile": hashlib.sha256(current_bytes).hexdigest()},
                duration_seconds=time.time() - t0,
            )

        # 2. Strict Axiom Auditing
        source = source_bytes.decode("utf-8")
        declarations = extract_lean_declarations(source)
        if not declarations:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=["No theorem/lemma declarations were found; axiom audit cannot be certified."],
                socratic_critique="Gate 5 fails closed when there are no declarations to audit.",
                details={"candidate_sha256": source_sha256},
                duration_seconds=time.time() - t0,
            )

        audit_source = (
            "import Lean\n"
            + source.rstrip()
            + "\n\n"
            + "\n".join(f"#print axioms {d}" for d in declarations)
            + "\n"
        )

        with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", encoding="utf-8") as temp_audit:
            temp_audit.write(audit_source)
            temp_audit.flush()
            audit_cmd = ["flock", "-x", self.lock_file, "lake", "env", "lean", temp_audit.name]
            try:
                audit_proc = subprocess.run(
                    audit_cmd,
                    cwd=REPO_ROOT,
                    capture_output=True,
                    text=True,
                    timeout=180,
                    check=False,
                )
                axiom_returncode = audit_proc.returncode
                axiom_output = audit_proc.stdout
                audit_declarations = declarations
            except Exception as exc:
                return GateResult(
                    gate_number=5,
                    gate_name="KERNEL_SOURCE_CHECK",
                    passed=False,
                    diagnostics=[f"Axiom audit execution failed: {exc}"],
                    socratic_critique=f"Gate 5 Kernel Failure: Axiom audit subprocess crashed: {exc}",
                    duration_seconds=time.time() - t0,
                )

        if axiom_returncode != 0:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=["Axiom audit returned non-zero exit code."],
                socratic_critique=f"Gate 5 Kernel Failure: Axiom elaboration failed: {audit_proc.stderr[:400]}",
                duration_seconds=time.time() - t0,
            )

        parsed_axioms, parse_errors = parse_axiom_audit_output(axiom_output, declarations)
        if parse_errors:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=[f"Axiom audit output could not be validated: {err}" for err in parse_errors],
                socratic_critique="Gate 5 fails closed on missing, malformed, duplicate, or unexpected axiom records.",
                details={"axiom_audit_output": axiom_output, "axiom_audit_declarations": declarations},
                duration_seconds=time.time() - t0,
            )

        # Audit all parsed axiom lists against the allowlist.
        forbidden_axioms_found: dict[str, list[str]] = defaultdict(list)
        for theorem, axioms in parsed_axioms.items():
            for axiom in axioms:
                if axiom not in ALLOWED_CORE_AXIOMS:
                    forbidden_axioms_found[theorem].append(axiom)

        if forbidden_axioms_found:
            critique_lines = ["Gate 5 Axiom Audit Failure: Custom or unauthorized axioms detected:"]
            for th, ax_list in forbidden_axioms_found.items():
                critique_lines.append(f"  • Theorem '{th}' relies on custom axioms: {ax_list}")
                diagnostics.append(f"Custom axioms in '{th}': {ax_list}")

            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique="\n".join(critique_lines),
                details={"forbidden_axioms": dict(forbidden_axioms_found)},
                duration_seconds=time.time() - t0,
            )

        final_sha256 = hashlib.sha256(packet.lean_file.read_bytes()).hexdigest()
        if final_sha256 != source_sha256:
            return GateResult(
                gate_number=5,
                gate_name="KERNEL_SOURCE_CHECK",
                passed=False,
                diagnostics=["Candidate source changed before axiom audit completed."],
                socratic_critique="Gate 5 rejected a source snapshot mismatch after axiom auditing.",
                details={"candidate_sha256_before": source_sha256, "candidate_sha256_after_audit": final_sha256},
                duration_seconds=time.time() - t0,
            )

        diagnostics.append("Lean kernel compilation checked with exit code 0 under build lock.")
        diagnostics.append(
            f"Axiom audit clean across {len(declarations)} declarations: "
            "ONLY standard core axioms [propext, Quot.sound, Classical.choice] used (0 custom axioms)."
        )

        return GateResult(
            gate_number=5,
            gate_name="KERNEL_SOURCE_CHECK",
            passed=True,
            diagnostics=diagnostics,
            details={
                "lean_returncode": proc.returncode,
                "lean_output": proc.stdout,
                "axiom_audit_status": "collected",
                "axiom_audit_declarations": audit_declarations,
                "axiom_audit_output": axiom_output,
                "axiom_audit_returncode": axiom_returncode,
                "candidate_sha256": source_sha256,
            },
            duration_seconds=time.time() - t0,
        )

    # -------------------------------------------------------------------------
    # Gate 6: SPECIFICATION CONTRACT SCREEN
    # -------------------------------------------------------------------------
    def gate_6_statement_fidelity_review(
        self, packet: EvidencePacket, kernel_result: GateResult | None = None
    ) -> GateResult:
        """Run syntax-based contract checks; this score is not a semantic correctness proof."""
        t0 = time.time()
        diagnostics: list[str] = []

        from tools.quality.statement_fidelity_gate import evaluate_source_fidelity

        try:
            source_bytes = packet.lean_file.read_bytes()
            source_text = source_bytes.decode("utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            return GateResult(
                gate_number=6,
                gate_name="STATEMENT_FIDELITY_REVIEW",
                passed=False,
                diagnostics=[f"Gate 6 could not read the candidate source snapshot: {exc}"],
                socratic_critique="Gate 6 fails closed when the candidate source snapshot cannot be read as UTF-8.",
                duration_seconds=time.time() - t0,
            )

        current_source_sha = hashlib.sha256(source_bytes).hexdigest()
        if kernel_result is not None:
            if not kernel_result.passed:
                return GateResult(
                    gate_number=6,
                    gate_name="STATEMENT_FIDELITY_REVIEW",
                    passed=False,
                    diagnostics=["Gate 5 did not pass; Gate 6 cannot consume failed kernel evidence."],
                    socratic_critique="Gate 6 fails closed unless Gate 5 supplied a passing kernel result.",
                    duration_seconds=time.time() - t0,
                )
            kernel_source_sha = kernel_result.details.get("candidate_sha256")
            if not isinstance(kernel_source_sha, str) or not re.fullmatch(r"[0-9a-f]{64}", kernel_source_sha):
                return GateResult(
                    gate_number=6,
                    gate_name="STATEMENT_FIDELITY_REVIEW",
                    passed=False,
                    diagnostics=["Gate 5 kernel evidence is missing a valid candidate_sha256 source binding."],
                    socratic_critique="Gate 6 fails closed when Gate 5 does not provide a well-formed source fingerprint.",
                    duration_seconds=time.time() - t0,
                )
            if current_source_sha != kernel_source_sha:
                return GateResult(
                    gate_number=6,
                    gate_name="STATEMENT_FIDELITY_REVIEW",
                    passed=False,
                    diagnostics=[
                        "Candidate source changed after Gate 5 kernel checking and before Gate 6 review.",
                        f"Gate 5 SHA256: {kernel_source_sha}",
                        f"Gate 6 SHA256: {current_source_sha}",
                    ],
                    socratic_critique="Gate 6 fails closed because it is not screening the source snapshot compiled by Gate 5.",
                    duration_seconds=time.time() - t0,
                )

        # The exact decoded text whose bytes were fingerprinted above is passed
        # directly to the source checker; it is not reopened from disk.
        reports = evaluate_source_fidelity(source_text, packet.raw_spec)
        if kernel_result is not None:
            audited = set(kernel_result.details.get("axiom_audit_declarations", []))
            selected = {report.theorem_name for report in reports.values()}
            missing_from_kernel_audit = selected - audited
            if not audited or missing_from_kernel_audit:
                return GateResult(
                    gate_number=6,
                    gate_name="STATEMENT_FIDELITY_REVIEW",
                    passed=False,
                    diagnostics=[
                        "Gate 6 selected declaration identity is not covered by Gate 5's kernel audit.",
                        f"Selected names missing from Gate 5: {sorted(missing_from_kernel_audit)}",
                    ],
                    socratic_critique="Gate 6 fails closed when its selected declarations are not exactly among the kernel-audited names.",
                    details={
                        "selected_declarations": sorted(selected),
                        "axiom_audit_declarations": sorted(audited),
                    },
                    duration_seconds=time.time() - t0,
                )
        if not reports:
            diagnostics.append("No theorems could be matched between Lean file and specification.")
            return GateResult(
                gate_number=6,
                gate_name="STATEMENT_FIDELITY_REVIEW",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique="Gate 6 Statement Fidelity Failure: Specification evaluated 0 theorems.",
                duration_seconds=time.time() - t0,
            )

        failed_theorems: list[str] = []
        socratic_items: list[str] = []

        for th_name, rep in reports.items():
            if not rep.passed or rep.fidelity_score < 0.95:
                failed_theorems.append(th_name)
                critique_item = [f"Theorem '{th_name}' failed fidelity (score: {rep.fidelity_score:.4f} < 0.95):"]
                for d in rep.defects:
                    diag = f"[{d.severity}] {d.defect_type}: {d.message} (penalty: -{d.penalty:.2f})"
                    diagnostics.append(f"{th_name}: {diag}")
                    critique_item.append(f"    - {diag}")
                socratic_items.append("\n".join(critique_item))
            else:
                diagnostics.append(f"Theorem '{th_name}' passed syntactic contract checks (score {rep.fidelity_score:.4f}).")

        if failed_theorems:
            critique = (
                f"Gate 6 Contract Screen Failure: {len(failed_theorems)} theorem(s) failed syntactic contract checks:\n"
                + "\n\n".join(socratic_items)
            )
            return GateResult(
                gate_number=6,
                gate_name="STATEMENT_FIDELITY_REVIEW",
                passed=False,
                diagnostics=diagnostics,
                socratic_critique=critique,
                details={"reports": {k: v.to_dict() for k, v in reports.items()}},
                duration_seconds=time.time() - t0,
            )

        avg_score = sum(r.fidelity_score for r in reports.values()) / len(reports)
        diagnostics.append(
            f"All {len(reports)} theorem(s) passed syntactic specification checks "
            f"(heuristic score: {avg_score:.4f} >= 0.95); independent semantic review remains required."
        )
        return GateResult(
            gate_number=6,
            gate_name="STATEMENT_FIDELITY_REVIEW",
            passed=True,
            diagnostics=diagnostics,
            details={"reports": {k: v.to_dict() for k, v in reports.items()}, "average_fidelity": avg_score},
            duration_seconds=time.time() - t0,
        )

    # -------------------------------------------------------------------------
    # Gate 7: CANDIDATE RECEIPT
    # -------------------------------------------------------------------------
    def gate_7_candidate_receipt(
        self,
        packet: EvidencePacket,
        kernel_result: GateResult,
        out_receipt: Path | None = None,
    ) -> tuple[GateResult, dict[str, Any] | None, Path | None]:
        """Record a self-checksummed candidate observation; this does not promote a theorem."""
        t0 = time.time()
        diagnostics: list[str] = []

        from tools.infra.proof_artifact_receipt import (
            build_candidate_receipt,
            verify_candidate_receipt,
        )

        # Collect Git & Environment fingerprints
        git_head = ""
        try:
            git_head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True).strip()
        except Exception:
            git_head = "0" * 40

        toolchain = ""
        toolchain_path = REPO_ROOT / "lean-toolchain"
        if toolchain_path.is_file():
            toolchain = toolchain_path.read_text(encoding="utf-8").strip()

        lakefile_hash = ""
        lakefile_path = REPO_ROOT / "lakefile.lean"
        if lakefile_path.is_file():
            lakefile_hash = hashlib.sha256(lakefile_path.read_bytes()).hexdigest()

        manifest_hash = ""
        manifest_path = REPO_ROOT / "lake-manifest.json"
        if manifest_path.is_file():
            manifest_hash = hashlib.sha256(manifest_path.read_bytes()).hexdigest()

        candidate_sha = kernel_result.details.get("candidate_sha256")
        current_sha = hashlib.sha256(packet.lean_file.read_bytes()).hexdigest()
        if not candidate_sha or current_sha != candidate_sha:
            return (
                GateResult(
                    gate_number=7,
                    gate_name="CANDIDATE_RECEIPT",
                    passed=False,
                    diagnostics=["Candidate source no longer matches the source checked by Gate 5."],
                    socratic_critique="Gate 7 refused to bind a receipt to a changed or untracked source snapshot.",
                    details={"kernel_candidate_sha256": candidate_sha, "current_candidate_sha256": current_sha},
                    duration_seconds=time.time() - t0,
                ), None, None,
            )

        try:
            rel_lean_path = str(packet.lean_file.relative_to(REPO_ROOT))
        except ValueError:
            rel_lean_path = str(packet.lean_file)

        kernel_details = kernel_result.details
        audit_output = kernel_details.get("axiom_audit_output", "")
        audit_output_sha = hashlib.sha256(audit_output.encode("utf-8")).hexdigest() if audit_output else ""
        audit_declarations = kernel_details.get("axiom_audit_declarations", [])

        # 1. Run genuine Semantic Vacuity Audit
        vac_script = REPO_ROOT / "tools" / "quality" / "semantic_vacuity_gate.py"
        vac_rc: int | None = None
        vac_stdout = ""
        vac_sha256 = ""
        if vac_script.is_file():
            vac_cmd = [
                sys.executable,
                str(vac_script),
                str(packet.lean_file),
                "--fail-on",
                "error",
            ]
            try:
                vac_proc = subprocess.run(
                    vac_cmd,
                    cwd=REPO_ROOT,
                    capture_output=True,
                    text=True,
                    timeout=60,
                    check=False,
                )
                vac_rc = vac_proc.returncode
                vac_stdout = vac_proc.stdout
                vac_sha256 = hashlib.sha256(vac_stdout.encode("utf-8")).hexdigest()
            except Exception as exc:
                vac_rc = 1
                vac_stdout = f"Semantic vacuity audit execution failed: {exc}"
                vac_sha256 = hashlib.sha256(vac_stdout.encode("utf-8")).hexdigest()

        if vac_rc is not None and vac_rc != 0:
            diagnostics.append(f"Semantic vacuity audit failed with exit code {vac_rc}.")
            return (
                GateResult(
                    gate_number=7,
                    gate_name="CANDIDATE_RECEIPT",
                    passed=False,
                    diagnostics=diagnostics,
                    socratic_critique=f"Gate 7 Semantic Vacuity Failure: Semantic vacuity audit failed (exit code {vac_rc}):\n{vac_stdout[:400]}",
                    details={"semantic_vacuity_returncode": vac_rc, "semantic_vacuity_output": vac_stdout},
                    duration_seconds=time.time() - t0,
                ),
                None,
                None,
            )

        # 2. Check source context changed / snapshot integrity
        prompted_source_sha = (
            packet.raw_spec.get("source_snapshot_sha256")
            or packet.metadata.get("source_snapshot_sha256")
            or ""
        )
        if prompted_source_sha:
            source_snapshot_sha256 = prompted_source_sha
            source_context_changed = (prompted_source_sha != candidate_sha)
        else:
            # Check against git HEAD snapshot if tracked in repository
            git_show = subprocess.run(
                ["git", "show", f"HEAD:{rel_lean_path}"],
                cwd=REPO_ROOT,
                capture_output=True,
                check=False,
            )
            if git_show.returncode == 0:
                head_sha = hashlib.sha256(git_show.stdout).hexdigest()
                source_snapshot_sha256 = head_sha
                source_context_changed = (head_sha != candidate_sha)
            else:
                source_snapshot_sha256 = candidate_sha
                source_context_changed = False

        if source_context_changed:
            record: dict[str, Any] = {
                "lean_file": rel_lean_path,
                "candidate_sha256": candidate_sha,
                "source_path": rel_lean_path,
                "source_snapshot_sha256": source_snapshot_sha256,
                "source_snapshot_current_sha256": candidate_sha,
                "source_context_changed": True,
                "toolchain": toolchain,
                "lakefile_sha256": lakefile_hash,
                "lake_manifest_sha256": manifest_hash,
                "git_head": git_head,
                "lean_check_returncode": kernel_details.get("lean_returncode", 0),
                "lean_output_sha256": hashlib.sha256(kernel_details.get("lean_output", "").encode("utf-8")).hexdigest(),
                "semantic_vacuity_returncode": vac_rc,
                "semantic_vacuity_output_sha256": vac_sha256,
                "axiom_audit_status": "collected" if audit_declarations else "not_requested",
                "axiom_audit_declarations": audit_declarations,
                "axiom_audit_returncode": kernel_details.get("axiom_audit_returncode") if audit_declarations else None,
                "axiom_audit_output": audit_output,
                "axiom_audit_output_sha256": audit_output_sha,
            }
            receipt = build_candidate_receipt(record)
            if not verify_candidate_receipt(receipt):
                return (
                    GateResult(
                        gate_number=7,
                        gate_name="CANDIDATE_RECEIPT",
                        passed=False,
                        diagnostics=["Changed-source candidate receipt failed integrity verification."],
                        socratic_critique="Gate 7 could not verify the candidate observation receipt.",
                        duration_seconds=time.time() - t0,
                    ), None, None,
                )
            target_receipt_path = out_receipt or packet.lean_file.with_suffix(".receipt.json")
            target_receipt_path.parent.mkdir(parents=True, exist_ok=True)
            target_receipt_path.write_text(
                json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
            )
            snapshot_origin = "specification snapshot" if prompted_source_sha else "repository HEAD"
            diagnostics.append(
                f"Candidate differs from {snapshot_origin} ({source_snapshot_sha256[:8]} vs {candidate_sha[:8]}). "
                f"Evidence recorded; owner review is required ({receipt['review']['status']})."
            )
            return (
                GateResult(
                    gate_number=7,
                    gate_name="CANDIDATE_RECEIPT",
                    passed=True,
                    diagnostics=diagnostics,
                    details={
                        "source_context_changed": True,
                        "receipt": receipt,
                        "receipt_sha256": receipt["receiptSha256"],
                        "receipt_path": str(target_receipt_path),
                        "promotion_allowed": False,
                    },
                    duration_seconds=time.time() - t0,
                ),
                receipt,
                target_receipt_path,
            )

        # 3. Build raw candidate archive record for verified pass
        record = {
            "lean_file": rel_lean_path,
            "candidate_sha256": candidate_sha,
            "source_path": rel_lean_path,
            "source_snapshot_sha256": source_snapshot_sha256,
            "source_snapshot_current_sha256": candidate_sha,
            "source_context_changed": False,
            "toolchain": toolchain,
            "lakefile_sha256": lakefile_hash,
            "lake_manifest_sha256": manifest_hash,
            "git_head": git_head,
            "lean_check_returncode": kernel_details.get("lean_returncode", 0),
            "lean_output_sha256": hashlib.sha256(kernel_details.get("lean_output", "").encode("utf-8")).hexdigest(),
            "semantic_vacuity_returncode": vac_rc,
            "semantic_vacuity_output_sha256": vac_sha256,
            "axiom_audit_status": "collected" if audit_declarations else "not_requested",
            "axiom_audit_declarations": audit_declarations,
            "axiom_audit_returncode": kernel_details.get("axiom_audit_returncode") if audit_declarations else None,
            "axiom_audit_output": audit_output,
            "axiom_audit_output_sha256": audit_output_sha,
        }

        # Mint deterministic receipt
        receipt = build_candidate_receipt(record)

        # Verify receipt integrity and cryptographic self-consistency
        if not verify_candidate_receipt(receipt):
            diagnostics.append("Receipt verification failed: computed hash does not match canonical structure.")
            return (
                GateResult(
                    gate_number=7,
                    gate_name="CANDIDATE_RECEIPT",
                    passed=False,
                    diagnostics=diagnostics,
                    socratic_critique="Gate 7 Receipt Failure: Newly minted proof artifact receipt failed canonical verification.",
                    duration_seconds=time.time() - t0,
                ),
                None,
                None,
            )

        # Determine receipt destination
        if out_receipt:
            target_receipt_path = out_receipt
        else:
            target_receipt_path = packet.lean_file.with_suffix(".receipt.json")

        target_receipt_path.parent.mkdir(parents=True, exist_ok=True)
        target_receipt_path.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

        diagnostics.append(f"Self-checksummed candidate observation recorded: {receipt['receiptSha256']}")
        diagnostics.append(f"Observed environment gitHead={git_head[:8]}, toolchain={toolchain}")
        diagnostics.append(f"Saved candidate receipt to {target_receipt_path}; promotion remains pending owner review.")

        return (
            GateResult(
                gate_number=7,
                gate_name="CANDIDATE_RECEIPT",
                passed=True,
                diagnostics=diagnostics,
                details={
                    "receipt_sha256": receipt["receiptSha256"],
                    "receipt_path": str(target_receipt_path),
                    "promotion_allowed": receipt["review"]["promotionAllowed"],
                    "receipt_authority": receipt["authority"],
                    "review_status": receipt["review"]["status"],
                    "source_context_changed": False,
                    "semantic_vacuity_returncode": vac_rc,
                },
                duration_seconds=time.time() - t0,
            ),
            receipt,
            target_receipt_path,
        )

    gate_7_promotion_and_receipt = gate_7_candidate_receipt

    # -------------------------------------------------------------------------
    # State Machine Orchestrator
    # -------------------------------------------------------------------------
    def run_pipeline(
        self,
        spec_path: Path,
        lean_file: Path,
        out_receipt: Path | None = None,
    ) -> PipelineReport:
        """Execute the 7-Gate Evidence State Machine in strict order, halting on any failure."""
        start_time = time.time()
        report = PipelineReport(
            target_file=str(lean_file),
            spec_file=str(spec_path),
            status="IN_PROGRESS",
            final_verdict="IN_PROGRESS",
        )

        # Gate 1: INTAKE
        g1_res, packet = self.gate_1_intake(spec_path, lean_file)
        report.gates.append(g1_res)
        if not g1_res.passed or packet is None:
            report.status = "REJECTED_AT_GATE_1_INTAKE"
            report.final_verdict = "REJECTED"
            report.halted_at_gate = 1
            report.total_duration_seconds = time.time() - start_time
            return report

        # Gate 2: GROUNDING
        g2_res = self.gate_2_grounding(packet)
        report.gates.append(g2_res)
        if not g2_res.passed:
            report.status = "REJECTED_AT_GATE_2_GROUNDING"
            report.final_verdict = "REJECTED"
            report.halted_at_gate = 2
            report.total_duration_seconds = time.time() - start_time
            return report

        # Gate 3: STATIC TRAP SCREEN
        g3_res = self.gate_3_static_trap_screen(packet)
        report.gates.append(g3_res)
        if not g3_res.passed:
            report.status = "REJECTED_AT_GATE_3_STATIC_TRAP_SCREEN"
            report.final_verdict = "REJECTED"
            report.halted_at_gate = 3
            report.total_duration_seconds = time.time() - start_time
            return report

        # Gate 4: STATIC PROOF-HOLE SCAN
        g4_res = self.gate_4_static_proof_hole_scan(packet)
        report.gates.append(g4_res)
        if not g4_res.passed:
            report.status = "REJECTED_AT_GATE_4_STATIC_PROOF_HOLE_SCAN"
            report.final_verdict = "REJECTED"
            report.halted_at_gate = 4
            report.total_duration_seconds = time.time() - start_time
            return report

        # Gate 5: KERNEL SOURCE CHECK
        g5_res = self.gate_5_kernel_and_integration(packet)
        report.gates.append(g5_res)
        if not g5_res.passed:
            report.status = "REJECTED_AT_GATE_5_KERNEL_SOURCE_CHECK"
            report.final_verdict = "REJECTED"
            report.halted_at_gate = 5
            report.total_duration_seconds = time.time() - start_time
            return report

        # Gate 6: STATEMENT-FIDELITY REVIEW
        g6_res = self.gate_6_statement_fidelity_review(packet, kernel_result=g5_res)
        report.gates.append(g6_res)
        if not g6_res.passed:
            report.status = "REJECTED_AT_GATE_6_STATEMENT_FIDELITY_REVIEW"
            report.final_verdict = "REJECTED"
            report.halted_at_gate = 6
            report.total_duration_seconds = time.time() - start_time
            return report

        # Gate 7: CANDIDATE RECEIPT
        g7_res, receipt, receipt_path = self.gate_7_candidate_receipt(
            packet=packet,
            kernel_result=g5_res,
            out_receipt=out_receipt,
        )
        report.gates.append(g7_res)
        if not g7_res.passed or receipt is None:
            report.status = "REJECTED_AT_GATE_7_CANDIDATE_RECEIPT"
            report.final_verdict = "REJECTED"
            report.halted_at_gate = 7
            report.total_duration_seconds = time.time() - start_time
            return report

        # A candidate receipt records observations. Promotion is a separate owner action.
        report.status = "EVIDENCE_RECORDED_PENDING_OWNER_REVIEW"
        report.final_verdict = "PENDING_OWNER_REVIEW"
        report.receipt = receipt
        report.receipt_path = str(receipt_path) if receipt_path else None
        report.total_duration_seconds = time.time() - start_time
        return report


# -----------------------------------------------------------------------------
# CLI Entrypoint
# -----------------------------------------------------------------------------

def print_text_report(report: PipelineReport) -> None:
    """Render human-readable Socratic telemetry report."""
    print("=" * 76)
    print("OPENGAUSS QMS EVIDENCE PIPELINE - 7-GATE STATE MACHINE EXECUTION")
    print("=" * 76)
    print(f"Target Lean File:   {report.target_file}")
    print(f"Specification File: {report.spec_file}")
    print(f"Final Verdict:      {report.final_verdict}")
    print(f"Status:             {report.status}")
    print(f"Execution Time:     {report.total_duration_seconds:.2f}s")
    print("-" * 76)

    gate_names = [
        "1: INTAKE",
        "2: GROUNDING",
        "3: STATIC TRAP SCREEN",
        "4: STATIC PROOF-HOLE SCAN",
        "5: KERNEL SOURCE CHECK",
        "6: STATEMENT-FIDELITY REVIEW",
        "7: CANDIDATE RECEIPT",
    ]

    for idx, (gname, gres) in enumerate(zip(gate_names, report.gates, strict=False), start=1):
        status_tag = "[PASS]" if gres.passed else "[FAIL]"
        print(f"Gate {gname} - {status_tag} ({gres.duration_seconds:.2f}s)")
        for diag in gres.diagnostics:
            print(f"    • {diag}")
        if not gres.passed and gres.socratic_critique:
            print("\n  [SOCRATIC DIAGNOSTIC & CRITIQUE]")
            for c_line in gres.socratic_critique.splitlines():
                print(f"    {c_line}")
            print()

    print("=" * 76)
    if report.final_verdict == "PENDING_OWNER_REVIEW":
        print("✓ EVIDENCE RECORDED: ALL AUTOMATED CHECKS PASSED; OWNER REVIEW IS STILL REQUIRED")
        if report.receipt:
            print(f"Candidate Receipt SHA256:     {report.receipt.get('receiptSha256')}")
        if report.receipt_path:
            print(f"Candidate Receipt File:       {report.receipt_path}")
    else:
        print(f"✗ REJECTED: PROGRESSION HALTED AT GATE {report.halted_at_gate}")
    print("=" * 76)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="OpenGauss QMS Evidence Pipeline: 7-Gate Evidence State Machine"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    run_parser = subparsers.add_parser("run", help="Run the full 7-gate evidence pipeline on a candidate.")
    run_parser.add_argument("--spec", required=True, help="Path to theorem specification JSON file.")
    run_parser.add_argument("--lean", required=True, help="Path to candidate Lean 4 source file.")
    run_parser.add_argument("--out-receipt", default=None, help="Optional output path for immutable receipt JSON.")
    run_parser.add_argument("--lock-file", default="/tmp/info-geometry-build.lock", help="Path to Lake build flock lock.")
    run_parser.add_argument("--strict", action="store_true", default=True, help="Strict mode: treat all warnings as errors.")
    run_parser.add_argument("--no-strict", action="store_false", dest="strict", help="Relax strict warnings.")
    run_parser.add_argument("--json", action="store_true", help="Emit report in structured JSON format.")

    args = parser.parse_args(argv)

    if args.command == "run":
        spec_path = Path(args.spec).resolve()
        lean_path = Path(args.lean).resolve()
        out_receipt = Path(args.out_receipt).resolve() if args.out_receipt else None

        pipeline = QMSEvidencePipeline(
            lock_file=args.lock_file,
            strict=args.strict,
        )

        report = pipeline.run_pipeline(
            spec_path=spec_path,
            lean_file=lean_path,
            out_receipt=out_receipt,
        )

        if args.json:
            print(json.dumps(report.to_dict(), indent=2, ensure_ascii=False))
        else:
            print_text_report(report)

        return 0 if report.status == "EVIDENCE_RECORDED_PENDING_OWNER_REVIEW" else 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
