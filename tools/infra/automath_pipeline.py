#!/usr/bin/env python3
"""
AutoMath candidate pipeline: research, proposal, checking, audit, and archive.

The oracle proposes Lean candidates. Explicit SymPy witnesses provide
supporting evidence; Lean checks candidates; a static semantic-vacuity gate
screens proof shape; Arango stores append-only provenance. No stage
automatically edits owner source.

Uses:
  - Guarded ChatGPT Pro proposal/audit lane (cheap, no API tokens)
  - Optional hypothesis-linked SymPy witness scripts
  - Lean kernel under the shared build lock
  - Hive Memory ArangoDB (port 8540) for candidate provenance
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import urllib.request
import uuid
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Optional
from urllib.parse import quote

REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = REPO_ROOT / "lean"
TOOLS_INFRA = REPO_ROOT / "tools" / "infra"
SYMPY_VERIFY_DIR = REPO_ROOT / "tools" / "sympy"

# ArangoDB connections
INFOGEOMETRY_DB = "infogeometry"
HIVE_MEMORY_DB = "hive_memory"
ARANGO_ENDPOINT = os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530")
HIVE_ENDPOINT = os.environ.get("HIVE_ENDPOINT", "http://127.0.0.1:8540")

# Import the Pro polling bridge; sends are serialized by the shared lane guard.
if str(TOOLS_INFRA) not in sys.path:
    sys.path.insert(0, str(TOOLS_INFRA))

from lean_audit_prompt import extract_replacement_lean, lean_candidate_reject_reason
from chatgpt_lane_guard import browser_chatgpt_lane
from proof_artifact_receipt import build_candidate_receipt
from tools.infra.hive_epistemic_bridge import read_candidate_receipt
from tools.build_lock import acquire_build_lock

# Import oracle_dispatch if present
try:
    if str(REPO_ROOT / "tools" / "chatgpt-oracle") not in sys.path:
        sys.path.insert(0, str(REPO_ROOT / "tools" / "chatgpt-oracle"))
    from oracle_dispatch import dispatch_direct_record
except ImportError:
    dispatch_direct_record = None

def ask_ai(
    prompt: str,
    *,
    conversation_id: str | None = None,
    queue: bool = True,
    wait: bool = True,
) -> dict:
    del queue, wait  # The shared lane guard is mandatory for this transport.
    if dispatch_direct_record is None:
        raise RuntimeError("Tampermonkey oracle_dispatch is unavailable")

    # Project-attached Pro context is useful for generation, but this legacy
    # HTTP-polling bridge must share aiClaw's single-flight lane. Never fall
    # through to an uncoordinated browser-harness sender after a timeout.
    task_name = f"automath_{uuid.uuid4().hex}"
    print(f"  [FORMALIZE] Routing one proposal through the guarded Pro lane ({task_name})...")
    with browser_chatgpt_lane(
        source="automath_pipeline.oracle_proposal",
        prompt_chars=len(prompt),
        reason="tampermonkey_oracle_request",
    ):
        record = dispatch_direct_record(
            task_name=task_name,
            prompt_text=prompt,
            model="chatgpt-5.4-pro",
            conversation_id=conversation_id,
            project_url=os.environ.get("CHATGPT_PROJECT_URL", ""),
            tag="automath_candidate",
        )
        response = str(record.get("response") or "")
        if record.get("status") != "completed":
            raise RuntimeError(
                f"oracle task {task_name} ended with status={record.get('status')}; readback required"
            )
        if not response.strip():
            # The request may have reached the browser despite failed readback.
            raise RuntimeError(f"oracle returned no final response for {task_name}; readback required")
    return {
        "content": response,
        "task_id": task_name,
        "conversation_id": record.get("conversation_id", ""),
        "success": True,
    }


def candidate_path(hypothesis_id: str, code: str) -> Path:
    """Write a content-addressed candidate outside the Lean source tree."""
    normalized = code.rstrip() + "\n"
    digest = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
    safe_id = re.sub(r"[^A-Za-z0-9_.-]+", "_", hypothesis_id)
    directory = REPO_ROOT / "tmp" / "oracle_candidates" / "automath" / safe_id
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{digest}.lean"
    if path.exists():
        if path.read_text(encoding="utf-8") != normalized:
            raise RuntimeError(f"candidate hash collision at {path}")
    else:
        with path.open("x", encoding="utf-8") as handle:
            handle.write(normalized)
    return path


def reject_unproved_candidate(code: str) -> str:
    """Reject proof-debt and obvious vacuity before invoking Lean."""
    if re.search(r"(?<!\w)(sorry|admit|axiom)(?!\w)", code):
        return "proof_debt_marker"
    if re.search(r"(?<!\w)unsafe(?!\w)", code):
        return "unsafe_declaration"
    if re.search(r":\s*True\s*:=", code):
        return "vacuous_true_theorem"
    return lean_candidate_reject_reason(code)


@dataclass
class Hypothesis:
    """A single mathematical hypothesis (ore from Codex)."""
    id: str
    statement: str
    rationale: str
    mathematical_objects: list[str]
    source_apex: str
    metadata: dict = field(default_factory=dict)
    shape_hash: str = ""
    cas_passed: bool = False
    socratic_critique: str = ""
    lean_file: Optional[Path] = None
    lean_errors: str = ""
    repair_attempts: int = 0
    oracle_verdict: str = ""
    archived: bool = False


@dataclass
class GateResult:
    passed: bool
    errors: str = ""
    warnings: list[str] = field(default_factory=list)
    lean_returncode: int | None = None
    lean_output_sha256: str = ""
    semantic_vacuity_returncode: int | None = None
    semantic_vacuity_output_sha256: str = ""
    axiom_audit_status: str = "not_requested"
    axiom_audit_declarations: list[str] = field(default_factory=list)
    axiom_audit_returncode: int | None = None
    axiom_audit_output: str = ""
    axiom_audit_output_sha256: str = ""
    candidate_sha256: str = ""
    candidate_integrity_ok: bool = True


class LeanGate:
    """Lean kernel gate — the alchemical crucible."""

    def __init__(self, lean_root: Path = LEAN_ROOT):
        self.lean_root = lean_root

    def check(self, lean_file: Path) -> GateResult:
        """Check one candidate; module builds are scheduled by the locked BuildBee."""
        return self.check_file(lean_file)

    def check_file(
        self, lean_file: Path, *, axiom_audit_declarations: list[str] | None = None
    ) -> GateResult:
        """Kernel-check a candidate and optionally query Lean for named axiom dependencies."""
        declarations = axiom_audit_declarations or []
        if (not isinstance(declarations, list)
                or any(not isinstance(name, str) or not re.fullmatch(
                    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name
                ) for name in declarations)
                or len(set(declarations)) != len(declarations)):
            return GateResult(passed=False, errors="invalid or duplicate axiom audit declaration names")
        try:
            candidate_sha = hashlib.sha256(lean_file.read_bytes()).hexdigest()
            with acquire_build_lock(
                None, f"automath-lean-candidate:{os.getpid()}:{lean_file.name}", block=True
            ):
                result = subprocess.run(
                    ["lake", "env", "lean", str(lean_file)],
                    cwd=REPO_ROOT,
                    capture_output=True,
                    text=True,
                    timeout=120,
                    check=False,
                )
                axiom_result = None
                axiom_error = ""
                if result.returncode == 0 and declarations:
                    try:
                        axiom_result = self._run_axiom_audit(lean_file, declarations)
                    except Exception as exc:
                        axiom_error = str(exc)
            output = "\n".join(part for part in (result.stdout, result.stderr) if part)
            lean_hash = hashlib.sha256(output.encode("utf-8")).hexdigest()
            if result.returncode != 0:
                candidate_integrity_ok = (
                    hashlib.sha256(lean_file.read_bytes()).hexdigest() == candidate_sha
                )
                return GateResult(
                    passed=False, errors=output, lean_returncode=result.returncode,
                    lean_output_sha256=lean_hash, candidate_sha256=candidate_sha,
                    candidate_integrity_ok=candidate_integrity_ok,
                )
            qms = subprocess.run(
                [sys.executable, str(REPO_ROOT / "tools/quality/semantic_vacuity_gate.py"),
                 "--fail-on", "error", str(lean_file)],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=60,
                check=False,
            )
            qms_output = "\n".join(part for part in (qms.stdout, qms.stderr) if part)
            candidate_integrity_ok = (
                hashlib.sha256(lean_file.read_bytes()).hexdigest() == candidate_sha
            )
            combined = "\n".join(part for part in (output, qms_output) if part)
            axiom_output = ""
            axiom_status = "not_requested"
            if axiom_result is not None:
                axiom_output = "\n".join(
                    part for part in (axiom_result.stdout, axiom_result.stderr) if part
                )
                axiom_status = (
                    "collected"
                    if axiom_result.returncode == 0 and axiom_output.strip()
                    else "failed"
                )
            elif declarations:
                axiom_status = "failed"
                axiom_output = axiom_error or "axiom audit subprocess did not produce a result"
            warnings = []
            if not candidate_integrity_ok:
                warnings.append("candidate bytes changed during verification")
            return GateResult(
                passed=qms.returncode == 0 and candidate_integrity_ok, errors=combined,
                warnings=warnings,
                lean_returncode=result.returncode, lean_output_sha256=lean_hash,
                semantic_vacuity_returncode=qms.returncode,
                semantic_vacuity_output_sha256=hashlib.sha256(
                    qms_output.encode("utf-8")
                ).hexdigest(),
                axiom_audit_status=axiom_status,
                axiom_audit_declarations=list(declarations),
                axiom_audit_returncode=(axiom_result.returncode if axiom_result is not None else None),
                axiom_audit_output=axiom_output,
                axiom_audit_output_sha256=hashlib.sha256(
                    axiom_output.encode("utf-8")
                ).hexdigest() if axiom_result is not None or declarations else "",
                candidate_sha256=candidate_sha,
                candidate_integrity_ok=candidate_integrity_ok,
            )
        except subprocess.TimeoutExpired as exc:
            output = "\n".join(
                part for part in (exc.stdout or "", exc.stderr or "") if part
            )
            return GateResult(passed=False, errors=f"Lean check timeout (120s)\n{output}")
        except Exception as exc:
            return GateResult(passed=False, errors=str(exc))

    @staticmethod
    def _run_axiom_audit(lean_file: Path, declarations: list[str]) -> subprocess.CompletedProcess[str]:
        """Re-elaborate the candidate and run `#print axioms` for explicit names."""
        source = lean_file.read_text(encoding="utf-8")
        audit_source = "import Lean\n" + source.rstrip() + "\n\n" + "\n".join(
            f"#print axioms {name}" for name in declarations
        ) + "\n"
        with tempfile.TemporaryDirectory(prefix="automath-axiom-audit-") as temp_dir:
            audit_file = Path(temp_dir) / "CandidateAxiomAudit.lean"
            audit_file.write_text(audit_source, encoding="utf-8")
            return subprocess.run(
                ["lake", "env", "lean", str(audit_file)],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=120,
                check=False,
            )


class CASFilter:
    """Run only explicit, hypothesis-linked SymPy witness scripts."""

    def __init__(self, sympy_dir: Path = SYMPY_VERIFY_DIR):
        self.sympy_dir = sympy_dir

    def verify(self, hypothesis: Hypothesis) -> tuple[bool, str, list[dict[str, str]]]:
        """Run manifest-declared witnesses; unrelated scripts are no evidence."""
        witnesses = hypothesis.metadata.get("cas_witnesses", [])
        if not witnesses:
            return True, "not_supplied", []
        evidence: list[dict[str, str]] = []
        for entry in witnesses:
            relative = Path(str(entry))
            script = (REPO_ROOT / relative).resolve()
            try:
                script.relative_to(self.sympy_dir.resolve())
            except ValueError:
                return False, "witness_outside_sympy_directory", evidence
            if not script.is_file() or script.suffix != ".py":
                return False, f"witness_missing:{relative}", evidence
            try:
                result = subprocess.run(
                    [sys.executable, str(script)],
                    cwd=REPO_ROOT,
                    capture_output=True,
                    text=True,
                    timeout=60,
                )
                if result.returncode != 0:
                    print(f"  [CAS] FAIL: {relative} -> {result.stderr[:200]}")
                    return False, "failed", evidence
                evidence.append({
                    "path": relative.as_posix(),
                    "sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
                })
            except subprocess.TimeoutExpired:
                print(f"  [CAS] TIMEOUT: {relative}")
                return False, "timeout", evidence
            except Exception as e:
                print(f"  [CAS] ERROR: {relative} -> {e}")
                return False, f"error:{e}", evidence
        return True, "passed", evidence


class SocraticVerifier:
    """Socratic proposal critic through the shared guarded Pro lane."""

    def __init__(self):
        self.clawbot = TOOLS_INFRA / "socratic_clawbot.py"

    def critique(self, hypothesis: Hypothesis) -> str:
        """Audit a checked candidate; this output is never treated as proof."""
        try:
            prompt = self._build_critique_prompt(hypothesis)
            response = ask_ai(
                prompt=prompt,
                conversation_id=hypothesis.metadata.get("oracle_conversation_id"),
            )
            hypothesis.metadata.setdefault("oracle_exchanges", []).append({
                "role": "post_lean_critic",
                "task_id": response["task_id"],
                "conversation_id": response.get("conversation_id", ""),
                "prompt_sha256": hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
                "response_sha256": hashlib.sha256(
                    str(response.get("content", "")).encode("utf-8")
                ).hexdigest(),
            })
            return str(response.get("content") or "")
        except Exception as e:
            return f"Socratic critique error: {e}"

    def _build_critique_prompt(self, hypothesis: Hypothesis) -> str:
        candidate = hypothesis.lean_file.read_text(encoding="utf-8") if hypothesis.lean_file else ""
        owner_path, owner_context = AutomathPipeline._owner_context(hypothesis.source_apex)
        return f"""Socratic critique of mathematical hypothesis:

HYPOTHESIS: {hypothesis.statement}
RATIONALE: {hypothesis.rationale}
OBJECTS: {', '.join(hypothesis.mathematical_objects)}
SOURCE APEX: {hypothesis.source_apex}
OWNER MODULE: {owner_path or 'unresolved'}
OWNER CONTEXT:
```lean4
{owner_context or '[unresolved; do not claim repository declarations not shown below]'}
```
LEAN CANDIDATE:
```lean4
{candidate}
```
LEAN AND SEMANTIC-VACUITY DIAGNOSTICS:
{hypothesis.lean_errors or '[Lean and semantic-vacuity gates passed; inspect theorem scope and assumptions.]'}

Provide a structured critique:
1. Mathematical soundness (true/false/uncertain)
2. Missing assumptions
3. Potential counterexamples
4. Suggested formalization approach in Lean 4
5. Separate mathematical observations from claims requiring repository search
"""


class HiveSync:
    """Archive candidate provenance; this class does not promote Lean source."""

    def __init__(self):
        self.infogeo_endpoint = ARANGO_ENDPOINT
        self.hive_endpoint = HIVE_ENDPOINT

    def archive_candidate(self, hypothesis: Hypothesis) -> bool:
        """Append a candidate observation; this does not promote a theorem."""
        print(f"HIVE CANDIDATE ARCHIVE: {hypothesis.id} -> {hypothesis.lean_file}")
        print(f"  Statement: {hypothesis.statement[:100]}...")

        # 1. Commit to ArangoDB (hive_memory.Thoughts)
        endpoint = self.hive_endpoint
        db = "hive_memory"
        username = os.environ.get("ARANGO_USER", "root")
        password = os.environ.get("ARANGO_PASSWORD", "hive_brain")

        # Prepare the document payload
        doc = {
            "_key": uuid.uuid4().hex,
            "id": hypothesis.id,
            "run_id": hypothesis.metadata.get("run_id", hypothesis.id),
            "record_type": "automath_lean_candidate",
            "authority": "candidate_record_not_proof_authority",
            "status": "lean_checked_pending_review",
            "statement": hypothesis.statement,
            "rationale": hypothesis.rationale,
            "mathematical_objects": hypothesis.mathematical_objects,
            "source_apex": hypothesis.source_apex,
            "cas_passed": hypothesis.cas_passed,
            "cas_status": hypothesis.metadata.get("cas_status", "not_supplied"),
            "cas_witness_evidence": hypothesis.metadata.get("cas_witness_evidence", []),
            "socratic_critique": hypothesis.socratic_critique,
            "oracle_verdict": hypothesis.oracle_verdict,
            "oracle_exchanges": hypothesis.metadata.get("oracle_exchanges", []),
            "lean_file": str(hypothesis.lean_file) if hypothesis.lean_file else "",
            "candidate_sha256": (
                hashlib.sha256(hypothesis.lean_file.read_bytes()).hexdigest()
                if hypothesis.lean_file and hypothesis.lean_file.is_file()
                else ""
            ),
            "source_snapshot_sha256": hypothesis.metadata.get("source_snapshot_sha256", ""),
            "source_path": hypothesis.metadata.get("source_path", ""),
            "toolchain": hypothesis.metadata.get("toolchain", ""),
            "lakefile_sha256": hypothesis.metadata.get("lakefile_sha256", ""),
            "lake_manifest_sha256": hypothesis.metadata.get("lake_manifest_sha256", ""),
            "git_head": hypothesis.metadata.get("git_head", ""),
            "lean_check_returncode": hypothesis.metadata.get("lean_check_returncode"),
            "lean_output_sha256": hypothesis.metadata.get("lean_output_sha256", ""),
            "semantic_vacuity_returncode": hypothesis.metadata.get("semantic_vacuity_returncode"),
            "semantic_vacuity_output_sha256": hypothesis.metadata.get("semantic_vacuity_output_sha256", ""),
            "semantic_vacuity_status": hypothesis.metadata.get("semantic_vacuity_status", "not_run"),
            "axiom_audit_status": hypothesis.metadata.get("axiom_audit_status", "not_requested"),
            "axiom_audit_declarations": hypothesis.metadata.get("axiom_audit_declarations", []),
            "axiom_audit_returncode": hypothesis.metadata.get("axiom_audit_returncode"),
            "axiom_audit_output": hypothesis.metadata.get("axiom_audit_output", ""),
            "axiom_audit_output_sha256": hypothesis.metadata.get("axiom_audit_output_sha256", ""),
            "axiom_audit_status": hypothesis.metadata.get("axiom_audit_status", "not_requested"),
            "axiom_audit_declarations": hypothesis.metadata.get("axiom_audit_declarations", []),
            "axiom_audit_output": hypothesis.metadata.get("axiom_audit_output", ""),
            "axiom_audit_output_sha256": hypothesis.metadata.get("axiom_audit_output_sha256", ""),
            "lean_errors": hypothesis.lean_errors,
            "repair_attempts": hypothesis.repair_attempts,
            "source_snapshot_current_sha256": hypothesis.metadata.get("source_snapshot_current_sha256", ""),
            "source_context_changed": hypothesis.metadata.get("source_context_changed", False),
            "audit_defect": hypothesis.metadata.get("audit_defect"),
            "audit_policy_version": hypothesis.metadata.get("audit_policy_version"),
            "status": hypothesis.metadata.get("archive_status", "lean_checked_pending_review"),
            "timestamp": datetime.utcnow().isoformat() + "Z"
        }
        archived_candidate_sha = doc["candidate_sha256"]
        if archived_candidate_sha != hypothesis.metadata.get("candidate_sha256", ""):
            print("  [HIVE] Candidate changed after Lean checking; refusing to archive")
            return False
        doc["audit_receipt"] = build_candidate_receipt(doc)
        validated_receipt = read_candidate_receipt(doc)
        if validated_receipt is None:
            print("  [HIVE] Candidate receipt failed integrity/binding validation; not archived")
            return False
        doc["audit_receipt"] = validated_receipt
        hypothesis.metadata["audit_receipt"] = doc["audit_receipt"]

        # POST with a fresh UUID key preserves append-only observation history.
        def auth_header(u: str, p: str) -> str:
            token = base64.b64encode(f"{u}:{p}".encode("utf-8")).decode("ascii")
            return f"Basic {token}"

        def db_url(ep: str, d: str, path: str) -> str:
            return f"{ep.rstrip('/')}/_db/{quote(d)}/{path.lstrip('/')}"

        headers = {
            "Authorization": auth_header(username, password),
            "Accept": "application/json",
            "Content-Type": "application/json"
        }

        committed_db = False
        local_fallback = False
        try:
            url = db_url(endpoint, db, "/_api/document/Thoughts")
            req = urllib.request.Request(url, data=json.dumps(doc).encode("utf-8"), headers=headers, method="POST")
            with urllib.request.urlopen(req) as resp:
                result = json.loads(resp.read().decode("utf-8"))
                print(f"  [HIVE] Successfully committed to ArangoDB Thoughts collection (key={result.get('_key')})")
                committed_db = True
        except Exception as e:
            print(f"  [HIVE] Failed to commit to ArangoDB: {e}")

        # Fallback log in case ArangoDB is unreachable
        if not committed_db:
            try:
                gold_log = Path("/tmp/automath_candidate_log.jsonl")
                with gold_log.open("a", encoding="utf-8") as f:
                    f.write(json.dumps(doc) + "\n")
                local_fallback = True
                print("  [HIVE] Saved fallback entry to /tmp/automath_candidate_log.jsonl")
            except Exception as fe:
                print(f"  [HIVE] Fallback logging failed: {fe}")

        return committed_db or local_fallback

    def broadcast_to_bees(self, hypothesis: Hypothesis):
        """Announce candidate availability; consumers must recheck provenance."""
        print(f"CANDIDATE AVAILABLE: {hypothesis.id}")


class AutomathPipeline:
    """Main pipeline orchestrator."""

    def __init__(self, apex: str, max_repairs: int = 3):
        self.apex = apex
        self.max_repairs = max_repairs
        self.lean_gate = LeanGate()
        self.cas_filter = CASFilter()
        self.socratic = SocraticVerifier()
        self.hive = HiveSync()
        self.candidate_count = 0

    def run(self, hypotheses: list[Hypothesis]) -> list[Hypothesis]:
        """Run the full pipeline on a list of hypotheses."""
        candidates = []
        for h in hypotheses:
            print(f"\n{'='*60}")
            print(f"PROCESSING: {h.id}")
            print(f"  Statement: {h.statement[:100]}...")

            # Stage 1: CAS Filter (cheap)
            print("  [CAS] Running symbolic verification...")
            cas_ok, cas_status, cas_evidence = self.cas_filter.verify(h)
            h.metadata["cas_status"] = cas_status
            h.metadata["cas_witness_evidence"] = cas_evidence
            h.cas_passed = cas_status == "passed"
            if not cas_ok:
                print("  [CAS] FAILED — discarding")
                continue
            print(f"  [CAS] {cas_status.upper()}")

            # Stage 2: Generate a proof-carrying proposal.
            h.lean_file = self._formalize(h)
            if not h.lean_file:
                print("  [FORMALIZE] Failed to generate Lean file")
                continue

            print("  [LEAN GATE] Checking...")
            gate = self.lean_gate.check_file(
                h.lean_file,
                axiom_audit_declarations=h.metadata.get("axiom_audit_declarations"),
            )
            if not gate.passed:
                if not gate.candidate_integrity_ok:
                    print("  [LEAN GATE] Candidate changed during checking; discarding")
                    continue
                print(f"  [LEAN GATE] FAILED — attempting repair (max {self.max_repairs})")
                h.lean_errors = gate.errors
                repaired_gate = self._repair_loop(h)
                if repaired_gate is None:
                    print("  [REPAIR] Exhausted — discarding")
                    continue
                gate = repaired_gate
            else:
                print("  [LEAN GATE] PASSED on first try!")

            self._record_gate_result(h, gate)
            print("  [SOCRATIC] Auditing the checked candidate...")
            h.socratic_critique = self.socratic.critique(h)
            h.oracle_verdict = "advisory_only"

            # Stage 5: Archive evidence only. Owner-source promotion is a
            # separate reviewed action and is intentionally not automated here.
            print("  [HIVE] Archiving kernel-checked candidate evidence...")
            current_source_sha = self._source_snapshot_hash(h.source_apex)
            prompted_source_sha = h.metadata.get("source_snapshot_sha256", "")
            h.metadata["source_snapshot_current_sha256"] = current_source_sha
            h.metadata["source_context_changed"] = bool(
                prompted_source_sha and prompted_source_sha != current_source_sha
            )
            h.metadata["source_snapshot_sha256"] = prompted_source_sha or current_source_sha
            h.metadata["archive_status"] = (
                "source_context_changed_pending_review"
                if h.metadata["source_context_changed"]
                else "lean_checked_pending_review"
            )
            h.metadata["toolchain"] = (REPO_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
            h.metadata["lakefile_sha256"] = hashlib.sha256(
                (REPO_ROOT / "lakefile.lean").read_bytes()
            ).hexdigest()
            h.metadata["lake_manifest_sha256"] = hashlib.sha256(
                (REPO_ROOT / "lake-manifest.json").read_bytes()
            ).hexdigest()
            head = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT,
                capture_output=True, text=True, check=False,
            )
            h.metadata["git_head"] = head.stdout.strip() if head.returncode == 0 else "unavailable"
            h.archived = self.hive.archive_candidate(h)
            self.hive.broadcast_to_bees(h)
            self.candidate_count += 1
            candidates.append(h)
            print(f"  ✅ CANDIDATE #{self.candidate_count}: {h.id}")

        print(f"\n{'='*60}")
        print(
            f"PIPELINE COMPLETE: {self.candidate_count} kernel-checked candidates "
            f"from {len(hypotheses)} hypotheses; no owner source was promoted"
        )
        return candidates

    @staticmethod
    def _record_gate_result(hypothesis: Hypothesis, gate: GateResult) -> None:
        hypothesis.metadata["lean_check_returncode"] = gate.lean_returncode
        hypothesis.metadata["candidate_sha256"] = gate.candidate_sha256
        hypothesis.metadata["lean_output_sha256"] = gate.lean_output_sha256
        hypothesis.metadata["semantic_vacuity_returncode"] = gate.semantic_vacuity_returncode
        hypothesis.metadata["semantic_vacuity_output_sha256"] = gate.semantic_vacuity_output_sha256
        hypothesis.metadata["semantic_vacuity_status"] = (
            "passed" if gate.semantic_vacuity_returncode == 0 else "failed"
        ) if gate.semantic_vacuity_returncode is not None else "not_run"
        hypothesis.metadata["axiom_audit_status"] = gate.axiom_audit_status
        hypothesis.metadata["axiom_audit_declarations"] = list(gate.axiom_audit_declarations)
        hypothesis.metadata["axiom_audit_returncode"] = gate.axiom_audit_returncode
        hypothesis.metadata["axiom_audit_output"] = gate.axiom_audit_output
        hypothesis.metadata["axiom_audit_output_sha256"] = gate.axiom_audit_output_sha256
        hypothesis.metadata["axiom_audit_status"] = gate.axiom_audit_status
        hypothesis.metadata["axiom_audit_declarations"] = list(gate.axiom_audit_declarations)
        hypothesis.metadata["axiom_audit_output"] = gate.axiom_audit_output
        hypothesis.metadata["axiom_audit_output_sha256"] = gate.axiom_audit_output_sha256

    @staticmethod
    def _owner_module(source_apex: str) -> Path | None:
        """Resolve the longest module prefix of a qualified owner declaration."""
        parts = source_apex.split(".")
        for end in range(len(parts) - 1, 0, -1):
            owner = (LEAN_ROOT / Path(*parts[:end])).with_suffix(".lean")
            if owner.is_file():
                return owner
        return None

    @classmethod
    def _owner_context(cls, source_apex: str) -> tuple[str, str]:
        """Return bounded source evidence, never inferred declarations."""
        owner_path, context, _ = cls._owner_context_snapshot(source_apex)
        return owner_path, context

    @classmethod
    def _owner_context_snapshot(cls, source_apex: str) -> tuple[str, str, str]:
        """Build prompt context and hash from the same read of the owner bytes."""
        owner = cls._owner_module(source_apex)
        if owner is None:
            return "", "", ""
        raw = owner.read_bytes()
        text = raw.decode("utf-8")
        digest = hashlib.sha256(raw).hexdigest()
        if len(text) <= 30000:
            return str(owner.relative_to(REPO_ROOT)), text, digest
        name = source_apex.split(".")[-1]
        lines = text.splitlines()
        match_index = next(
            (i for i, line in enumerate(lines)
             if re.search(rf"\b(?:def|abbrev|theorem|lemma|structure|class|inductive)\s+{re.escape(name)}\b", line)),
            None,
        )
        if match_index is None:
            return str(owner.relative_to(REPO_ROOT)), "", digest
        imports = [line for line in lines[:match_index] if line.startswith(("import ", "open ", "namespace ", "variable ", "universe "))]
        excerpt = lines[max(0, match_index - 60):match_index + 100]
        return str(owner.relative_to(REPO_ROOT)), "\n".join(imports + ["-- Target context excerpt:"] + excerpt), digest

    @classmethod
    def _source_snapshot_hash(cls, source_apex: str) -> str:
        """Hash the likely owner module; unresolved names remain unlinked."""
        owner = cls._owner_module(source_apex)
        return hashlib.sha256(owner.read_bytes()).hexdigest() if owner else ""

    def _formalize(self, hypothesis: Hypothesis) -> Optional[Path]:
        """Generate an immutable Lean candidate; never write owner source."""
        owner_path, owner_context, source_digest = self._owner_context_snapshot(hypothesis.source_apex)
        if owner_context:
            hypothesis.metadata["source_path"] = owner_path
            hypothesis.metadata["source_snapshot_sha256"] = source_digest
        prompt = f"""You are Antigravity, a formalization assistant for Lean 4.
Given the following mathematical hypothesis:

STATEMENT: {hypothesis.statement}
RATIONALE: {hypothesis.rationale}
OBJECTS: {', '.join(hypothesis.mathematical_objects)}
SOURCE APEX: {hypothesis.source_apex}
OWNER MODULE: {owner_path or 'unresolved'}
OWNER CONTEXT (source evidence; declarations outside this context are unavailable):
```lean4
{owner_context or '[No owner module resolved. Return NO_CANDIDATE rather than guessing declarations.]'}
```

Translate this mathematical hypothesis and its objects into a formal Lean 4 theorem.
Your translation should:
1. Reuse only declarations actually present in the supplied owner context.
2. State only the requested result, with mathematically necessary explicit hypotheses.
3. Provide a complete Lean 4 candidate with a kernel proof; do not use `sorry`, `admit`, `axiom`, `unsafe`, or a theorem concluding `True`.
4. Treat the apex label as untrusted. If its owner or required declarations are absent from the supplied context, return `NO_CANDIDATE` rather than guessing or inventing them.
5. Provide the complete Lean source inside one fenced `lean4` block.
"""
        print(f"  [FORMALIZE] Asking AI to formalize '{hypothesis.id}'...")
        hypothesis.metadata["run_id"] = hypothesis.metadata.get("run_id", uuid.uuid4().hex)
        try:
            res = ask_ai(prompt=prompt, conversation_id="", queue=True, wait=True)
            hypothesis.metadata["oracle_conversation_id"] = res.get("conversation_id", "")
            hypothesis.metadata.setdefault("oracle_exchanges", []).append({
                "role": "formalizer",
                "task_id": res["task_id"],
                "conversation_id": res.get("conversation_id", ""),
                "prompt_sha256": hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
                "response_sha256": hashlib.sha256(
                    str(res.get("content", "")).encode("utf-8")
                ).hexdigest(),
            })
            content = res.get("content") or ""
            lean_content = extract_replacement_lean(content)
        except Exception as e:
            print(f"  [FORMALIZE] ask_ai failed; no candidate produced: {e}")
            return None

        if "NO_CANDIDATE" in (res.get("content") or ""):
            print("  [FORMALIZE] Oracle reported NO_CANDIDATE")
            return None
        rejection = reject_unproved_candidate(lean_content)
        if rejection:
            print(f"  [FORMALIZE] Candidate rejected before Lean check: {rejection}")
            return None

        lean_file = candidate_path(hypothesis.id, lean_content)
        hypothesis.metadata["candidate_sha256"] = hashlib.sha256(lean_file.read_bytes()).hexdigest()
        return lean_file

    def _repair_loop(self, hypothesis: Hypothesis) -> GateResult | None:
        """Attempt to repair Lean errors via Socratic repair loop."""
        for attempt in range(1, self.max_repairs + 1):
            hypothesis.repair_attempts = attempt
            print(f"  [REPAIR] Attempt {attempt}/{self.max_repairs}")

            if not hypothesis.lean_file or not hypothesis.lean_file.exists():
                return None

            file_content = hypothesis.lean_file.read_text(encoding="utf-8")

            repair_prompt = f"""You are Antigravity, a Lean 4 proof repair assistant.
The following Lean 4 file has compilation errors.

FILE PATH: {hypothesis.lean_file}
FILE CONTENT:
{file_content}

ERRORS:
{hypothesis.lean_errors}

Please provide the COMPLETE, corrected Lean 4 code for this file.
Your output must:
1. Fix all the listed compilation errors.
2. Maintain the same namespace, imports, and theorem name.
3. Do not add `sorry`, `admit`, `axiom`, `unsafe`, or weaken the theorem to `True`.
4. If it cannot be repaired honestly, return `NO_CANDIDATE`.
5. Output the complete Lean 4 code inside a single `lean4` fence.
"""
            print(f"  [REPAIR] Querying Socratic Verifier for correction...")
            try:
                res = ask_ai(
                    prompt=repair_prompt,
                    conversation_id=hypothesis.metadata.get("oracle_conversation_id"),
                    queue=True,
                    wait=True,
                )
                hypothesis.metadata.setdefault("oracle_exchanges", []).append({
                    "role": "lean_repair",
                    "task_id": res["task_id"],
                    "conversation_id": res.get("conversation_id", ""),
                    "prompt_sha256": hashlib.sha256(repair_prompt.encode("utf-8")).hexdigest(),
                    "response_sha256": hashlib.sha256(
                        str(res.get("content", "")).encode("utf-8")
                    ).hexdigest(),
                })
                content = res.get("content") or ""
                corrected_code = extract_replacement_lean(content)

                if "NO_CANDIDATE" in (res.get("content") or ""):
                    print("  [REPAIR] Oracle reported NO_CANDIDATE")
                    return None
                rejection = reject_unproved_candidate(corrected_code)
                if not rejection:
                    hypothesis.lean_file = candidate_path(hypothesis.id, corrected_code)
                    hypothesis.metadata["candidate_sha256"] = hashlib.sha256(
                        hypothesis.lean_file.read_bytes()
                    ).hexdigest()
                    print(f"  [REPAIR] Wrote immutable candidate {hypothesis.lean_file}")
                else:
                    print(f"  [REPAIR] Candidate rejected: {rejection}")
                    continue
            except Exception as e:
                print(f"  [REPAIR] Socratic query failed: {e}")
                continue

            # Recheck the file
            gate = self.lean_gate.check_file(
                hypothesis.lean_file,
                axiom_audit_declarations=hypothesis.metadata.get("axiom_audit_declarations"),
            )
            if gate.passed:
                hypothesis.lean_errors = ""
                print("  [REPAIR] SUCCESS - file compiled successfully!")
                return gate

            if not gate.candidate_integrity_ok:
                print("  [REPAIR] Candidate changed during checking; abandoning this repair chain")
                return None

            hypothesis.lean_errors = gate.errors
            print(f"  [REPAIR] Still failing: {gate.errors[:200]}...")

        return None

def extract_objects_from_text(text: str) -> list[str]:
    """Extract mathematical objects from text using keyword matching."""
    keywords = [
        "spectrum", "C*-algebra", "functional-calculus", "fibonacci", "K-theory", 
        "presheaf", "sheaf", "causal-site", "alexandrov-topology", "Zorn", 
        "Clifford", "Freudenthal", "octonion", "Gell-Mann", "SU(3)", "Cuntz", 
        "Hilbert", "Bost-Connes", "Jordan", "algebra", "Lie", "topology"
    ]
    extracted = []
    text_lower = text.lower()
    for kw in keywords:
        if re.search(rf"\b{re.escape(kw.lower())}\b", text_lower):
            extracted.append(kw)
    if not extracted:
        extracted = ["algebra", "spectrum"]
    return extracted


def load_hypotheses_from_oracle_result(result_file: Path) -> list[Hypothesis]:
    """Parse the oracle result (free-form text with numbered sections) into Hypothesis objects."""
    if not result_file.exists():
        return []
    content = result_file.read_text()
    hypotheses = []

    # Match sections starting with numbers followed by dot at start of line
    sections = re.split(r'(?:^|\n)\d+\.\s+', content)
    for i, section in enumerate(sections):
        section = section.strip()
        if not section:
            continue
        lines = section.split('\n')
        title = lines[0].strip()
        rationale = '\n'.join(lines[1:5]).strip()
        
        objects = extract_objects_from_text(title + "\n" + rationale)

        h = Hypothesis(
            id=f"auto_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{i}",
            statement=title,
            rationale=rationale,
            mathematical_objects=objects,
            source_apex="InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz",
        )
        hypotheses.append(h)

    return hypotheses


def main():
    parser = argparse.ArgumentParser(description="Automath Pipeline — Hybrid Omega + Hive")
    parser.add_argument("--apex", default="InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz",
                        help="Apex declaration to seed from")
    parser.add_argument("--result-file", default="/tmp/chatgpt_browser_result.json",
                        help="Oracle result JSON file")
    parser.add_argument("--max-repairs", type=int, default=3,
                        help="Max repair attempts per hypothesis")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be done without executing")
    args = parser.parse_args()

    hypotheses = load_hypotheses_from_oracle_result(Path(args.result_file))
    print(f"Loaded {len(hypotheses)} hypotheses from {args.result_file}")

    if args.dry_run:
        for h in hypotheses:
            print(f"  {h.id}: {h.statement[:80]}...")
            print(f"    Objects: {h.mathematical_objects}")
        return

    pipeline = AutomathPipeline(apex=args.apex, max_repairs=args.max_repairs)
    candidates = pipeline.run(hypotheses)

    print(f"\nFinal candidate count: {len(candidates)} (owner source promotion remains manual)")


if __name__ == "__main__":
    main()
