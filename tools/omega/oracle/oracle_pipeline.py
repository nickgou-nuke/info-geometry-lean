#!/usr/bin/env python3
"""
Omega Oracle Pipeline — stages F→A→B→C→D
Ported from the-omega-institute/automath/tools/chatgpt-oracle/oracle_pipeline.py
Adapted for info-geometry-lean with aiClaw lane + ArangoDB causal cones.
"""

import json
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import Literal, Optional

STATE_DIR = Path("tools/omega/state")
STATE_DIR.mkdir(parents=True, exist_ok=True)

PipelineStage = Literal["F", "A", "B", "C", "D", "DONE"]

@dataclass
class PipelineState:
    run_id: str
    stage: PipelineStage
    concept_id: str
    formal_intent_envelope: dict
    derivation_log: list
    audit_report: Optional[dict] = None
    acceptance_record: Optional[dict] = None
    created_at: str = ""
    updated_at: str = ""

    def __post_init__(self):
        if not self.created_at:
            self.created_at = datetime.utcnow().isoformat() + "Z"
        self.updated_at = datetime.utcnow().isoformat() + "Z"

    def path(self) -> Path:
        return STATE_DIR / f"pipeline_{self.run_id}.json"

    def save(self):
        self.path().write_text(json.dumps(asdict(self), indent=2))

    @staticmethod
    def load(run_id: str) -> "PipelineState":
        p = STATE_DIR / f"pipeline_{run_id}.json"
        return PipelineState(**json.loads(p.read_text()))


# ─── Stage F: Formal Intent Capture ───
def stage_F(intent_path: Path) -> dict:
    """Read and validate the formal intent envelope."""
    envelope = json.loads(intent_path.read_text())
    required = ["concept_id", "intake_classification", "mathematical_domain", 
                "target_status", "risk_level", "formal_objects", "acceptance_theorems"]
    for k in required:
        if k not in envelope:
            raise ValueError(f"Missing required field in intent envelope: {k}")
    return envelope


# ─── Stage A: Automated Derivation (autoresearch loop) ───
def stage_A(envelope: dict, run_id: str) -> list:
    """
    Run the derivation engine:
    1. Query ArangoDB for existing owner surfaces (causal cone)
    2. Generate candidate Lean declarations
    3. Attempt proofs via lake build + socratic_clawbot
    4. Log all attempts
    """
    derivation_log = []
    
    # 1. Causal cone expansion from relevant seeds
    seeds = _extract_seeds(envelope)
    for seed in seeds:
        cone = _causal_cone(seed, backward=3, forward=3)
        derivation_log.append({"step": "cone", "seed": seed, "nodes": len(cone)})
    
    # 2. Generate candidate declarations (skeleton)
    candidates = _generate_skeletons(envelope, cone)
    derivation_log.append({"step": "skeletons", "count": len(candidates)})
    
    # 3. Attempt proofs via socratic_clawbot (oracle)
    for cand in candidates:
        result = _prove_with_oracle(cand)
        derivation_log.append({"step": "prove", "candidate": cand["name"], "result": result})
    
    return derivation_log


def _extract_seeds(envelope: dict) -> list[str]:
    """Map formal_objects to existing ArangoDB declarations."""
    seeds = []
    for obj in envelope.get("formal_objects", []):
        query = f'FOR d IN decls FILTER d.name LIKE "%{obj}%" RETURN d.name'
        try:
            result = subprocess.run(
                ["python3", "tools/infra/arango_causal_memory.py", "query", query],
                capture_output=True, text=True, timeout=30,
                cwd="/home/goutev/repos/info-geometry-lean"
            )
            if result.returncode == 0:
                data = json.loads(result.stdout)
                for row in data.get("output", {}).get("result", []):
                    seeds.append(row.get("name", ""))
        except Exception:
            pass
    return seeds or [
        "InfoGeometry.Algebra.SpecialUnitary.su",
        "InfoGeometry.Algebra.GellMannBasis",
        "InfoGeometry.Physics.GellMannSU3",
        "InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz"
    ]


def _causal_cone(seed: str, backward: int, forward: int) -> list[dict]:
    """Query ArangoDB for causal cone around seed."""
    cmd = [
        "python3", "tools/infra/arango_causal_chiral_cone_prompt.py",
        "--decl", seed,
        "--backward-depth", str(backward),
        "--forward-depth", str(forward),
        "--json-out", f"/tmp/cone_{seed.replace('.', '_')}.json"
    ]
    subprocess.run(cmd, capture_output=True, cwd="/home/goutev/repos/info-geometry-lean")
    try:
        with open(f"/tmp/cone_{seed.replace('.', '_')}.json") as f:
            return json.load(f).get("cone", [])
    except Exception:
        return []


def _generate_skeletons(envelope: dict, cones: list) -> list[dict]:
    """Generate Lean skeleton declarations from intent + cone context."""
    skeletons = []
    for obj in envelope.get("formal_objects", []):
        skeletons.append({
            "name": obj,
            "type": "def" if "Basis" in obj or "Constants" in obj else "theorem",
            "statement": f"-- TODO: formalize {obj} from {envelope['concept_id']}",
            "imports": envelope.get("allowed_imports", [])
        })
    return skeletons


def _prove_with_oracle(candidate: dict) -> dict:
    """Invoke socratic_clawbot (aiClaw) for proof attempt."""
    # Find the Lean file for this candidate
    file_path = _find_lean_file(candidate["name"])
    if not file_path:
        return {"status": "failed", "error": "Lean file not found"}
    
    # Extract the theorem/def name
    theorem_name = candidate["name"].split(".")[-1]
    
    try:
        result = subprocess.run(
            ["python3", "tools/infra/socratic_clawbot.py", 
             "--file", file_path,
             "--theorem", theorem_name,
             "--dry-run", "--json"],
            capture_output=True, text=True, timeout=120,
            cwd="/home/goutev/repos/info-geometry-lean"
        )
        if result.returncode == 0:
            try:
                return json.loads(result.stdout)
            except:
                return {"status": "failed", "error": "Invalid JSON from clawbot"}
        return {"status": "failed", "error": result.stderr or result.stdout}
    except Exception as e:
        return {"status": "failed", "error": str(e)}


def _find_lean_file(decl_name: str) -> Optional[str]:
    """Find the Lean file containing a declaration."""
    # Map common prefixes to file paths
    if decl_name.startswith("InfoGeometry.Algebra.SpecialUnitary"):
        return "lean/InfoGeometry/Algebra/SpecialUnitary.lean"
    elif decl_name.startswith("InfoGeometry.Algebra.GellMannBasis"):
        return "lean/InfoGeometry/Algebra/GellMannBasis.lean"
    elif decl_name.startswith("InfoGeometry.Algebra.StructureConstants"):
        return "lean/InfoGeometry/Algebra/StructureConstants.lean"
    elif decl_name.startswith("InfoGeometry.Algebra.GellMannBridge"):
        return "lean/InfoGeometry/Algebra/GellMannBridge.lean"
    elif decl_name.startswith("InfoGeometry.Physics.GellMannSU3"):
        return "lean/InfoGeometry/Physics/GellMannSU3.lean"
    elif decl_name.startswith("InfoGeometry.Algebra.CuntzFibonacciBraidInclusion"):
        return "lean/InfoGeometry/Algebra/CuntzFibonacciBraidInclusion.lean"
    # Search for it
    for f in Path("lean").rglob("*.lean"):
        try:
            if decl_name in f.read_text():
                return str(f)
        except:
            pass
    return None


# ─── Stage B: Independent Audit (A-A role) ───
def stage_B(derivation_log: list, envelope: dict) -> dict:
    """Run vacuity/axiom/style checks on generated artifacts."""
    audit = {
        "vacuity_check": _run_vacuity_linter(),
        "axiom_audit": _run_axiom_index(),
        "style_check": _run_style_check(),
        "dag_freshness": _check_dag_freshness(),
        "passed": True
    }
    # Evaluate
    for k, v in audit.items():
        if k != "passed" and isinstance(v, dict) and v.get("errors"):
            audit["passed"] = False
    return audit


def _run_vacuity_linter() -> dict:
    # Target the new SU(3) files specifically
    files = [
        "lean/InfoGeometry/Algebra/SpecialUnitary.lean",
        "lean/InfoGeometry/Algebra/GellMannBasis.lean",
        "lean/InfoGeometry/Algebra/StructureConstants.lean",
        "lean/InfoGeometry/Algebra/GellMannBridge.lean",
    ]
    all_errors = []
    for f in files:
        result = subprocess.run(
            ["python3", "tools/scripts/vacuity-linter.py", f, "--json"],
            capture_output=True, text=True, cwd="/home/goutev/repos/info-geometry-lean"
        )
        if result.returncode == 0:
            try:
                data = json.loads(result.stdout)
                if data.get("findings"):
                    all_errors.extend(data["findings"])
            except:
                pass
        else:
            all_errors.append({"error": f"linter failed on {f}: {result.stderr}"})
    return {"errors": all_errors}


def _run_axiom_index() -> dict:
    result = subprocess.run(
        ["python3", "tools/infra/axiom_index.py", "--json", "InfoGeometry.Algebra"],
        capture_output=True, text=True, cwd="/home/goutev/repos/info-geometry-lean"
    )
    # Extract JSON from output (may contain human-readable prefix)
    if result.returncode == 0:
        try:
            # Find the last line that looks like JSON
            for line in reversed(result.stdout.strip().split('\n')):
                line = line.strip()
                if line.startswith('{') and line.endswith('}'):
                    data = json.loads(line)
                    # Check for nonstandard axioms (excluding standard ones)
                    standard = {"propext", "Classical.choice", "Quot.sound"}
                    suspicious = {k: v for k, v in data.get("axiom_usage", {}).items() if k not in standard}
                    if suspicious:
                        return {"errors": [f"Nonstandard axioms: {suspicious}"]}
                    return {"errors": []}
        except Exception:
            pass
    return {"errors": [result.stderr or result.stdout or "axiom_index failed"]}


def _run_style_check() -> dict:
    # Check mathlib style - placeholder
    return {"errors": []}


def _check_dag_freshness() -> dict:
    # Check artifacts/dag/index/meta.json timestamp
    meta = Path("artifacts/dag/index/meta.json")
    if not meta.exists():
        return {"errors": ["DAG index not found"]}
    # Check if meta is recent (within 24 hours)
    import os, time
    mtime = os.path.getmtime(meta)
    if time.time() - mtime > 86400:
        return {"errors": ["DAG index stale (>24h)"]}
    return {"errors": []}


# ─── Stage C: Acceptance (QA-A role) ───
def stage_C(audit: dict, envelope: dict) -> dict:
    """Run final build gate and produce acceptance record."""
    if not audit.get("passed", False):
        return {"accepted": False, "reason": "Audit failed", "audit": audit}
    
    # Build the target module
    result = subprocess.run(
        ["lake", "build", "InfoGeometry.Algebra.SpecialUnitary"],
        capture_output=True, text=True, timeout=300,
        cwd="/home/goutev/repos/info-geometry-lean"
    )
    
    accepted = result.returncode == 0
    return {
        "accepted": accepted,
        "build_log": result.stdout[-2000:] if result.stdout else "",
        "build_errors": result.stderr[-2000:] if result.stderr else "",
        "audit": audit,
        "git_head": subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    }


# ─── Stage D: Publication / State Update ───
def stage_D(acceptance: dict, state: PipelineState):
    """Update pipeline state, commit if accepted."""
    state.stage = "DONE" if acceptance.get("accepted") else "FAILED"
    state.acceptance_record = acceptance
    state.save()
    
    if acceptance.get("accepted"):
        # Stage changes
        subprocess.run(["git", "add", "-A"], cwd="/home/goutev/repos/info-geometry-lean")
        msg = f"Omega: {state.concept_id} — {acceptance.get('git_head', '')[:8]}"
        subprocess.run(["git", "commit", "-m", msg], cwd="/home/goutev/repos/info-geometry-lean")


# ─── Main Pipeline Runner ───
def run_pipeline(intent_path: str, run_id: Optional[str] = None):
    run_id = run_id or datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    state = PipelineState(
        run_id=run_id,
        stage="F",
        concept_id="",
        formal_intent_envelope={},
        derivation_log=[]
    )
    
    try:
        # Stage F
        envelope = stage_F(Path(intent_path))
        state.concept_id = envelope["concept_id"]
        state.formal_intent_envelope = envelope
        state.stage = "A"
        state.save()
        
        # Stage A
        print(f"[{run_id}] Stage A: Derivation...")
        derivation_log = stage_A(envelope, run_id)
        state.derivation_log = derivation_log
        state.stage = "B"
        state.save()
        
        # Stage B
        print(f"[{run_id}] Stage B: Audit...")
        audit = stage_B(derivation_log, envelope)
        state.audit_report = audit
        state.stage = "C"
        state.save()
        
        # Stage C
        print(f"[{run_id}] Stage C: Acceptance...")
        acceptance = stage_C(audit, envelope)
        state.acceptance_record = acceptance
        state.stage = "D"
        state.save()
        
        # Stage D
        print(f"[{run_id}] Stage D: Publication...")
        stage_D(acceptance, state)
        
        print(f"[{run_id}] Pipeline {'COMPLETED' if acceptance.get('accepted') else 'FAILED'}")
        return state
        
    except Exception as e:
        state.stage = "ERROR"
        state.derivation_log.append({"error": str(e)})
        state.save()
        raise


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--intent", required=True, help="Path to formal intent envelope JSON")
    parser.add_argument("--run-id", help="Optional run ID")
    args = parser.parse_args()
    run_pipeline(args.intent, args.run_id)