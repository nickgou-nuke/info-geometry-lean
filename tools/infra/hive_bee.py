#!/usr/bin/env python3
"""Queue-backed autoproof bee for the live Hive manifold.

This worker enforces the repo's trust boundary:
- retrieve graph-grounded context from the theorem DAG on 8529 first
- ask a prover model for a tactic only after retrieval succeeds
- verify every tactic through the Lean REPL bridge
- fossilize successes back into hive_live
- record structured deadends/rejections to avoid blind churn
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.hermes_bounded_runner import call_openai_compatible
from tools.infra import hive_arango_queue as queue_tool
from tools.infra.ingest_hive_json import ingest_text
from tools.infra.lean_interact_wrapper import apply_tactic, get_proof_state


def emit_packet(
    config: "BeeConfig",
    packet: dict[str, Any],
    *,
    task_key: str | None = None,
    dependencies: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    return queue_tool.import_packet_with_lineage(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        packet=packet,
        task_key_value=task_key,
        dependencies=dependencies,
    )

DEFAULT_HIVE_ENDPOINT = queue_tool.DEFAULT_ENDPOINT
DEFAULT_HIVE_DATABASE = queue_tool.DEFAULT_DATABASE
DEFAULT_HIVE_USERNAME = queue_tool.DEFAULT_USERNAME
DEFAULT_HIVE_PASSWORD = queue_tool.DEFAULT_PASSWORD
DEFAULT_QUEUE = queue_tool.DEFAULT_QUEUE
DEFAULT_WORKER_ID = "hive-bee-001"
DEFAULT_LEASE_SECONDS = queue_tool.DEFAULT_LEASE_SECONDS
DEFAULT_GRAVITY_BASE_URL = "http://127.0.0.1:8529"
DEFAULT_GRAVITY_DATABASE = "infogeometry"
DEFAULT_MODEL_BASE_URL = "http://127.0.0.1:8001/v1"
DEFAULT_MODEL = "deepseek-prover-v2-7b"
DEFAULT_API_KEY = "***"
DEFAULT_BACKEND_CAPABILITY = "proof_tactic_proposal"
DEFAULT_HERMES_ROLE = "hive_proof_bee"
DEFAULT_TOP_K = 6
DEFAULT_MAX_ATTEMPTS = 3
ARTIFACT_DIR = ROOT / "artifacts" / "hermes_loop" / "hive_bee"
GRAVITY_TOOL = ROOT / "tools" / "infra" / "arango_gravity_context.py"


@dataclass(frozen=True)
class BeeConfig:
    hive_endpoint: str
    hive_database: str
    hive_username: str
    hive_password: str
    queue_name: str
    worker_id: str
    lease_seconds: int
    gravity_base_url: str
    gravity_database: str
    gravity_top_k: int
    model_base_url: str
    model_name: str
    api_key: str
    backend_kind: str
    backend_identity: str
    subscription_backed: bool
    backend_capability: str
    hermes_role: str
    allow_direct_provider_api: bool
    timeout: int
    tactic_override: str | None = None


@dataclass
class BeeAttempt:
    task: dict[str, Any]
    goal: dict[str, Any]
    proof_state: dict[str, Any]
    gravity_context: dict[str, Any]
    gravity_path: Path
    proposed_tactic: str
    verification: dict[str, Any]
    elapsed_wall_s: float
    lean_latency_s: float


def utc_now() -> str:
    return queue_tool.iso_now()


def sanitize_identifier(text: str) -> str:
    text = re.sub(r"[^A-Za-z0-9_]+", "_", text.strip())
    text = re.sub(r"_+", "_", text).strip("_")
    return text or "goal"


def parse_imports(goal: dict[str, Any]) -> list[str]:
    imports = goal.get("imports") or goal.get("lean_imports") or []
    if isinstance(imports, str):
        imports = [item.strip() for item in imports.split(",") if item.strip()]
    if isinstance(imports, list):
        out = [str(item).strip() for item in imports if str(item).strip()]
        return out or ["Mathlib"]
    return ["Mathlib"]


def parse_context(goal: dict[str, Any]) -> str:
    context = goal.get("lean_context") or goal.get("context") or ""
    return str(context)


def build_gravity_query(goal: dict[str, Any]) -> str:
    parts = [
        str(goal.get("target_pretty") or ""),
        str(goal.get("canonical_shape") or ""),
        str(goal.get("module") or ""),
        str(goal.get("entity_key") or ""),
        "operator partition massieu modular drazin weyl fisher hessian",
    ]
    return re.sub(r"\s+", " ", " ".join(part for part in parts if part).strip())


def run_gravity_retrieval(config: BeeConfig, goal: dict[str, Any], task_key: str) -> tuple[dict[str, Any] | None, Path, str | None]:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    out_path = ARTIFACT_DIR / f"{task_key}-gravity.json"
    query = build_gravity_query(goal)
    cmd = [
        sys.executable,
        str(GRAVITY_TOOL),
        "--query",
        query,
        "--source",
        "auto",
        "--graph-mode",
        "faithful",
        "--scc-anchor-first",
        "--top-k",
        str(config.gravity_top_k),
        "--max-hops",
        "8",
        "--arango-url",
        config.gravity_base_url,
        "--arango-db",
        config.gravity_database,
        "--json-out",
        str(out_path),
        "--repo-root",
        str(ROOT),
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=config.timeout,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001
        return None, out_path, repr(exc)
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or f"gravity exit {proc.returncode}").strip()
        return None, out_path, detail
    if not out_path.exists():
        return None, out_path, "gravity retrieval produced no JSON artifact"
    payload = json.loads(out_path.read_text(encoding="utf-8"))
    return payload, out_path, None


def summarize_gravity_context(context: dict[str, Any]) -> str:
    items = context.get("items") or []
    lines = [
        f"graph_source={context.get('graph_source')} graph_mode={context.get('graph_mode')}",
        f"node_count={context.get('node_count')} edge_count={context.get('edge_count')}",
    ]
    for item in items[:4]:
        witness = item.get("faithful_witness") or {}
        lines.append(
            f"- {item.get('id') or item.get('name')} module={item.get('module')} score={item.get('score')} "
            f"scc={witness.get('scc_key') or witness.get('scc_id')} raw={witness.get('raw_doc_id')}"
        )
        excerpt = item.get("source_excerpt") or {}
        excerpt_lines = excerpt.get("lines") or []
        if excerpt_lines:
            sample = " ".join(str(row.get("text") or "").strip() for row in excerpt_lines[:2]).strip()
            if sample:
                lines.append(f"  source: {sample[:220]}")
    return "\n".join(lines)


def build_bee_prompt(goal: dict[str, Any], proof_state: dict[str, Any], gravity_context: dict[str, Any]) -> str:
    return (
        "You are a proof bee for info-geometry-lean.\n"
        "Return exactly one Lean tactic or a short tactic block.\n"
        "Do not claim proof success; propose only a tactic to test.\n"
        "Output format:\n"
        "TACTIC: <Lean tactic text>\n"
        "RATIONALE: <one sentence>\n\n"
        f"Goal target: {goal.get('target_pretty') or goal.get('canonical_shape') or goal.get('entity_key')}\n"
        f"Module hint: {goal.get('module') or 'none'}\n"
        f"Current proof state:\n{proof_state.get('proof_state') or '(no proof state)'}\n\n"
        f"Gravitational context:\n{summarize_gravity_context(gravity_context)}\n"
    )


def extract_tactic(text: str) -> str:
    def normalize(candidate: str) -> str:
        candidate = candidate.strip()
        if not candidate:
            return ""
        if candidate.startswith(("#", "//", "/*", "RATIONALE:", "VERDICT:", "NOTES:", "PROMOTION_ALLOWED:")):
            return ""
        if candidate.startswith("TACTIC:"):
            candidate = candidate.split(":", 1)[1].strip()
        theorem_match = re.search(r"(?:^|\n)theorem\b.*?:=\s*by\n(?P<body>.*)$", candidate, flags=re.DOTALL)
        if theorem_match:
            body = theorem_match.group("body").strip()
            return body
        inline_by_match = re.search(r":=\s*by\s*(?P<body>.+)$", candidate, flags=re.DOTALL)
        if inline_by_match and "theorem" in candidate:
            body = inline_by_match.group("body").strip()
            return body
        return candidate

    match = re.search(r"(?im)^TACTIC:\s*(.+)$", text)
    if match:
        tactic = normalize(match.group(1))
        if tactic:
            return tactic
    fenced = re.search(r"```(?:lean|lean4)?\n(.*?)```", text, flags=re.DOTALL)
    if fenced:
        tactic = normalize(fenced.group(1))
        if tactic:
            return tactic
    for line in text.strip().splitlines():
        candidate = normalize(line)
        if candidate:
            return candidate
    return ""


def propose_tactic(config: BeeConfig, goal: dict[str, Any], proof_state: dict[str, Any], gravity_context: dict[str, Any]) -> str:
    if config.tactic_override:
        return config.tactic_override.strip()
    if config.backend_kind == "provider_api" and not config.allow_direct_provider_api:
        raise RuntimeError(
            "direct provider_api backend is disabled; route provider contact through a Codex CLI-backed backend "
            "or pass --allow-direct-provider-api explicitly"
        )
    prompt = build_bee_prompt(goal, proof_state, gravity_context)
    response = call_openai_compatible(
        base_url=config.model_base_url,
        model=config.model_name,
        api_key=config.api_key,
        prompt=prompt,
        timeout=config.timeout,
        max_tokens=220,
    )
    text = ""
    choices = response.get("choices") or []
    if choices:
        message = choices[0].get("message") or {}
        text = str(message.get("content") or message.get("reasoning_content") or "")
    tactic = extract_tactic(text)
    if not tactic:
        raise RuntimeError("model returned no tactic")
    return tactic


def infer_blocked_dependency(gravity_context: dict[str, Any], verification_output: str) -> dict[str, Any] | None:
    text = verification_output.lower()
    items = [item for item in (gravity_context.get("items") or []) if isinstance(item, dict)]
    if not items:
        return None
    likely_block = any(
        marker in text
        for marker in [
            "unknown constant",
            "unknown identifier",
            "failed to synthesize",
            "type mismatch",
            "application type mismatch",
            "unsolved goals",
            "cannot be applied",
            "don't know how to synthesize",
        ]
    )
    if not likely_block:
        return None
    best: dict[str, Any] | None = None
    best_score = -1
    for item in items:
        score = 0
        names = [str(item.get("id") or ""), str(item.get("name") or ""), str(item.get("module") or "")]
        for name in names:
            if not name:
                continue
            tokens = [tok.lower() for tok in re.split(r"[^A-Za-z0-9_]+", name) if len(tok) >= 3]
            if any(tok and tok in text for tok in tokens):
                score += 3
        if item.get("score") is not None:
            try:
                score += int(float(item.get("score")) // 100)
            except Exception:  # noqa: BLE001
                pass
        if score > best_score:
            best_score = score
            best = item
    if not best:
        best = items[0]
    witness = best.get("faithful_witness") or {}
    return {
        "candidate_id": best.get("id") or best.get("name"),
        "module": best.get("module"),
        "score": best.get("score"),
        "scc_key": witness.get("scc_key") or witness.get("scc_id"),
        "raw_doc_id": witness.get("raw_doc_id"),
        "reason": "gravity-nearest likely dependency/blocker inferred from Lean verification output",
    }



def build_deadend_doc(goal: dict[str, Any], task: dict[str, Any], *, worker_id: str, tactic: str, failure_kind: str, verification: dict[str, Any], gravity_path: Path, elapsed_wall_s: float, lean_latency_s: float, gravity_context: dict[str, Any] | None = None) -> dict[str, Any]:
    key = queue_tool.stable_key(
        "deadend",
        str(goal.get("_key")),
        tactic,
        failure_kind,
        str(task.get("claim_count") or 0),
    )
    output = ((verification.get("lean") or {}).get("stdout") or "") + ((verification.get("lean") or {}).get("stderr") or "")
    blocked_dependency = infer_blocked_dependency(gravity_context or {}, output) if gravity_context else None
    return {
        "_key": key,
        "schema": "info_geometry.hive_deadend.v1",
        "antiproof_kind": "lean_nonclosure",
        "authority_level": "lean_checked",
        "corridor": "proof.search",
        "forbids_downstream": ["build.verify", "audit.semantic", "promotion.decide"],
        "global_impossibility_claim": False,
        "goal_key": goal.get("_key"),
        "goal_hash_shape": goal.get("goal_hash_shape"),
        "task_key": task.get("_key"),
        "worker_id": worker_id,
        "const_name": None,
        "attempted_tactic": tactic,
        "attempted_tactic_family": tactic.split()[0] if tactic.split() else tactic,
        "local_context_slice": parse_context(goal),
        "failure_kind": failure_kind,
        "retry_policy": {"max_attempts": goal.get("max_attempts") or DEFAULT_MAX_ATTEMPTS},
        "blocked_by_dependency": blocked_dependency,
        "verification_output": output[-4000:],
        "gravity_context_path": str(gravity_path),
        "metabolic_cost": {
            "wall_time_s": round(elapsed_wall_s, 6),
            "lean_verification_latency_s": round(lean_latency_s, 6),
            "retrieval_breadth": DEFAULT_TOP_K,
            "retries_before_closure": int((task.get("claim_count") or 1) - 1),
            "proof_depth": len([line for line in tactic.splitlines() if line.strip()]),
        },
        "state_taxonomy": ["retrieved", "proposed", "checked", "deadend"],
        "created_at": utc_now(),
    }


def build_fossil_record(goal: dict[str, Any], task: dict[str, Any], *, worker_id: str, tactic: str, gravity_path: Path, elapsed_wall_s: float, lean_latency_s: float) -> dict[str, Any]:
    const_name = f"hive.{sanitize_identifier(str(goal.get('module') or 'goal'))}.{task.get('_key')}"
    packet = {
        "artifactKind": "DiamondFossil",
        "space": "logos",
        "constName": const_name,
        "declarationKind": "theorem",
        "fullTypePretty": str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        "conclusionPretty": str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        "kernelStatus": "verified",
        "axiomsUsed": [],
        "proofTactic": tactic,
        "goalKey": goal.get("_key"),
        "taskKey": task.get("_key"),
        "workerId": worker_id,
        "gravityContextPath": str(gravity_path),
        "metabolicCost": {
            "wall_time_s": round(elapsed_wall_s, 6),
            "lean_verification_latency_s": round(lean_latency_s, 6),
            "proof_depth": len([line for line in tactic.splitlines() if line.strip()]),
        },
        "stateTaxonomy": ["retrieved", "proposed", "checked", "fossilized"],
    }
    canonical_shape = str(goal.get("canonical_shape") or goal.get("target_pretty") or goal.get("entity_key") or "")
    packet_bytes = json.dumps(packet, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    import hashlib
    return {
        "schema": "info_geometry.hive_memory.v1",
        "source": "hive-bee",
        "line_number": 0,
        "packet_index": 0,
        "artifact_kind": "DiamondFossil",
        "space": "logos",
        "entity_key": const_name,
        "canonical_shape": canonical_shape,
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "shape_sha256": hashlib.sha256(canonical_shape.encode("utf-8")).hexdigest(),
        "packet": packet,
    }


def theorem_name_for_task(goal: dict[str, Any], task: dict[str, Any]) -> str:
    return f"hive_{sanitize_identifier(str(goal.get('module') or 'goal'))}_{sanitize_identifier(str(task.get('_key') or 'task'))}"


def generated_theorem_source(goal: dict[str, Any], task: dict[str, Any], tactic: str) -> tuple[str, str]:
    theorem_name = theorem_name_for_task(goal, task)
    imports = parse_imports(goal)
    context = parse_context(goal)
    target = str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or "")
    lines: list[str] = []
    lines.extend(f"import {name}" for name in dict.fromkeys([*imports, "InfoGeometry.Meta.HiveLogos"]))
    lines.append("")
    if context.strip():
        lines.extend(line.rstrip() for line in context.splitlines())
        lines.append("")
    lines.append(f"theorem {theorem_name} : {target} := by")
    for line in tactic.splitlines():
        lines.append(f"  {line}" if line.strip() else "")
    lines.append("")
    lines.append(f"#hive_index_decl {theorem_name}")
    lines.append("")
    return theorem_name, "\n".join(lines)


def run_generated_theorem_capture(
    goal: dict[str, Any],
    task: dict[str, Any],
    tactic: str,
    *,
    timeout: int,
) -> tuple[str, str, str, list[dict[str, Any]]]:
    theorem_name, source = generated_theorem_source(goal, task, tactic)
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", prefix=f"{theorem_name}_", dir=ARTIFACT_DIR, encoding="utf-8", delete=False) as handle:
        handle.write(source)
        path = Path(handle.name)
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        output = (proc.stdout or "") + (proc.stderr or "")
        if proc.returncode != 0:
            raise RuntimeError(output.strip() or f"generated theorem check failed for {theorem_name}")
        records = ingest_text(output, source=f"hive-bee:{theorem_name}")
        if not records:
            raise RuntimeError(f"no HIVE_JSON fossils emitted for {theorem_name}")
        return theorem_name, source, output, records
    finally:
        path.unlink(missing_ok=True)


def gravity_neighbors_used(context: dict[str, Any]) -> list[dict[str, Any]]:
    neighbors: list[dict[str, Any]] = []
    for item in context.get("items") or []:
        if not isinstance(item, dict):
            continue
        witness = item.get("faithful_witness") or {}
        neighbors.append(
            {
                "id": item.get("id") or item.get("name"),
                "module": item.get("module"),
                "score": item.get("score"),
                "scc_key": witness.get("scc_key") or witness.get("scc_id"),
                "raw_doc_id": witness.get("raw_doc_id"),
            }
        )
    return neighbors


def lean_output_from_verification(verification: dict[str, Any]) -> str:
    lean = verification.get("lean") or {}
    return str(lean.get("stdout") or "") + str(lean.get("stderr") or "")


def build_replay_packet(
    attempt: BeeAttempt,
    *,
    worker_id: str,
    fossil_doc: dict[str, Any],
    theorem_name: str,
    theorem_source: str,
    generated_lean_output: str,
) -> dict[str, Any]:
    fossil_key = str(fossil_doc.get("_key") or "")
    now = utc_now()
    proof_state_text = str(attempt.proof_state.get("proof_state") or "")
    tactic_verification_output = lean_output_from_verification(attempt.verification)
    return {
        "_key": queue_tool.stable_key(
            "replay",
            str(attempt.goal.get("_key") or ""),
            str(attempt.task.get("_key") or ""),
            fossil_key,
        ),
        "schema": "info_geometry.hive_replay_packet.v1",
        "authority": "lean_checked",
        "representation_class": "owner",
        "representation_depth": "operatorial",
        "source_regime": "theorem_lane",
        "verification_origin": "replay_lane",
        "goal_key": attempt.goal.get("_key"),
        "task_key": attempt.task.get("_key"),
        "fossil_key": fossil_key,
        "worker_id": worker_id,
        "generated_theorem_name": theorem_name,
        "theorem_source": theorem_source,
        "gravity_neighbors": gravity_neighbors_used(attempt.gravity_context),
        "gravity_context_path": str(attempt.gravity_path),
        "proof_state_before": proof_state_text,
        "tactic_trace": [
            {
                "phase": "proposed",
                "tactic": attempt.proposed_tactic,
                "tactic_family": attempt.proposed_tactic.split()[0]
                if attempt.proposed_tactic.split()
                else attempt.proposed_tactic,
            },
            {
                "phase": "apply_tactic",
                "status": attempt.verification.get("status"),
                "lean_output": tactic_verification_output[-4000:],
            },
            {
                "phase": "generated_theorem_check",
                "status": "success",
                "lean_output": generated_lean_output[-4000:],
            },
        ],
        "lean_output": {
            "proof_state": proof_state_text,
            "tactic_verification": tactic_verification_output[-4000:],
            "generated_theorem_check": generated_lean_output[-4000:],
        },
        "metabolic_cost": {
            "wall_time_s": round(attempt.elapsed_wall_s, 6),
            "lean_verification_latency_s": round(attempt.lean_latency_s, 6),
            "proof_depth": len([line for line in attempt.proposed_tactic.splitlines() if line.strip()]),
            "gravity_neighbors_count": len(gravity_neighbors_used(attempt.gravity_context)),
        },
        "timestamps": {
            "created_at": now,
            "goal_created_at": attempt.goal.get("created_at"),
            "task_created_at": attempt.task.get("created_at"),
            "task_claimed_at": attempt.task.get("claimed_at") or attempt.task.get("claimed_at_utc"),
            "fossil_created_at": fossil_doc.get("created_at"),
        },
    }


def emit_attempt_packets(
    config: BeeConfig,
    *,
    goal: dict[str, Any],
    task: dict[str, Any],
    gravity_context: dict[str, Any],
    gravity_path: Path,
    proof_state: dict[str, Any],
    tactic: str,
    verification: dict[str, Any] | None = None,
    emit_proposal: bool = True,
) -> dict[str, dict[str, Any]]:
    goal_key = str(goal.get("_key") or "")
    task_key = str(task.get("_key") or "")
    retrieval_packet = {
        "schema": "hive.packet.retrieval.v1",
        "goal_key": goal_key,
        "authority": "navigation",
        "representation_class": "owner",
        "representation_depth": "operatorial",
        "retrieval_kind": "graph",
        "source_lane": "arango8529" if gravity_context.get("graph_source") == "arango" else "jsonl_fallback",
        "freshness": gravity_context.get("graph_source") or "unknown",
        "items": gravity_context.get("items") or [],
        "scc_anchors": [
            (item.get("faithful_witness") or {}).get("scc_key") or (item.get("faithful_witness") or {}).get("scc_id")
            for item in (gravity_context.get("items") or []) if isinstance(item, dict)
        ],
        "raw_witnesses": [item.get("faithful_witness") for item in (gravity_context.get("items") or []) if isinstance(item, dict)],
        "source_excerpts": [item.get("source_excerpt") for item in (gravity_context.get("items") or []) if isinstance(item, dict)],
        "graph_outage": False,
        "stale_warning": gravity_context.get("graph_source") != "arango",
        "artifact_path": str(gravity_path),
    }
    retrieval_row = emit_packet(config, retrieval_packet, task_key=task_key)["packet"]

    proof_state_packet = {
        "schema": "hive.packet.proof_state.v1",
        "goal_key": goal_key,
        "authority": "navigation",
        "representation_class": "owner",
        "representation_depth": "operatorial",
        "imports": parse_imports(goal),
        "context": parse_context(goal),
        "goal_text": str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        "proof_state": str(proof_state.get("proof_state") or ""),
        "wrapper_version": "lean_interact_wrapper",
    }
    proof_state_row = emit_packet(config, proof_state_packet, task_key=task_key)["packet"]

    if not emit_proposal:
        return {
            "retrieval": retrieval_row,
            "proof_state": proof_state_row,
        }

    proposal_packet = {
        "schema": "hive.packet.proposal.v1",
        "goal_key": goal_key,
        "proof_state_key": proof_state_row["packet_key"],
        "retrieval_key": retrieval_row["packet_key"],
        "authority": "proposal",
        "representation_class": "owner",
        "representation_depth": "operatorial",
        "proposal_kind": "tactic",
        "content": tactic,
        "rationale": "proof bee proposed tactic from proof state and retrieval context",
        "model": config.model_name,
        "backend_kind": "manual_override" if config.tactic_override else config.backend_kind,
        "backend_identity": "manual_override" if config.tactic_override else config.backend_identity,
        "subscription_backed": False if config.tactic_override else config.subscription_backed,
        "backend_capability": config.backend_capability,
        "hermes_role": "manual_operator" if config.tactic_override else config.hermes_role,
        "provider_contact_policy": "codex_cli_only_for_provider_contact",
    }
    proposal_row = emit_packet(
        config,
        proposal_packet,
        task_key=task_key,
        dependencies=[retrieval_row, proof_state_row],
    )["packet"]

    critique_packet = {
        "schema": "hive.packet.critique.v1",
        "proposal_key": proposal_row["packet_key"],
        "authority": "proposal",
        "hermes_role": config.hermes_role,
        "verdict": "approve",
        "reason": "single-bee lane approves its own frozen execution intent in Phase 1",
        "notes": "composite worker placeholder until critic bee is split out",
    }
    critique_row = emit_packet(config, critique_packet, task_key=task_key, dependencies=[proposal_row])["packet"]

    execution_intent_packet = {
        "schema": "hive.packet.execution_intent.v1",
        "proposal_key": proposal_row["packet_key"],
        "critique_key": critique_row["packet_key"],
        "authority": "execution_intent",
        "hermes_role": config.hermes_role,
        "intent_kind": "lean_tactic",
        "frozen_payload": {
            "goal": str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
            "tactic": tactic,
            "imports": parse_imports(goal),
            "context": parse_context(goal),
        },
    }
    execution_row = emit_packet(
        config,
        execution_intent_packet,
        task_key=task_key,
        dependencies=[proposal_row, critique_row],
    )["packet"]

    out = {
        "retrieval": retrieval_row,
        "proof_state": proof_state_row,
        "proposal": proposal_row,
        "critique": critique_row,
        "execution_intent": execution_row,
    }

    if verification is not None:
        verification_packet = {
            "schema": "hive.packet.verification.v1",
            "execution_intent_key": execution_row["packet_key"],
            "authority": "lean_checked",
            "source_regime": "theorem_lane",
            "verification_origin": "lean_produced",
            "verification_kind": "lean_tactic",
            "status": str(verification.get("status") or "failure"),
            "stdout": str((verification.get("lean") or {}).get("stdout") or ""),
            "stderr": str((verification.get("lean") or {}).get("stderr") or ""),
            "latency_s": float((verification.get("lean") or {}).get("latency_s") or 0.0),
        }
        out["verification"] = emit_packet(
            config,
            verification_packet,
            task_key=task_key,
            dependencies=[execution_row],
        )["packet"]
    return out


def write_replay_packet_artifact(packet: dict[str, Any]) -> Path:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    path = ARTIFACT_DIR / f"{packet['_key']}-replay.json"
    path.write_text(json.dumps(packet, indent=2, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    return path


def fossilize_success(config: BeeConfig, attempt: BeeAttempt) -> dict[str, Any]:
    theorem_name, theorem_source, generated_lean_output, records = run_generated_theorem_capture(
        attempt.goal,
        attempt.task,
        attempt.proposed_tactic,
        timeout=config.timeout,
    )
    fossil_records = [record for record in records if record.get("artifact_kind") in queue_tool.FOSSIL_ARTIFACT_KINDS]
    if not fossil_records:
        raise RuntimeError(f"generated theorem {theorem_name} emitted no fossil packet")
    fossil_record = fossil_records[0]
    packet = fossil_record.setdefault("packet", {})
    packet["proofTactic"] = attempt.proposed_tactic
    packet["goalKey"] = attempt.goal.get("_key")
    packet["taskKey"] = attempt.task.get("_key")
    packet["workerId"] = config.worker_id
    packet["gravityContextPath"] = str(attempt.gravity_path)
    packet["generatedTheoremName"] = theorem_name
    packet["generatedTheoremSource"] = theorem_source
    packet["metabolicCost"] = {
        "wall_time_s": round(attempt.elapsed_wall_s, 6),
        "lean_verification_latency_s": round(attempt.lean_latency_s, 6),
        "proof_depth": len([line for line in attempt.proposed_tactic.splitlines() if line.strip()]),
    }
    packet["stateTaxonomy"] = ["retrieved", "proposed", "checked", "fossilized"]
    fossil_doc = queue_tool.build_fossil_doc(fossil_record)
    replay_packet = build_replay_packet(
        attempt,
        worker_id=config.worker_id,
        fossil_doc=fossil_doc,
        theorem_name=theorem_name,
        theorem_source=theorem_source,
        generated_lean_output=generated_lean_output,
    )
    replay_path = write_replay_packet_artifact(replay_packet)
    packet["replayPacketKey"] = replay_packet["_key"]
    packet["replayPacketPath"] = str(replay_path)
    fossil_doc = queue_tool.build_fossil_doc(fossil_record)
    event_doc = queue_tool.build_event_doc(fossil_record)
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_fossils", [fossil_doc])
    queue_tool.import_rows(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        "hive_replay_packets",
        [replay_packet],
    )
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_events", [event_doc])
    queue_tool.import_rows(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        "hive_event_about",
        [queue_tool.build_event_edge(event_doc, "hive_fossils", fossil_doc["_key"])],
    )
    closed_edge = {
        "_key": queue_tool.stable_key("closedby", attempt.goal["_key"], fossil_doc["_key"]),
        "_from": f"hive_goals/{attempt.goal['_key']}",
        "_to": f"hive_fossils/{fossil_doc['_key']}",
        "schema": "info_geometry.hive_goal_closed_by.v1",
        "role": "closed_by",
        "created_at": utc_now(),
    }
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_goal_closed_by", [closed_edge])
    updated_goal = queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(attempt.goal["_key"]),
        status="closed",
        extra_fields={
            "closed_by_fossil_key": fossil_doc["_key"],
            "last_verified_tactic": attempt.proposed_tactic,
            "generated_theorem_name": theorem_name,
            "bee_state": "fossilized",
        },
    )
    updated_task = queue_tool.complete_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(attempt.task["_key"]),
        worker_id=config.worker_id,
    )
    return {
        "fossil": fossil_doc,
        "event": event_doc,
        "closed_edge": closed_edge,
        "replay_packet": replay_packet,
        "replay_packet_path": str(replay_path),
        "goal": updated_goal,
        "task": updated_task,
        "generated_theorem_name": theorem_name,
    }


def record_deadend(config: BeeConfig, attempt: BeeAttempt, failure_kind: str) -> dict[str, Any]:
    deadend_doc = build_deadend_doc(
        attempt.goal,
        attempt.task,
        worker_id=config.worker_id,
        tactic=attempt.proposed_tactic,
        failure_kind=failure_kind,
        verification=attempt.verification,
        gravity_path=attempt.gravity_path,
        elapsed_wall_s=attempt.elapsed_wall_s,
        lean_latency_s=attempt.lean_latency_s,
        gravity_context=attempt.gravity_context,
    )
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_deadends", [deadend_doc])
    rejection_edge = {
        "_key": queue_tool.stable_key("rejectedby", attempt.goal["_key"], deadend_doc["_key"]),
        "_from": f"hive_goals/{attempt.goal['_key']}",
        "_to": f"hive_deadends/{deadend_doc['_key']}",
        "schema": "info_geometry.hive_goal_rejected_by.v1",
        "role": "rejected_by",
        "created_at": utc_now(),
    }
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_goal_rejected_by", [rejection_edge])
    return {"deadend": deadend_doc, "rejection_edge": rejection_edge}


def max_attempts(goal: dict[str, Any]) -> int:
    value = goal.get("max_attempts") or goal.get("retry_policy", {}).get("max_attempts")
    try:
        return max(1, int(value))
    except Exception:  # noqa: BLE001
        return DEFAULT_MAX_ATTEMPTS


def fetch_claimed_task_and_goal(config: BeeConfig) -> tuple[dict[str, Any], dict[str, Any]] | tuple[None, None]:
    queue_tool.init_schema(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
    )
    queue_tool.heartbeat_worker(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        capabilities=["gravity-retrieval", "lean-verification", "fossilization", "deadend-memory"],
        queues=[config.queue_name],
    )
    task = queue_tool.claim_next_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        queue_name=config.queue_name,
        lease_seconds=config.lease_seconds,
        task_kind="proof.search",
    )
    if not task:
        return None, None
    goal = queue_tool.get_goal_for_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
    )
    if not goal:
        queue_tool.fail_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="claimed task has no goal document",
        )
        return None, None
    return task, goal


def run_one(config: BeeConfig) -> dict[str, Any]:
    task, goal = fetch_claimed_task_and_goal(config)
    if not task or not goal:
        return {"status": "idle", "worker_id": config.worker_id, "queue_name": config.queue_name}
    start = time.time()
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="retrieved",
        extra_fields={"bee_state": "retrieved", "claimed_by": config.worker_id},
    )
    gravity_context, gravity_path, gravity_error = run_gravity_retrieval(config, goal, str(task["_key"]))
    if gravity_error or not gravity_context:
        queue_tool.requeue_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message=f"gravity retrieval failed: {gravity_error}",
        )
        queue_tool.update_goal_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            goal_key_value=str(goal["_key"]),
            status="requeued",
            extra_fields={"bee_state": "requeued", "last_gravity_error": gravity_error},
        )
        return {"status": "requeued", "task": task, "goal": goal, "error": gravity_error}
    proof_state = get_proof_state(
        str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        imports=parse_imports(goal),
        context=parse_context(goal),
        timeout=config.timeout,
    )
    packet_trace = emit_attempt_packets(
        config,
        goal=goal,
        task=task,
        gravity_context=gravity_context,
        gravity_path=gravity_path,
        proof_state=proof_state,
        tactic="",
        verification=None,
        emit_proposal=False,
    )
    if proof_state.get("status") != "ok":
        queue_tool.fail_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="could not obtain Lean proof state",
        )
        queue_tool.update_goal_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            goal_key_value=str(goal["_key"]),
            status="failed",
            extra_fields={"bee_state": "failed", "last_proof_state_error": proof_state},
        )
        return {"status": "failed", "task": task, "goal": goal, "proof_state": proof_state}
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="proposed",
        extra_fields={
            "bee_state": "proposed",
            "gravity_context_path": str(gravity_path),
            "packet_trace": {
                "retrieval_key": packet_trace["retrieval"]["packet_key"],
                "proof_state_key": packet_trace["proof_state"]["packet_key"],
            },
        },
    )
    try:
        tactic = propose_tactic(config, goal, proof_state, gravity_context)
    except Exception as exc:  # noqa: BLE001
        error_message = str(exc) or repr(exc)
        updated_task = queue_tool.update_task_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            status="environment_blocked",
            extra_fields={
                "worker_id": None,
                "lease_expires_at": None,
                "blocked_kind": "provider_unavailable",
                "failure_kind": "retryable_transport_failure",
                "semantic_failure": False,
                "proof_failure": False,
                "provider_contact_policy": "codex_cli_only_for_provider_contact",
                "last_provider_error": error_message[-4000:],
                "retry_guidance": "restart or resume one canonical Codex CLI-backed agent session; do not fan out direct provider connections",
            },
        )
        updated_goal = queue_tool.update_goal_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            goal_key_value=str(goal["_key"]),
            status="environment_blocked",
            extra_fields={
                "bee_state": "environment_blocked",
                "blocked_kind": "provider_unavailable",
                "failure_kind": "retryable_transport_failure",
                "semantic_failure": False,
                "proof_failure": False,
                "last_provider_error": error_message[-4000:],
            },
        )
        return {
            "status": "environment_blocked",
            "blocked_kind": "provider_unavailable",
            "failure_kind": "retryable_transport_failure",
            "semantic_failure": False,
            "proof_failure": False,
            "task": updated_task or task,
            "goal": updated_goal or goal,
            "error": error_message,
        }
    packet_trace = emit_attempt_packets(
        config,
        goal=goal,
        task=task,
        gravity_context=gravity_context,
        gravity_path=gravity_path,
        proof_state=proof_state,
        tactic=tactic,
        verification=None,
    )
    lean_start = time.time()
    verification = apply_tactic(
        str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        tactic,
        imports=parse_imports(goal),
        context=parse_context(goal),
        timeout=config.timeout,
    )
    verification_packet = emit_packet(
        config,
        {
            "schema": "hive.packet.verification.v1",
            "execution_intent_key": packet_trace["execution_intent"]["packet_key"],
            "authority": "lean_checked",
            "representation_class": "owner",
            "representation_depth": "operatorial",
            "verification_kind": "lean_tactic",
            "status": str(verification.get("status") or "failure"),
            "stdout": str((verification.get("lean") or {}).get("stdout") or ""),
            "stderr": str((verification.get("lean") or {}).get("stderr") or ""),
            "latency_s": float((verification.get("lean") or {}).get("latency_s") or 0.0),
        },
        task_key=str(task["_key"]),
        dependencies=[packet_trace["execution_intent"]],
    )["packet"]
    lean_latency = time.time() - lean_start
    attempt = BeeAttempt(
        task=task,
        goal=goal,
        proof_state=proof_state,
        gravity_context=gravity_context,
        gravity_path=gravity_path,
        proposed_tactic=tactic,
        verification=verification,
        elapsed_wall_s=time.time() - start,
        lean_latency_s=lean_latency,
    )
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="checked",
        extra_fields={
            "bee_state": "checked",
            "last_proposed_tactic": tactic,
            "packet_trace": {
                "retrieval_key": packet_trace["retrieval"]["packet_key"],
                "proof_state_key": packet_trace["proof_state"]["packet_key"],
                "proposal_key": packet_trace["proposal"]["packet_key"],
                "critique_key": packet_trace["critique"]["packet_key"],
                "execution_intent_key": packet_trace["execution_intent"]["packet_key"],
                "verification_key": verification_packet["packet_key"],
            },
        },
    )
    if verification.get("status") == "success":
        fossil = fossilize_success(config, attempt)
        return {
            "status": "fossilized",
            "task": fossil.get("task") or task,
            "goal": fossil.get("goal") or goal,
            "tactic": tactic,
            "fossil": fossil,
        }
    rejection = record_deadend(config, attempt, "lean_verification_failure")
    attempts = int(task.get("claim_count") or 1)
    if attempts < max_attempts(goal):
        queue_tool.requeue_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="tactic failed verification; requeued",
        )
        queue_tool.update_goal_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            goal_key_value=str(goal["_key"]),
            status="requeued",
            extra_fields={"bee_state": "requeued", "last_deadend_key": rejection["deadend"]["_key"]},
        )
        return {"status": "requeued", "task": task, "goal": goal, "tactic": tactic, "deadend": rejection}
    queue_tool.fail_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
        worker_id=config.worker_id,
        error_message="maximum attempts reached after Lean verification failures",
    )
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="deadend",
        extra_fields={"bee_state": "deadend", "last_deadend_key": rejection["deadend"]["_key"]},
    )
    return {"status": "deadend", "task": task, "goal": goal, "tactic": tactic, "deadend": rejection}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-endpoint", default=DEFAULT_HIVE_ENDPOINT)
    parser.add_argument("--hive-database", default=DEFAULT_HIVE_DATABASE)
    parser.add_argument("--hive-username", default=DEFAULT_HIVE_USERNAME)
    parser.add_argument("--hive-password", default=DEFAULT_HIVE_PASSWORD)
    parser.add_argument("--queue-name", default=DEFAULT_QUEUE)
    parser.add_argument("--worker-id", default=DEFAULT_WORKER_ID)
    parser.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)
    parser.add_argument("--gravity-base-url", default=DEFAULT_GRAVITY_BASE_URL)
    parser.add_argument("--gravity-database", default=DEFAULT_GRAVITY_DATABASE)
    parser.add_argument("--gravity-top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--model-base-url", default=DEFAULT_MODEL_BASE_URL)
    parser.add_argument("--model-name", default=DEFAULT_MODEL)
    parser.add_argument("--api-key", default=DEFAULT_API_KEY)
    parser.add_argument("--backend-kind", default=None)
    parser.add_argument("--backend-identity", default=None)
    parser.add_argument("--subscription-backed", action="store_true")
    parser.add_argument("--backend-capability", default=DEFAULT_BACKEND_CAPABILITY)
    parser.add_argument("--hermes-role", default=DEFAULT_HERMES_ROLE)
    parser.add_argument(
        "--allow-direct-provider-api",
        action="store_true",
        help="explicitly permit direct provider_api model calls; default policy routes provider contact through Codex CLI",
    )
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--tactic-override", default=None)
    parser.add_argument("--once", action="store_true", help="run one claim/attempt cycle and exit")
    parser.add_argument("--poll-interval", type=int, default=15)
    return parser.parse_args()


def is_local_model_url(url: str) -> bool:
    parsed = urlparse(url)
    host = (parsed.hostname or "").lower()
    return host in {"127.0.0.1", "localhost", "::1"} or host.startswith("10.") or host.startswith("192.168.")


def infer_backend_kind(args: argparse.Namespace) -> str:
    if args.backend_kind:
        return str(args.backend_kind)
    if args.tactic_override:
        return "manual_override"
    if is_local_model_url(str(args.model_base_url)):
        return "local_openai_compatible"
    return "provider_api"


def config_from_args(args: argparse.Namespace) -> BeeConfig:
    backend_kind = infer_backend_kind(args)
    return BeeConfig(
        hive_endpoint=str(args.hive_endpoint).rstrip("/"),
        hive_database=str(args.hive_database),
        hive_username=str(args.hive_username),
        hive_password=str(args.hive_password),
        queue_name=str(args.queue_name),
        worker_id=str(args.worker_id),
        lease_seconds=int(args.lease_seconds),
        gravity_base_url=str(args.gravity_base_url).rstrip("/"),
        gravity_database=str(args.gravity_database),
        gravity_top_k=int(args.gravity_top_k),
        model_base_url=str(args.model_base_url).rstrip("/"),
        model_name=str(args.model_name),
        api_key=str(args.api_key),
        backend_kind=backend_kind,
        backend_identity=str(args.backend_identity or args.model_base_url).rstrip("/"),
        subscription_backed=bool(args.subscription_backed),
        backend_capability=str(args.backend_capability),
        hermes_role=str(args.hermes_role),
        allow_direct_provider_api=bool(args.allow_direct_provider_api),
        timeout=int(args.timeout),
        tactic_override=str(args.tactic_override).strip() if args.tactic_override else None,
    )


def main() -> int:
    args = parse_args()
    config = config_from_args(args)
    while True:
        result = run_one(config)
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        if args.once:
            return 0
        time.sleep(max(1, int(args.poll_interval)))


if __name__ == "__main__":
    raise SystemExit(main())
