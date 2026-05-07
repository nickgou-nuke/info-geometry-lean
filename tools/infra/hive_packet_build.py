#!/usr/bin/env python3
"""Build Hive packets with repo-local defaults and optional schema validation."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
except ImportError:  # pragma: no cover - CLI fallback
    from hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

ROOT = Path(__file__).resolve().parents[2]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def slug(text: str) -> str:
    out = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return out[:64] or "hive"


def stable_json(payload: Any) -> str:
    return json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def stable_digest(payload: Any, *, size: int = 12) -> str:
    data = json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(data.encode("utf-8")).hexdigest()[:size]


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(stable_json(payload), encoding="utf-8")
    tmp.replace(path)


def parse_ref_spec(spec: str) -> dict[str, Any]:
    parts = [p.strip() for p in spec.split("|")]
    ref = {"ref": parts[0]}
    if len(parts) > 1 and parts[1]:
        ref["kind"] = parts[1]
    if len(parts) > 2 and parts[2]:
        ref["role"] = parts[2]
    if len(parts) > 3 and parts[3]:
        try:
            ref["confidence"] = float(parts[3])
        except ValueError:
            raise SystemExit(f"ERROR: invalid confidence in ref spec: {spec}")
    return ref


def uniq(items: list[str]) -> list[str]:
    seen = set()
    out: list[str] = []
    for item in items:
        s = str(item).strip()
        if not s or s in seen:
            continue
        seen.add(s)
        out.append(s)
    return out


def base_envelope(args: argparse.Namespace, kind: str, status: str, *, identity_seed: dict[str, Any]) -> dict[str, Any]:
    lineage_id = args.lineage_id.strip()
    digest = stable_digest({"kind": kind, "lineage_id": lineage_id, **identity_seed})
    default_ids = {
        "SymbolicSeed": f"seed_{digest}",
        "InvariantDraft": f"invariant_{slug(lineage_id)}_{digest}",
        "TheoremCandidatePacket": f"packet_theorem_candidate_{slug(lineage_id)}_{digest}",
        "ExternalTheoremCandidatePacket": f"packet_external_theorem_candidate_{slug(lineage_id)}_{digest}",
        "ResiduePacket": f"packet_residue_{slug(lineage_id)}_{digest}",
        "ExecutionIntentPacket": f"packet_execution_intent_{slug(lineage_id)}_{digest}",
        "LeanVerificationPacket": f"packet_lean_verification_{slug(lineage_id)}_{digest}",
        "BuildPacket": f"packet_build_{slug(lineage_id)}_{digest}",
        "AuditPacket": f"packet_audit_{slug(lineage_id)}_{digest}",
        "PromotionDecisionPacket": f"packet_promotion_decision_{slug(lineage_id)}_{digest}",
    }
    envelope = {
        "id": (args.id or default_ids.get(kind, f"obj_{digest}")).strip(),
        "kind": kind,
        "status": status,
        "lineage_id": lineage_id,
        "revision": args.revision,
        "origin_run_id": (args.origin_run_id or f"run_{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}_{digest[:6]}").strip(),
        "created_by_agent": args.created_by_agent.strip(),
        "agent_role": args.agent_role.strip(),
        "backend": args.backend.strip(),
        "task_id": args.task_id.strip(),
        "session_key": args.session_key.strip(),
        "created_at": args.created_at or utc_now(),
        "updated_at": args.updated_at or utc_now(),
        "tags": uniq(args.tag or []),
        "notes": args.notes.strip(),
        "parent_refs": [parse_ref_spec(x) for x in (args.parent_ref or [])],
        "evidence_refs": [parse_ref_spec(x) for x in (args.evidence_ref or [])],
        "source_hashes": uniq(args.source_hash or []),
    }
    if not envelope["task_id"]:
        envelope.pop("task_id")
    if not envelope["session_key"]:
        envelope.pop("session_key")
    if not envelope["notes"]:
        envelope.pop("notes")
    if not envelope["tags"]:
        envelope.pop("tags")
    if not envelope["parent_refs"]:
        envelope.pop("parent_refs")
    if not envelope["evidence_refs"]:
        envelope.pop("evidence_refs")
    if not envelope["source_hashes"]:
        envelope.pop("source_hashes")
    return envelope


def with_metadata(packet: dict[str, Any], *, authority: str, representation_class: str, representation_depth: list[str] | str, promotion_allowed: bool | None = None) -> dict[str, Any]:
    packet["authority"] = authority
    packet["representation_class"] = representation_class
    packet["representation_depth"] = representation_depth
    if promotion_allowed is not None:
        packet["promotion_allowed"] = promotion_allowed
    return packet


def require_non_empty(name: str, value: str) -> str:
    text = value.strip()
    if not text:
        raise SystemExit(f"ERROR: {name} must be non-empty")
    return text


def build_symbolic_seed(args: argparse.Namespace) -> dict[str, Any]:
    source_locator: dict[str, Any] = {}
    if args.source_path:
        source_locator["path"] = args.source_path.strip()
    if args.source_section:
        source_locator["section"] = args.source_section.strip()
    if args.source_line_start:
        source_locator["line_start"] = args.source_line_start
    if args.source_line_end:
        source_locator["line_end"] = args.source_line_end
    if not source_locator:
        source_locator["source_ref"] = args.source_ref.strip()

    content_text = require_non_empty("--content-text", args.content_text)
    identity_seed = {
        "source_ref": args.source_ref.strip(),
        "content_text": content_text,
        "pressure_class": args.pressure_class.strip(),
    }
    packet = base_envelope(args, "SymbolicSeed", args.status, identity_seed=identity_seed)
    seed_material = {
        "lineage_id": args.lineage_id.strip(),
        "source_class": args.source_class.strip(),
        "source_ref": args.source_ref.strip(),
        "content_text": content_text,
        "pressure_class": args.pressure_class.strip(),
    }
    packet.update(
        {
            "seed_hash": args.seed_hash.strip() or f"sha256:{stable_digest(seed_material, size=32)}",
            "source_class": args.source_class.strip(),
            "source_ref": require_non_empty("--source-ref", args.source_ref),
            "source_excerpt": require_non_empty("--source-excerpt", args.source_excerpt),
            "source_locator": source_locator,
            "content_text": content_text,
            "pressure_class": args.pressure_class.strip(),
        }
    )
    return with_metadata(
        packet,
        authority="semantic",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
    )


def build_formulation_variant(args: argparse.Namespace) -> dict[str, Any]:
    content_text = require_non_empty("--content-text", args.content_text)
    summary = require_non_empty("--summary", args.summary)
    identity_seed = {
        "seed_hash": args.seed_hash.strip(),
        "variant_index": args.variant_index,
        "iteration_index": args.iteration_index,
        "representation_mode": args.representation_mode.strip(),
        "content_text": content_text,
    }
    packet = base_envelope(args, "FormulationVariant", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "seed_hash": require_non_empty("--seed-hash", args.seed_hash),
            "variant_index": args.variant_index,
            "iteration_index": args.iteration_index,
            "jung_pass_id": require_non_empty("--jung-pass-id", args.jung_pass_id),
            "representation_mode": args.representation_mode.strip(),
            "content_text": content_text,
            "summary": summary,
            "temperature_profile": require_non_empty("--temperature-profile", args.temperature_profile),
            "confidence": args.confidence,
            "formal_projection_score": args.formal_projection_score,
        }
    )
    return with_metadata(
        packet,
        authority="semantic",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
    )


def build_resonance_cluster(args: argparse.Namespace) -> dict[str, Any]:
    distinguishing_axes = uniq(args.distinguishing_axis or [])
    if not distinguishing_axes:
        raise SystemExit("ERROR: at least one --distinguishing-axis is required")
    identity_seed = {
        "cluster_method": args.cluster_method.strip(),
        "cluster_signature": args.cluster_signature.strip(),
        "member_count": args.member_count,
        "invariant_hypothesis": args.invariant_hypothesis.strip(),
    }
    packet = base_envelope(args, "ResonanceCluster", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "cluster_method": require_non_empty("--cluster-method", args.cluster_method),
            "cluster_signature": require_non_empty("--cluster-signature", args.cluster_signature),
            "member_count": args.member_count,
            "invariant_hypothesis": require_non_empty("--invariant-hypothesis", args.invariant_hypothesis),
            "distinguishing_axes": distinguishing_axes,
        }
    )
    return with_metadata(
        packet,
        authority="semantic",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
    )


def build_pauli_critique(args: argparse.Namespace) -> dict[str, Any]:
    variant_refs = [parse_ref_spec(x) for x in (args.variant_ref or [])]
    cluster_refs = [parse_ref_spec(x) for x in (args.cluster_ref or [])]
    invariant_refs = [parse_ref_spec(x) for x in (args.invariant_ref or [])]
    if not (variant_refs or cluster_refs or invariant_refs):
        raise SystemExit("ERROR: at least one target scope ref is required (--variant-ref, --cluster-ref, or --invariant-ref)")
    target_scope: dict[str, Any] = {}
    if variant_refs:
        target_scope["variant_refs"] = variant_refs
    if cluster_refs:
        target_scope["cluster_refs"] = cluster_refs
    if invariant_refs:
        target_scope["invariant_refs"] = invariant_refs
    identity_seed = {
        "iteration_index": args.iteration_index,
        "critique_mode": args.critique_mode.strip(),
        "targets": target_scope,
        "critique_text": args.critique_text.strip(),
    }
    packet = base_envelope(args, "PauliCritique", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "iteration_index": args.iteration_index,
            "critique_mode": args.critique_mode.strip(),
            "target_scope": target_scope,
            "critique_text": require_non_empty("--critique-text", args.critique_text),
            "novelty_assessment": require_non_empty("--novelty-assessment", args.novelty_assessment),
            "duplication_assessment": require_non_empty("--duplication-assessment", args.duplication_assessment),
            "formal_target_assessment": require_non_empty("--formal-target-assessment", args.formal_target_assessment),
            "repo_anchor_assessment": require_non_empty("--repo-anchor-assessment", args.repo_anchor_assessment),
            "admissibility_state": args.admissibility_state.strip(),
            "cost_class": args.cost_class.strip(),
        }
    )
    return with_metadata(
        packet,
        authority="semantic",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
    )


def build_translation_packet(args: argparse.Namespace) -> dict[str, Any]:
    invariant_refs = [parse_ref_spec(x) for x in (args.invariant_ref or [])]
    if not invariant_refs:
        raise SystemExit("ERROR: at least one --invariant-ref is required")
    signature_candidates = uniq(args.signature_candidate or [])
    if not signature_candidates:
        raise SystemExit("ERROR: at least one --signature-candidate is required")
    imports_candidate = uniq(args.import_candidate or [])
    probe_steps = uniq(args.probe_step or [])
    if not probe_steps:
        raise SystemExit("ERROR: at least one --probe-step is required")

    minimal_probe_plan = {
        "probe_kind": require_non_empty("--probe-kind", args.probe_kind),
        "steps": probe_steps,
    }
    identity_seed = {
        "invariants": invariant_refs,
        "namespace_candidate": args.namespace_candidate.strip(),
        "module_candidate": args.module_candidate.strip(),
        "signatures": signature_candidates,
    }
    packet = base_envelope(args, "TranslationPacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "invariant_refs": invariant_refs,
            "namespace_candidate": require_non_empty("--namespace-candidate", args.namespace_candidate),
            "signature_candidates": signature_candidates,
            "module_candidate": require_non_empty("--module-candidate", args.module_candidate),
            "imports_candidate": imports_candidate,
            "minimal_probe_plan": minimal_probe_plan,
            "declaration_name_candidates": uniq(args.declaration_name_candidate or []),
            "dependency_candidates": uniq(args.dependency_candidate or []),
            "target_surface": args.target_surface.strip(),
            "anchor_refs": [parse_ref_spec(x) for x in (args.anchor_ref or [])],
        }
    )
    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "invariant_refs",
            "namespace_candidate",
            "signature_candidates",
            "module_candidate",
            "imports_candidate",
            "minimal_probe_plan",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    if not packet["declaration_name_candidates"]:
        packet.pop("declaration_name_candidates")
    if not packet["dependency_candidates"]:
        packet.pop("dependency_candidates")
    if not packet["target_surface"]:
        packet.pop("target_surface")
    if not packet["anchor_refs"]:
        packet.pop("anchor_refs")
    return with_metadata(
        packet,
        authority="proposal",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_retrieval_hypothesis_packet(args: argparse.Namespace) -> dict[str, Any]:
    seed_refs = [parse_ref_spec(x) for x in (args.seed_ref or [])]
    if not seed_refs:
        raise SystemExit("ERROR: at least one --seed-ref is required")
    candidate_anchor_refs = [parse_ref_spec(x) for x in (args.candidate_anchor_ref or [])]
    identity_seed = {
        "query_text": args.query_text.strip(),
        "seed_refs": seed_refs,
        "graph_mode": args.graph_mode.strip(),
    }
    packet = base_envelope(args, "RetrievalHypothesisPacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "query_text": require_non_empty("--query-text", args.query_text),
            "seed_refs": seed_refs,
            "candidate_anchor_refs": candidate_anchor_refs,
            "graph_mode": args.graph_mode.strip(),
            "retrieval_summary": require_non_empty("--retrieval-summary", args.retrieval_summary),
        }
    )
    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "query_text",
            "seed_refs",
            "candidate_anchor_refs",
            "graph_mode",
            "retrieval_summary",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    return with_metadata(
        packet,
        authority="navigation",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_execution_intent_packet(args: argparse.Namespace) -> dict[str, Any]:
    target_refs = [parse_ref_spec(x) for x in (args.target_ref or [])]
    if not target_refs:
        raise SystemExit("ERROR: at least one --target-ref is required")
    intended_actions = uniq(args.intended_action or [])
    required_tools = uniq(args.required_tool or [])
    required_gates = uniq(args.required_gate or [])
    if not intended_actions:
        raise SystemExit("ERROR: at least one --intended-action is required")
    if not required_tools:
        raise SystemExit("ERROR: at least one --required-tool is required")
    if not required_gates:
        raise SystemExit("ERROR: at least one --required-gate is required")

    identity_seed = {
        "targets": target_refs,
        "actions": intended_actions,
        "mutation_scope": args.mutation_scope.strip(),
        "execution_allowed": args.execution_allowed,
    }
    packet = base_envelope(args, "ExecutionIntentPacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "target_refs": target_refs,
            "intended_actions": intended_actions,
            "required_tools": required_tools,
            "required_gates": required_gates,
            "mutation_scope": args.mutation_scope.strip(),
            "execution_allowed": args.execution_allowed,
        }
    )
    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "target_refs",
            "intended_actions",
            "required_tools",
            "required_gates",
            "mutation_scope",
            "execution_allowed",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    return with_metadata(
        packet,
        authority="execution_intent",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
    )


def build_lean_verification_packet(args: argparse.Namespace) -> dict[str, Any]:
    execution_refs = [parse_ref_spec(x) for x in (args.execution_intent_ref or [])]
    if not execution_refs:
        raise SystemExit("ERROR: at least one --execution-intent-ref is required")
    verification_outcomes = [x.lower() for x in uniq([args.verification_outcome])]
    if not verification_outcomes:
        raise SystemExit("ERROR: --verification-outcome is required")

    identity_seed = {
        "execution_intent": execution_refs,
        "verification_key": args.verification_key.strip(),
        "verification_outcome": args.verification_outcome.strip(),
        "execution_allowed": args.execution_allowed,
    }
    packet = base_envelope(args, "LeanVerificationPacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "execution_intent_ref": execution_refs[0],
            "execution_allowed": args.execution_allowed,
            "verification_key": require_non_empty("--verification-key", args.verification_key),
            "verification_outcome": verification_outcomes[0],
            "kernel_summary": require_non_empty("--kernel-summary", args.kernel_summary),
            "proof_status": args.proof_status.strip(),
            "proof_code": args.proof_code.strip(),
        }
    )
    if packet["proof_code"] == "":
        packet.pop("proof_code")
    if args.error_excerpt.strip():
        packet["error_excerpt"] = args.error_excerpt.strip()
    if args.lean_output.strip():
        packet["lean_output"] = args.lean_output.strip()

    if packet["proof_status"] not in ["pending", "verified", "blocked", "rejected"]:
        raise SystemExit("ERROR: --proof-status must be one of pending|verified|blocked|rejected")
    if packet["verification_outcome"] not in ["passed", "failed", "not_executed", "skipped"]:
        raise SystemExit("ERROR: --verification-outcome must be one of passed|failed|not_executed|skipped")

    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "execution_intent_ref",
            "execution_allowed",
            "verification_outcome",
            "proof_status",
            "verification_key",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    return with_metadata(
        packet,
        authority="lean_checked",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_build_packet(args: argparse.Namespace) -> dict[str, Any]:
    verification_refs = [parse_ref_spec(x) for x in (args.lean_verification_ref or [])]
    if not verification_refs:
        raise SystemExit("ERROR: at least one --lean-verification-ref is required")

    identity_seed = {
        "lean_verification": verification_refs,
        "build_command": args.build_command.strip(),
        "build_exit_code": args.build_exit_code,
        "build_success": args.build_success,
    }
    packet = base_envelope(args, "BuildPacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "lean_verification_ref": verification_refs[0],
            "build_key": require_non_empty("--build-key", args.build_key),
            "build_command": require_non_empty("--build-command", args.build_command),
            "build_exit_code": args.build_exit_code,
            "build_success": args.build_success,
        }
    )
    if args.build_output_excerpt.strip():
        packet["build_output_excerpt"] = args.build_output_excerpt.strip()
    if args.build_artifact:
        packet["build_artifacts"] = uniq(args.build_artifact)

    if args.build_exit_code < 0:
        raise SystemExit("ERROR: --build-exit-code must be a non-negative integer")

    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "lean_verification_ref",
            "build_key",
            "build_command",
            "build_exit_code",
            "build_success",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    return with_metadata(
        packet,
        authority="build_checked",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_audit_packet(args: argparse.Namespace) -> dict[str, Any]:
    build_refs = [parse_ref_spec(x) for x in (args.build_ref or [])]
    if not build_refs:
        raise SystemExit("ERROR: at least one --build-ref is required")

    findings = uniq(args.audit_finding or [])
    if not findings:
        raise SystemExit("ERROR: at least one --audit-finding is required")

    identity_seed = {
        "build_ref": build_refs,
        "audit_key": args.audit_key.strip(),
        "audit_scope": args.audit_scope.strip(),
    }
    packet = base_envelope(args, "AuditPacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "build_ref": build_refs[0],
            "audit_key": require_non_empty("--audit-key", args.audit_key),
            "audit_scope": args.audit_scope.strip(),
            "audit_findings": findings,
            "audit_outcome": require_non_empty("--audit-outcome", args.audit_outcome),
            "evidence_summary": require_non_empty("--evidence-summary", args.evidence_summary),
        }
    )

    if packet["audit_scope"] not in ["correctness", "safety", "build", "promotion"]:
        raise SystemExit("ERROR: --audit-scope must be one of correctness|safety|build|promotion")
    if packet["audit_outcome"] not in ["approved", "rejected", "deferred"]:
        raise SystemExit("ERROR: --audit-outcome must be one of approved|rejected|deferred")

    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "build_ref",
            "audit_key",
            "audit_scope",
            "audit_outcome",
            "audit_findings",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    return with_metadata(
        packet,
        authority="audit_checked",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_promotion_decision_packet(args: argparse.Namespace) -> dict[str, Any]:
    audit_refs = [parse_ref_spec(x) for x in (args.audit_ref or [])]
    if not audit_refs:
        raise SystemExit("ERROR: at least one --audit-ref is required")

    identity_seed = {
        "audit_ref": audit_refs,
        "promotion_key": args.promotion_key.strip(),
        "decision": args.decision.strip(),
    }
    packet = base_envelope(args, "PromotionDecisionPacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "audit_ref": audit_refs[0],
            "promotion_key": require_non_empty("--promotion-key", args.promotion_key),
            "decision": require_non_empty("--decision", args.decision),
            "decision_rationale": require_non_empty("--decision-rationale", args.decision_rationale),
        }
    )

    if args.decision not in ["approved", "rejected", "deferred"]:
        raise SystemExit("ERROR: --decision must be one of approved|rejected|deferred")

    if args.promotion_target:
        packet["promotion_targets"] = uniq(args.promotion_target)
    if args.condition:
        packet["conditions"] = uniq(args.condition)

    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "audit_ref",
            "promotion_key",
            "decision",
            "decision_rationale",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    return with_metadata(
        packet,
        authority="promoted",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_invariant_draft(args: argparse.Namespace) -> dict[str, Any]:
    identity_seed = {
        "iteration_index": args.iteration_index,
        "invariant_text": args.invariant_text.strip(),
        "invariant_class": args.invariant_class.strip(),
    }
    packet = base_envelope(args, "InvariantDraft", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "iteration_index": args.iteration_index,
            "invariant_text": require_non_empty("--invariant-text", args.invariant_text),
            "invariant_class": args.invariant_class.strip(),
            "bridge_claim": require_non_empty("--bridge-claim", args.bridge_claim),
            "novelty_defense_summary": require_non_empty("--novelty-defense-summary", args.novelty_defense_summary),
            "formal_projection_summary": require_non_empty("--formal-projection-summary", args.formal_projection_summary),
            "repo_anchor_summary": require_non_empty("--repo-anchor-summary", args.repo_anchor_summary),
            "confidence": args.confidence,
            "stability_score": args.stability_score,
        }
    )
    return with_metadata(
        packet,
        authority="semantic",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
    )


def parse_symbol_map(items: list[str]) -> dict[str, str]:
    out: dict[str, str] = {}
    for item in items:
        if "=" not in item:
            raise SystemExit(f"ERROR: --symbol-map entries must be FOREIGN=LEAN, got: {item}")
        left, right = item.split("=", 1)
        left = left.strip()
        right = right.strip()
        if not left or not right:
            raise SystemExit(f"ERROR: --symbol-map entries must have non-empty sides: {item}")
        out[left] = right
    return out


def build_external_theorem_candidate(args: argparse.Namespace) -> dict[str, Any]:
    imports = uniq(args.lean_import_candidate or [])
    target_modules = uniq(args.lean_target_module_candidate or [])
    required_gates = uniq(args.required_gate or [])
    query_terms = uniq(args.query_term or [])
    source_refs = [parse_ref_spec(x) for x in (args.source_ref or [])]
    symbol_map = parse_symbol_map(args.symbol_map or [])
    if not imports:
        raise SystemExit("ERROR: at least one --lean-import-candidate is required")
    if not symbol_map:
        raise SystemExit("ERROR: at least one --symbol-map FOREIGN=LEAN is required")
    if not {"lean_checked", "build_checked", "audit_checked"}.issubset(set(required_gates)):
        raise SystemExit("ERROR: --required-gate must include lean_checked, build_checked, audit_checked")

    identity_seed = {
        "source_system": args.source_system.strip(),
        "source_library": args.source_library.strip(),
        "source_module": args.source_module.strip(),
        "source_decl": args.source_decl.strip(),
        "normalized_statement": args.normalized_statement.strip(),
        "lean_target_namespace": args.lean_target_namespace.strip(),
    }
    packet = base_envelope(args, "ExternalTheoremCandidatePacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "source_system": require_non_empty("--source-system", args.source_system),
            "source_library": require_non_empty("--source-library", args.source_library),
            "source_module": require_non_empty("--source-module", args.source_module),
            "source_decl": require_non_empty("--source-decl", args.source_decl),
            "source_url": args.source_url.strip(),
            "source_path": args.source_path.strip(),
            "source_line_start": args.source_line_start,
            "source_line_end": args.source_line_end,
            "source_statement_raw": require_non_empty("--source-statement-raw", args.source_statement_raw),
            "normalized_statement": require_non_empty("--normalized-statement", args.normalized_statement),
            "lean_target_namespace": require_non_empty("--lean-target-namespace", args.lean_target_namespace),
            "lean_candidate_statement": args.lean_candidate_statement.strip(),
            "lean_import_candidates": imports,
            "lean_target_module_candidates": target_modules,
            "symbol_map": symbol_map,
            "proof_transport_mode": args.proof_transport_mode.strip(),
            "translation_status": args.translation_status.strip(),
            "external_proof_object_ref": args.external_proof_object_ref.strip(),
            "correspondence_notes": args.correspondence_notes.strip(),
            "operator_gap_id": args.operator_gap_id.strip(),
            "query_terms": query_terms,
            "source_refs": source_refs,
            "required_gates": required_gates,
        }
    )
    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "source_system",
            "source_library",
            "source_module",
            "source_decl",
            "normalized_statement",
            "lean_target_namespace",
            "lean_import_candidates",
            "symbol_map",
            "proof_transport_mode",
            "translation_status",
            "required_gates",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    for optional_key in [
        "source_url",
        "source_path",
        "lean_candidate_statement",
        "external_proof_object_ref",
        "correspondence_notes",
        "operator_gap_id",
    ]:
        if not packet[optional_key]:
            packet.pop(optional_key)
    if not packet["source_line_start"]:
        packet.pop("source_line_start")
    if not packet["source_line_end"]:
        packet.pop("source_line_end")
    if not packet["lean_target_module_candidates"]:
        packet.pop("lean_target_module_candidates")
    if not packet["query_terms"]:
        packet.pop("query_terms")
    if not packet["source_refs"]:
        packet.pop("source_refs")
    return with_metadata(
        packet,
        authority="proposal",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_theorem_candidate(args: argparse.Namespace) -> dict[str, Any]:
    symbolic_origin_refs = [parse_ref_spec(x) for x in (args.symbolic_origin_ref or [])]
    invariant_refs = [parse_ref_spec(x) for x in (args.invariant_ref or [])]
    combined_origin_refs = invariant_refs + symbolic_origin_refs
    repo_anchor_refs = [parse_ref_spec(x) for x in (args.repo_anchor_ref or [])]
    candidate_dependencies = uniq(args.candidate_dependency or [])
    if not combined_origin_refs:
        raise SystemExit("ERROR: at least one --invariant-ref or --symbolic-origin-ref is required")
    if not repo_anchor_refs:
        raise SystemExit("ERROR: at least one --repo-anchor-ref is required")
    if not candidate_dependencies:
        raise SystemExit("ERROR: at least one --candidate-dependency is required")

    formal_target = {
        "target_kind": require_non_empty("--formal-target-kind", args.formal_target_kind),
        "summary": require_non_empty("--formal-target-summary", args.formal_target_summary),
    }
    if args.formal_target_shape.strip():
        formal_target["candidate_shape"] = args.formal_target_shape.strip()

    novelty_defense = {"summary": require_non_empty("--novelty-summary", args.novelty_summary)}
    if args.duplication_assessment.strip():
        novelty_defense["duplication_assessment"] = args.duplication_assessment.strip()
    if args.pressure_point:
        novelty_defense["pressure_points"] = uniq(args.pressure_point)

    identity_seed = {
        "formal_target": formal_target,
        "bridge_claim": args.bridge_claim.strip(),
        "origins": combined_origin_refs,
    }
    packet = base_envelope(args, "TheoremCandidatePacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "symbolic_origin_refs": combined_origin_refs,
            "invariant_refs": invariant_refs,
            "formal_target": formal_target,
            "bridge_claim": require_non_empty("--bridge-claim", args.bridge_claim),
            "novelty_defense": novelty_defense,
            "repo_anchor_refs": repo_anchor_refs,
            "candidate_dependencies": candidate_dependencies,
            "admissibility_state": args.admissibility_state.strip(),
            "cost_class": args.cost_class.strip(),
            "anchor_completeness": args.anchor_completeness.strip(),
            "target_namespace_candidates": uniq(args.target_namespace_candidate or []),
            "target_module_candidates": uniq(args.target_module_candidate or []),
        }
    )
    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "symbolic_origin_refs",
            "formal_target",
            "bridge_claim",
            "novelty_defense",
            "repo_anchor_refs",
            "candidate_dependencies",
            "admissibility_state",
            "cost_class",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    if not packet["anchor_completeness"]:
        packet.pop("anchor_completeness")
    if not packet["target_namespace_candidates"]:
        packet.pop("target_namespace_candidates")
    if not packet["target_module_candidates"]:
        packet.pop("target_module_candidates")
    if not packet["invariant_refs"]:
        packet.pop("invariant_refs")
    return with_metadata(
        packet,
        authority="proposal",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def build_residue(args: argparse.Namespace) -> dict[str, Any]:
    failure_refs = [parse_ref_spec(x) for x in (args.failure_ref or [])]
    if not failure_refs:
        raise SystemExit("ERROR: at least one --failure-ref is required")
    identity_seed = {
        "failure_refs": failure_refs,
        "failure_class": args.failure_class.strip(),
        "stage": args.stage.strip(),
    }
    packet = base_envelope(args, "ResiduePacket", args.status, identity_seed=identity_seed)
    packet.update(
        {
            "packet_version": args.packet_version.strip(),
            "failure_refs": failure_refs,
            "failure_class": args.failure_class.strip(),
            "stage": args.stage.strip(),
            "recovery_hint": require_non_empty("--recovery-hint", args.recovery_hint),
            "return_route": require_non_empty("--return-route", args.return_route),
            "recoverability": args.recoverability.strip(),
            "next_cultivation_hint": args.next_cultivation_hint.strip(),
            "blocked_packet_refs": [parse_ref_spec(x) for x in (args.blocked_packet_ref or [])],
            "anchor_gap_summary": args.anchor_gap_summary.strip(),
        }
    )
    packet_hash_material = {
        k: packet[k]
        for k in [
            "kind",
            "lineage_id",
            "failure_refs",
            "failure_class",
            "stage",
            "recovery_hint",
            "return_route",
        ]
    }
    packet["packet_hash"] = args.packet_hash.strip() or f"sha256:{stable_digest(packet_hash_material, size=32)}"
    if not packet["next_cultivation_hint"]:
        packet.pop("next_cultivation_hint")
    if not packet["blocked_packet_refs"]:
        packet.pop("blocked_packet_refs")
    if not packet["anchor_gap_summary"]:
        packet.pop("anchor_gap_summary")
    return with_metadata(
        packet,
        authority="proposal",
        representation_class=args.representation_class,
        representation_depth=args.representation_depth if len(args.representation_depth) > 1 else args.representation_depth[0],
        promotion_allowed=False,
    )


def maybe_validate(packet: dict[str, Any], *, enabled: bool) -> list[str]:
    if not enabled:
        return []
    schema_path = SCHEMA_BY_KIND.get(packet["kind"])
    if schema_path is None:
        return [f"no schema registered for kind: {packet['kind']}"]
    return validate_packet(packet, schema_path, build_store())


def cmd_build(args: argparse.Namespace) -> int:
    if args.cmd == "build-symbolic-seed":
        packet = build_symbolic_seed(args)
    elif args.cmd == "build-formulation-variant":
        packet = build_formulation_variant(args)
    elif args.cmd == "build-resonance-cluster":
        packet = build_resonance_cluster(args)
    elif args.cmd == "build-pauli-critique":
        packet = build_pauli_critique(args)
    elif args.cmd == "build-invariant-draft":
        packet = build_invariant_draft(args)
    elif args.cmd == "build-translation-packet":
        packet = build_translation_packet(args)
    elif args.cmd == "build-retrieval-hypothesis-packet":
        packet = build_retrieval_hypothesis_packet(args)
    elif args.cmd == "build-execution-intent-packet":
        packet = build_execution_intent_packet(args)
    elif args.cmd == "build-lean-verification-packet":
        packet = build_lean_verification_packet(args)
    elif args.cmd == "build-build-packet":
        packet = build_build_packet(args)
    elif args.cmd == "build-audit-packet":
        packet = build_audit_packet(args)
    elif args.cmd == "build-promotion-decision-packet":
        packet = build_promotion_decision_packet(args)
    elif args.cmd == "build-theorem-candidate":
        packet = build_theorem_candidate(args)
    elif args.cmd == "build-external-theorem-candidate":
        packet = build_external_theorem_candidate(args)
    elif args.cmd == "build-residue":
        packet = build_residue(args)
    else:
        print(f"ERROR: unsupported command: {args.cmd}", file=sys.stderr)
        return 2

    errors = maybe_validate(packet, enabled=args.validate)
    if errors:
        print("ERROR: built Hive packet failed schema validation:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 3

    out = Path(args.out)
    write_json(out, packet)
    print(f"hive packet written: {out}")
    return 0


def add_common_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--out", required=True, help="Output JSON path.")
    p.add_argument("--id", default="", help="Optional explicit id. Default is deterministic.")
    p.add_argument("--lineage-id", required=True, help="Lineage id.")
    p.add_argument("--revision", type=int, default=1, help="Revision number. Default: 1.")
    p.add_argument("--origin-run-id", default="", help="Optional explicit origin run id.")
    p.add_argument("--created-at", default="", help="Optional explicit created_at timestamp.")
    p.add_argument("--updated-at", default="", help="Optional explicit updated_at timestamp.")
    p.add_argument("--created-by-agent", default="mother-bee", help="Creator id.")
    p.add_argument("--agent-role", default="orchestrator", help="Agent role.")
    p.add_argument("--backend", default="local", help="Backend label.")
    p.add_argument("--task-id", default="", help="Optional task id.")
    p.add_argument("--session-key", default="", help="Optional session key.")
    p.add_argument("--tag", action="append", default=[], help="Repeatable tag.")
    p.add_argument("--notes", default="", help="Optional notes.")
    p.add_argument("--parent-ref", action="append", default=[], help="Repeatable parent ref spec: ref|kind|role|confidence")
    p.add_argument("--evidence-ref", action="append", default=[], help="Repeatable evidence ref spec: ref|kind|role|confidence")
    p.add_argument("--source-hash", action="append", default=[], help="Repeatable source hash.")
    p.add_argument("--representation-class", default="owner", choices=["owner", "translator", "coherence", "capstone", "shadow"], help="Representation class.")
    p.add_argument("--representation-depth", action="append", required=True, choices=["scalar", "finite_matrix", "projective", "hilbert", "operatorial", "krein", "von_neumann", "type_iii", "categorical"], help="Repeatable representation depth (at least one).")
    p.add_argument("--validate", action="store_true", help="Validate the built packet against the machine-readable schema before writing.")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    s = sp.add_parser("build-symbolic-seed", help="Build SymbolicSeed packet.")
    add_common_args(s)
    s.add_argument("--status", default="active", choices=["draft", "active", "stabilized", "translated", "formalized", "retired", "archived"])
    s.add_argument("--seed-hash", default="", help="Optional explicit seed hash.")
    s.add_argument("--source-class", required=True, choices=["black_book_fragment", "dialogue_fragment", "dag_anomaly", "audit_objection", "operator_prompt", "alexandria_extract", "residue_return"])
    s.add_argument("--source-ref", required=True)
    s.add_argument("--source-excerpt", required=True)
    s.add_argument("--source-path", default="")
    s.add_argument("--source-section", default="")
    s.add_argument("--source-line-start", type=int, default=0)
    s.add_argument("--source-line-end", type=int, default=0)
    s.add_argument("--content-text", required=True)
    s.add_argument("--pressure-class", required=True, choices=["definition_pressure", "theorem_pressure", "bridge_pressure", "obstruction_pressure", "audit_pressure", "graph_pressure"])

    v = sp.add_parser("build-formulation-variant", help="Build FormulationVariant packet.")
    add_common_args(v)
    v.add_argument("--status", default="active", choices=["draft", "active", "stabilized", "translated", "formalized", "retired", "archived"])
    v.add_argument("--seed-hash", required=True)
    v.add_argument("--variant-index", required=True, type=int)
    v.add_argument("--iteration-index", required=True, type=int)
    v.add_argument("--jung-pass-id", required=True)
    v.add_argument("--representation-mode", required=True, choices=["geometric", "categorical", "operatorial", "lean_facing", "thermodynamic", "semantic_bridge", "namespace_shaping"])
    v.add_argument("--content-text", required=True)
    v.add_argument("--summary", required=True)
    v.add_argument("--temperature-profile", required=True)
    v.add_argument("--confidence", required=True, type=float)
    v.add_argument("--formal-projection-score", required=True, type=float)

    c = sp.add_parser("build-resonance-cluster", help="Build ResonanceCluster packet.")
    add_common_args(c)
    c.add_argument("--status", default="active", choices=["draft", "active", "stabilized", "translated", "formalized", "retired", "archived"])
    c.add_argument("--cluster-method", required=True)
    c.add_argument("--cluster-signature", required=True)
    c.add_argument("--member-count", required=True, type=int)
    c.add_argument("--invariant-hypothesis", required=True)
    c.add_argument("--distinguishing-axis", action="append", default=[])

    pcrit = sp.add_parser("build-pauli-critique", help="Build PauliCritique packet.")
    add_common_args(pcrit)
    pcrit.add_argument("--status", default="active", choices=["draft", "active", "stabilized", "translated", "formalized", "retired", "archived"])
    pcrit.add_argument("--iteration-index", required=True, type=int)
    pcrit.add_argument("--critique-mode", required=True, choices=["branch_separation", "novelty_defense", "duplication_collapse", "formal_projection_pressure", "repo_anchor_pressure", "architecture_legality"])
    pcrit.add_argument("--variant-ref", action="append", default=[], help="Repeatable target ref spec: ref|kind|role|confidence")
    pcrit.add_argument("--cluster-ref", action="append", default=[], help="Repeatable target ref spec: ref|kind|role|confidence")
    pcrit.add_argument("--invariant-ref", action="append", default=[], help="Repeatable target ref spec: ref|kind|role|confidence")
    pcrit.add_argument("--critique-text", required=True)
    pcrit.add_argument("--novelty-assessment", required=True)
    pcrit.add_argument("--duplication-assessment", required=True)
    pcrit.add_argument("--formal-target-assessment", required=True)
    pcrit.add_argument("--repo-anchor-assessment", required=True)
    pcrit.add_argument("--admissibility-state", default="needs_anchor", choices=["unknown", "emergent", "plausible", "needs_anchor", "needs_translation", "inadmissible", "admissible_for_probe", "admissible_for_build"])
    pcrit.add_argument("--cost-class", default="medium", choices=["low", "medium", "high", "very_high", "unknown"])

    tp = sp.add_parser("build-translation-packet", help="Build TranslationPacket.")
    add_common_args(tp)
    tp.add_argument("--status", default="probe_ready", choices=["draft", "legalized", "probe_ready", "gated", "executed", "accepted", "rejected", "deferred"])
    tp.add_argument("--packet-version", default="1.0.0")
    tp.add_argument("--packet-hash", default="")
    tp.add_argument("--invariant-ref", action="append", default=[], help="Repeatable invariant ref spec: ref|kind|role|confidence")
    tp.add_argument("--namespace-candidate", required=True)
    tp.add_argument("--signature-candidate", action="append", default=[])
    tp.add_argument("--module-candidate", required=True)
    tp.add_argument("--import-candidate", action="append", default=[])
    tp.add_argument("--probe-kind", required=True)
    tp.add_argument("--probe-step", action="append", default=[])
    tp.add_argument("--declaration-name-candidate", action="append", default=[])
    tp.add_argument("--dependency-candidate", action="append", default=[])
    tp.add_argument("--target-surface", default="")
    tp.add_argument("--anchor-ref", action="append", default=[], help="Repeatable anchor ref spec: ref|kind|role|confidence")

    rh = sp.add_parser("build-retrieval-hypothesis-packet", help="Build RetrievalHypothesisPacket.")
    add_common_args(rh)
    rh.add_argument("--status", default="legalized", choices=["draft", "legalized", "probe_ready", "gated", "executed", "accepted", "rejected", "deferred"])
    rh.add_argument("--packet-version", default="1.0.0")
    rh.add_argument("--packet-hash", default="")
    rh.add_argument("--query-text", required=True)
    rh.add_argument("--seed-ref", action="append", default=[], help="Repeatable seed ref spec: ref|kind|role|confidence")
    rh.add_argument("--candidate-anchor-ref", action="append", default=[], help="Repeatable anchor ref spec: ref|kind|role|confidence")
    rh.add_argument("--graph-mode", required=True, choices=["retrieval_projection", "scc_overlay", "raw_descent", "mixed"])
    rh.add_argument("--retrieval-summary", required=True)

    ei = sp.add_parser("build-execution-intent-packet", help="Build ExecutionIntentPacket.")
    add_common_args(ei)
    ei.add_argument("--status", default="gated", choices=["draft", "legalized", "probe_ready", "gated", "executed", "accepted", "rejected", "deferred"])
    ei.add_argument("--packet-version", default="1.0.0")
    ei.add_argument("--packet-hash", default="")
    ei.add_argument("--target-ref", action="append", default=[], help="Repeatable target ref spec: ref|kind|role|confidence")
    ei.add_argument("--intended-action", action="append", default=[])
    ei.add_argument("--required-tool", action="append", default=[])
    ei.add_argument("--required-gate", action="append", default=[])
    ei.add_argument("--mutation-scope", required=True, choices=["none", "probe_only", "single_file", "single_module", "bounded_repo_surface"])
    ei.add_argument("--execution-allowed", action="store_true", help="Set execution_allowed=true. Default false.")

    lv = sp.add_parser("build-lean-verification-packet", help="Build LeanVerificationPacket.")
    add_common_args(lv)
    lv.add_argument("--status", default="gated", choices=["draft", "legalized", "probe_ready", "gated", "executed", "accepted", "rejected", "deferred"])
    lv.add_argument("--packet-version", default="1.0.0")
    lv.add_argument("--packet-hash", default="")
    lv.add_argument("--execution-intent-ref", action="append", default=[])
    lv.add_argument("--execution-allowed", action="store_true", help="Set execution_allowed=true.")
    lv.add_argument("--verification-key", required=True)
    lv.add_argument("--verification-outcome", required=True)
    lv.add_argument("--kernel-summary", required=True)
    lv.add_argument("--proof-status", default="pending", choices=["pending", "verified", "blocked", "rejected"])
    lv.add_argument("--proof-code", default="")
    lv.add_argument("--lean-output", default="")
    lv.add_argument("--error-excerpt", default="")

    bp = sp.add_parser("build-build-packet", help="Build BuildPacket.")
    add_common_args(bp)
    bp.add_argument("--status", default="gated", choices=["deferred", "gated", "executed", "failed", "passed", "rejected"])
    bp.add_argument("--packet-version", default="1.0.0")
    bp.add_argument("--packet-hash", default="")
    bp.add_argument("--lean-verification-ref", action="append", default=[])
    bp.add_argument("--build-key", required=True)
    bp.add_argument("--build-command", required=True)
    bp.add_argument("--build-success", action="store_true", help="Set build_success=true")
    bp.add_argument("--build-exit-code", type=int, default=0)
    bp.add_argument("--build-output-excerpt", default="")
    bp.add_argument("--build-artifact", action="append", default=[])

    ap = sp.add_parser("build-audit-packet", help="Build AuditPacket.")
    add_common_args(ap)
    ap.add_argument("--status", default="in_progress", choices=["deferred", "gated", "in_progress", "approved", "rejected", "needs_retry"])
    ap.add_argument("--packet-version", default="1.0.0")
    ap.add_argument("--packet-hash", default="")
    ap.add_argument("--build-ref", action="append", default=[])
    ap.add_argument("--audit-key", required=True)
    ap.add_argument("--audit-scope", default="correctness", choices=["correctness", "safety", "build", "promotion"])
    ap.add_argument("--audit-finding", action="append", default=[])
    ap.add_argument("--audit-outcome", required=True, choices=["approved", "rejected", "deferred"])
    ap.add_argument("--evidence-summary", required=True)

    pd = sp.add_parser("build-promotion-decision-packet", help="Build PromotionDecisionPacket.")
    add_common_args(pd)
    pd.add_argument("--status", default="deferred", choices=["deferred", "rejected", "approved", "promoted"])
    pd.add_argument("--packet-version", default="1.0.0")
    pd.add_argument("--packet-hash", default="")
    pd.add_argument("--audit-ref", action="append", default=[])
    pd.add_argument("--promotion-key", required=True)
    pd.add_argument("--decision", required=True, choices=["approved", "deferred", "rejected"])
    pd.add_argument("--decision-rationale", required=True)
    pd.add_argument("--promotion-target", action="append", default=[])
    pd.add_argument("--condition", action="append", default=[])

    i = sp.add_parser("build-invariant-draft", help="Build InvariantDraft packet.")
    add_common_args(i)
    i.add_argument("--status", default="stabilized", choices=["draft", "active", "stabilized", "translated", "formalized", "retired", "archived"])
    i.add_argument("--iteration-index", required=True, type=int)
    i.add_argument("--invariant-text", required=True)
    i.add_argument("--invariant-class", required=True, choices=["theorem_shape", "definition_need", "bridge_relation", "lemma_family", "obstruction_pattern"])
    i.add_argument("--bridge-claim", required=True)
    i.add_argument("--novelty-defense-summary", required=True)
    i.add_argument("--formal-projection-summary", required=True)
    i.add_argument("--repo-anchor-summary", required=True)
    i.add_argument("--confidence", required=True, type=float)
    i.add_argument("--stability-score", required=True, type=float)

    t = sp.add_parser("build-theorem-candidate", help="Build TheoremCandidatePacket.")
    add_common_args(t)
    t.add_argument("--status", default="legalized", choices=["draft", "legalized", "probe_ready", "gated", "executed", "accepted", "rejected", "deferred"])
    t.add_argument("--packet-version", default="1.0.0")
    t.add_argument("--packet-hash", default="")
    t.add_argument("--invariant-ref", action="append", default=[], help="Repeatable preferred origin ref spec: ref|kind|role|confidence")
    t.add_argument("--symbolic-origin-ref", action="append", default=[], help="Repeatable additional origin ref spec: ref|kind|role|confidence")
    t.add_argument("--formal-target-kind", default="theorem_family")
    t.add_argument("--formal-target-summary", required=True)
    t.add_argument("--formal-target-shape", default="")
    t.add_argument("--bridge-claim", required=True)
    t.add_argument("--novelty-summary", required=True)
    t.add_argument("--duplication-assessment", default="")
    t.add_argument("--pressure-point", action="append", default=[])
    t.add_argument("--repo-anchor-ref", action="append", default=[], help="Repeatable ref spec: ref|kind|role|confidence")
    t.add_argument("--candidate-dependency", action="append", default=[])
    t.add_argument("--admissibility-state", default="admissible_for_probe", choices=["unknown", "emergent", "plausible", "needs_anchor", "needs_translation", "inadmissible", "admissible_for_probe", "admissible_for_build"])
    t.add_argument("--cost-class", default="medium", choices=["low", "medium", "high", "very_high", "unknown"])
    t.add_argument("--anchor-completeness", default="")
    t.add_argument("--target-namespace-candidate", action="append", default=[])
    t.add_argument("--target-module-candidate", action="append", default=[])

    et = sp.add_parser("build-external-theorem-candidate", help="Build ExternalTheoremCandidatePacket.")
    add_common_args(et)
    et.add_argument("--status", default="discovered", choices=["draft", "discovered", "normalized", "matched_to_mathlib", "requires_adapter", "missing_in_lean", "rejected", "deferred"])
    et.add_argument("--packet-version", default="1.0.0")
    et.add_argument("--packet-hash", default="")
    et.add_argument("--source-system", required=True, choices=["Isabelle/HOL", "Lean/mathlib", "Dedukti", "Logipedia", "Coq", "HOL-Light", "Agda", "arXiv", "local_lean_failure_memory", "local_hive_packet_memory", "other"])
    et.add_argument("--source-library", required=True)
    et.add_argument("--source-module", required=True)
    et.add_argument("--source-decl", required=True)
    et.add_argument("--source-url", default="")
    et.add_argument("--source-path", default="")
    et.add_argument("--source-line-start", type=int, default=0)
    et.add_argument("--source-line-end", type=int, default=0)
    et.add_argument("--source-statement-raw", required=True)
    et.add_argument("--normalized-statement", required=True)
    et.add_argument("--lean-target-namespace", required=True)
    et.add_argument("--lean-candidate-statement", default="")
    et.add_argument("--lean-import-candidate", action="append", default=[])
    et.add_argument("--lean-target-module-candidate", action="append", default=[])
    et.add_argument("--symbol-map", action="append", default=[], help="Repeatable FOREIGN=LEAN symbol correspondence")
    et.add_argument("--proof-transport-mode", default="adapter", choices=["name_match", "adapter", "dedukti", "proof_sketch", "manual", "research_guidance"])
    et.add_argument("--translation-status", default="unclassified", choices=["unclassified", "matched_to_mathlib", "requires_adapter", "missing_in_lean", "rejected", "deferred"])
    et.add_argument("--external-proof-object-ref", default="")
    et.add_argument("--correspondence-notes", default="")
    et.add_argument("--operator-gap-id", default="")
    et.add_argument("--query-term", action="append", default=[])
    et.add_argument("--source-ref", action="append", default=[], help="Repeatable source ref spec: ref|kind|role|confidence")
    et.add_argument("--required-gate", action="append", default=["lean_checked", "build_checked", "audit_checked"], choices=["lean_checked", "build_checked", "audit_checked", "promotion_decision"])

    r = sp.add_parser("build-residue", help="Build ResiduePacket.")
    add_common_args(r)
    r.add_argument("--status", default="active", choices=["active", "recycled", "closed", "archived"])
    r.add_argument("--packet-version", default="1.0.0")
    r.add_argument("--packet-hash", default="")
    r.add_argument("--failure-ref", action="append", default=[], help="Repeatable ref spec: ref|kind|role|confidence")
    r.add_argument("--failure-class", required=True, choices=["symbolic_overheat", "formal_target_missing", "repo_anchor_missing", "novelty_collapse", "proof_obstruction", "translation_failure", "architecture_illegality", "transport_failure", "build_failure", "audit_rejection", "merge_instability"])
    r.add_argument("--stage", required=True, choices=["seed_intake", "jung_excitation", "resonance_clustering", "pauli_differentiation", "invariant_extraction", "packet_legalization", "translation", "formal_probe", "build", "audit", "promotion"])
    r.add_argument("--recovery-hint", required=True)
    r.add_argument("--return-route", default="return_to_residue")
    r.add_argument("--recoverability", default="unknown", choices=["high", "medium", "low", "unknown"])
    r.add_argument("--next-cultivation-hint", default="")
    r.add_argument("--blocked-packet-ref", action="append", default=[], help="Repeatable ref spec: ref|kind|role|confidence")
    r.add_argument("--anchor-gap-summary", default="")

    return p.parse_args()


def main() -> None:
    args = parse_args()
    raise SystemExit(cmd_build(args))


if __name__ == "__main__":
    main()
