#!/usr/bin/env python3
"""Emit one real Hive packet chain from a bounded Hermes planning cycle."""
from __future__ import annotations

import json
from argparse import Namespace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from tools.infra.hive_packet_build import (
    build_execution_intent_packet,
    build_formulation_variant,
    build_invariant_draft,
    build_pauli_critique,
    build_resonance_cluster,
    build_retrieval_hypothesis_packet,
    build_symbolic_seed,
    build_theorem_candidate,
    build_translation_packet,
    write_json,
)
from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

PACKET_CHAIN_DIRNAME = "packet_chain"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _ns(**kwargs: Any) -> Namespace:
    defaults = dict(
        out="",
        id="",
        lineage_id="",
        revision=1,
        origin_run_id="",
        created_at="",
        updated_at="",
        created_by_agent="hermes-bounded-runner",
        agent_role="orchestrator",
        backend="local",
        task_id="",
        session_key="",
        tag=[],
        notes="",
        parent_ref=[],
        evidence_ref=[],
        source_hash=[],
        representation_class="translator",
        representation_depth=["categorical"],
        validate=False,
        execution_allowed=False,
        status="draft",
        seed_hash="",
        source_path="",
        source_section="",
        source_line_start=0,
        source_line_end=0,
        packet_version="1.0.0",
        packet_hash="",
        target_surface="",
        declaration_name_candidate=[],
        dependency_candidate=[],
        anchor_ref=[],
        import_candidate=[],
        signature_candidate=[],
        probe_kind="",
        probe_step=[],
        candidate_anchor_ref=[],
        query_text="",
        retrieval_summary="",
        graph_mode="mixed",
        intended_action=[],
        required_tool=[],
        required_gate=[],
        mutation_scope="none",
        invariant_ref=[],
        variant_ref=[],
        cluster_ref=[],
        repo_anchor_ref=[],
        candidate_dependency=[],
        pressure_point=[],
        symbolic_origin_ref=[],
        anchor_completeness="",
        target_namespace_candidate=[],
        target_module_candidate=[],
        formal_target_kind="theorem_family",
        formal_target_summary="",
        formal_target_shape="",
        bridge_claim="",
        novelty_summary="",
        duplication_assessment="",
        admissibility_state="admissible_for_probe",
        cost_class="medium",
    )
    defaults.update(kwargs)
    return Namespace(**defaults)


def _ensure_valid(packet: dict[str, Any]) -> None:
    schema_path = SCHEMA_BY_KIND.get(packet["kind"])
    if schema_path is None:
        raise RuntimeError(f"no schema registered for kind: {packet['kind']}")
    errors = validate_packet(packet, schema_path, build_store())
    if errors:
        raise RuntimeError(f"invalid emitted {packet['kind']}: " + "; ".join(errors))


def _route_fields(planner_text: str) -> dict[str, str]:
    out = {"route": "", "execution_allowed": "", "next_action": "", "rationale": "", "guards": ""}
    current = None
    for raw in planner_text.splitlines():
        line = raw.strip()
        for label in ["ROUTE", "EXECUTION_ALLOWED", "NEXT_ACTION", "RATIONALE", "GUARDS"]:
            prefix = label + ":"
            if line.startswith(prefix):
                key = label.lower()
                out[key] = line[len(prefix):].strip()
                current = key
                break
        else:
            if current and line:
                out[current] = (out[current] + " " + line).strip()
    return out


def _seed_excerpt(packet_data: dict[str, Any]) -> str:
    evidence = packet_data.get("evidence") or []
    if evidence and isinstance(evidence, list):
        first = evidence[0]
        if isinstance(first, dict):
            claim = str(first.get("claim") or "").strip()
            if claim:
                return claim
    return str(packet_data.get("research_goal") or "bounded-planner-seed")


def emit_packet_chain(*, packet: dict[str, Any], packet_path: str, planner_text: str, gravity_context: dict[str, Any] | None, query: str, run_id: str, output_root: Path) -> dict[str, str]:
    route = _route_fields(planner_text)
    packet_id = str(packet.get("packet_id") or Path(packet_path).stem)
    lineage_id = f"lineage_{packet_id}"
    chain_dir = output_root / PACKET_CHAIN_DIRNAME / run_id
    chain_dir.mkdir(parents=True, exist_ok=True)

    base_tags = ["bounded-runner", "packet-chain", route.get("route", "hold") or "hold"]
    now = utc_now()

    seed = build_symbolic_seed(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="owner",
            representation_depth=["operatorial", "categorical"],
            tag=base_tags,
            notes=f"source_packet={packet_id}",
            source_class="operator_prompt",
            source_ref=packet_path,
            source_excerpt=_seed_excerpt(packet),
            source_path=packet_path,
            source_section="research_packet",
            content_text=str(packet.get("research_goal") or packet_id),
            pressure_class="theorem_pressure",
        )
    )
    _ensure_valid(seed)
    write_json(chain_dir / "01_symbolic_seed.json", seed)

    variant = build_formulation_variant(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="translator",
            representation_depth=["lean_facing", "categorical"] if False else ["categorical"],
            tag=base_tags,
            parent_ref=[f"{seed['id']}|SymbolicSeed|seed_origin|0.95"],
            source_hash=[seed["seed_hash"]],
            seed_hash=seed["seed_hash"],
            variant_index=1,
            iteration_index=1,
            jung_pass_id=f"jungpass_{packet_id}_1",
            representation_mode="lean_facing",
            content_text=route.get("next_action") or planner_text.strip() or str(packet.get("research_goal") or packet_id),
            summary=route.get("rationale") or "Bounded planner reformulation.",
            temperature_profile="bounded",
            confidence=0.6,
            formal_projection_score=0.7,
        )
    )
    _ensure_valid(variant)
    write_json(chain_dir / "02_formulation_variant.json", variant)

    cluster = build_resonance_cluster(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="coherence",
            representation_depth=["categorical"],
            tag=base_tags,
            parent_ref=[f"{variant['id']}|FormulationVariant|variant_origin|0.9"],
            cluster_method="bounded_single_pass_overlap",
            cluster_signature=route.get("route") or "hold",
            member_count=1,
            invariant_hypothesis=route.get("rationale") or route.get("next_action") or "Bounded planner output suggests a stable admissibility-facing motif.",
            distinguishing_axis=["route_choice", "graph_context_presence"],
        )
    )
    _ensure_valid(cluster)
    write_json(chain_dir / "03_resonance_cluster.json", cluster)

    critique = build_pauli_critique(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="coherence",
            representation_depth=["categorical"],
            tag=base_tags,
            cluster_ref=[f"{cluster['id']}|ResonanceCluster|target_cluster|0.85"],
            variant_ref=[f"{variant['id']}|FormulationVariant|target_variant|0.8"],
            iteration_index=1,
            critique_mode="repo_anchor_pressure" if gravity_context else "formal_projection_pressure",
            critique_text=(
                "The bounded planner output is useful, but it remains non-authoritative until translated, graph-grounded, and gated."
            ),
            novelty_assessment="bounded_runner_semantic_signal",
            duplication_assessment="single_pass_unconfirmed",
            formal_target_assessment="coherent_but_pre_authority",
            repo_anchor_assessment="candidate_anchor_available" if (gravity_context or {}).get("items") else "anchor_pending",
            admissibility_state="admissible_for_probe" if (gravity_context or {}).get("items") else "needs_anchor",
            cost_class="low",
        )
    )
    _ensure_valid(critique)
    write_json(chain_dir / "04_pauli_critique.json", critique)

    invariant = build_invariant_draft(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="coherence",
            representation_depth=["categorical"],
            tag=base_tags,
            parent_ref=[f"{critique['id']}|PauliCritique|critique_origin|0.9", f"{cluster['id']}|ResonanceCluster|cluster_origin|0.85"],
            iteration_index=1,
            invariant_text=route.get("rationale") or route.get("next_action") or "Bounded invariant awaiting refinement.",
            invariant_class="theorem_shape",
            bridge_claim=route.get("next_action") or "Bounded route suggests a theorem-facing invariant.",
            novelty_defense_summary="Derived from graph-grounded bounded planning output.",
            formal_projection_summary=f"Route={route.get('route') or 'hold'} with next action grounded by gravitational context.",
            repo_anchor_summary=(gravity_context or {}).get("graph_source") or "No graph source recorded.",
            confidence=0.62,
            stability_score=0.58,
        )
    )
    _ensure_valid(invariant)
    write_json(chain_dir / "05_invariant_draft.json", invariant)

    theorem_candidate = build_theorem_candidate(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="translator",
            representation_depth=["categorical"],
            tag=base_tags,
            invariant_ref=[f"{invariant['id']}|InvariantDraft|primary_invariant|0.88"],
            formal_target_summary=str((packet.get("formalization_targets") or [{}])[0]) if (packet.get("formalization_targets") or []) else "bounded theorem-facing target",
            formal_target_kind="theorem_family",
            bridge_claim=invariant.get("bridge_claim") or route.get("next_action") or "Bounded route suggests a theorem-facing invariant.",
            novelty_summary="Bounded runner legalizes a theorem-facing candidate from the stabilized invariant.",
            duplication_assessment="single_pass_candidate",
            pressure_point=[route.get("route") or "hold", "bounded_runner"],
            repo_anchor_ref=[f"{item.get('id')}|GraphNode|candidate_anchor|0.7" for item in ((gravity_context or {}).get('items') or [])[:2] if item.get('id')] or [f"{cluster['id']}|ResonanceCluster|semantic_anchor|0.5"],
            candidate_dependency=["PacketAuthority", "TranslationPacket", "RetrievalHypothesisPacket"],
            admissibility_state="admissible_for_probe" if (gravity_context or {}).get("items") else "needs_anchor",
            cost_class="low",
            anchor_completeness="partial" if (gravity_context or {}).get("items") else "pending",
        )
    )
    _ensure_valid(theorem_candidate)
    write_json(chain_dir / "06_theorem_candidate_packet.json", theorem_candidate)

    translation = build_translation_packet(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="translator",
            representation_depth=["categorical"],
            tag=base_tags,
            invariant_ref=[f"{invariant['id']}|InvariantDraft|primary_invariant|0.88"],
            namespace_candidate="InfoGeometry.Hive",
            signature_candidate=[str(t) for t in (packet.get("formalization_targets") or [])[:1]] or ["theorem boundedRouteCandidate : Prop"],
            module_candidate="InfoGeometry/Hive/BoundedRoute",
            import_candidate=["InfoGeometry.Hive.PacketAuthority"],
            probe_kind="bounded_planner_translation",
            probe_step=["inspect imports", "inspect target shape", "defer proof execution"],
            declaration_name_candidate=[f"boundedRoute_{packet_id}"],
            dependency_candidate=["PacketAuthority"],
            anchor_ref=[f"{item.get('id')}|GraphNode|candidate_anchor|0.7" for item in ((gravity_context or {}).get('items') or [])[:2] if item.get('id')],
        )
    )
    _ensure_valid(translation)
    write_json(chain_dir / "07_translation_packet.json", translation)

    retrieval = build_retrieval_hypothesis_packet(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="translator",
            representation_depth=["categorical"],
            tag=base_tags,
            query_text=query,
            seed_ref=[f"{seed['id']}|SymbolicSeed|seed|0.95"],
            candidate_anchor_ref=[f"{item.get('id')}|GraphNode|candidate_anchor|0.7" for item in ((gravity_context or {}).get('items') or [])[:4] if item.get('id')],
            graph_mode=(gravity_context or {}).get("graph_mode") or "mixed",
            retrieval_summary=(route.get("rationale") or "Use graph context to ground the next bounded step.")[:500],
        )
    )
    _ensure_valid(retrieval)
    write_json(chain_dir / "08_retrieval_hypothesis_packet.json", retrieval)

    execution_allowed = route.get("execution_allowed", "").lower() == "yes"
    mutation_scope = "probe_only" if execution_allowed else "none"
    execution_intent = build_execution_intent_packet(
        _ns(
            lineage_id=lineage_id,
            origin_run_id=run_id,
            created_at=now,
            updated_at=now,
            representation_class="translator",
            representation_depth=["categorical"],
            tag=base_tags,
            target_ref=[
                f"{theorem_candidate['id']}|TheoremCandidatePacket|candidate_target|0.9",
                f"{translation['id']}|TranslationPacket|translation_target|0.9",
                f"{retrieval['id']}|RetrievalHypothesisPacket|retrieval_target|0.8",
            ],
            intended_action=[route.get("next_action") or "hold for next bounded pass"],
            required_tool=["hive_packet_build.py", "hive_packet_validate.py"],
            required_gate=[g.strip() for g in (route.get("guards") or "LeanVerificationPacket").split(",") if g.strip()] or ["LeanVerificationPacket"],
            mutation_scope=mutation_scope,
            execution_allowed=execution_allowed,
        )
    )
    _ensure_valid(execution_intent)
    write_json(chain_dir / "09_execution_intent_packet.json", execution_intent)

    return {
        "lineage_id": lineage_id,
        "packet_chain_dir": str(chain_dir),
        "symbolic_seed": str(chain_dir / "01_symbolic_seed.json"),
        "formulation_variant": str(chain_dir / "02_formulation_variant.json"),
        "resonance_cluster": str(chain_dir / "03_resonance_cluster.json"),
        "pauli_critique": str(chain_dir / "04_pauli_critique.json"),
        "invariant_draft": str(chain_dir / "05_invariant_draft.json"),
        "theorem_candidate_packet": str(chain_dir / "06_theorem_candidate_packet.json"),
        "translation_packet": str(chain_dir / "07_translation_packet.json"),
        "retrieval_hypothesis_packet": str(chain_dir / "08_retrieval_hypothesis_packet.json"),
        "execution_intent_packet": str(chain_dir / "09_execution_intent_packet.json"),
    }
