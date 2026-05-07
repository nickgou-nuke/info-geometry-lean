from __future__ import annotations

from copy import deepcopy

from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet


BASE = {
    "id": "pkt_demo",
    "status": "draft",
    "lineage_id": "lineage_demo",
    "revision": 1,
    "origin_run_id": "run_demo",
    "created_at": "2026-05-07T00:00:00Z",
    "updated_at": "2026-05-07T00:00:00Z",
}

REPRESENTATION = {
    "representation_class": "shadow",
    "representation_depth": "operatorial",
}


def _errors(packet: dict) -> list[str]:
    store = build_store()
    return validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], store)


def test_source_observation_packet_validates_navigation_sensation() -> None:
    packet = {
        **BASE,
        "id": "src_obs_demo",
        "kind": "SourceObservationPacket",
        "status": "captured",
        "authority": "navigation",
        "authority_origin": "source_observation",
        "epistemic_layer": "raw_source",
        "cognitive_function": "sensation",
        "jung_function": "sensation",
        "jung_attitude": "extraverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "source_type": "repo_file",
        "source_uri": "docs/hive_neural_backbone_architecture.md",
        "capture_method": "read_file",
        "content_hash": "sha256:demo",
        "summary": "Observed committed Hive neural backbone doctrine.",
        "allowed_uses": [
            "citation",
            "retrieval",
            "source_grounding",
            "observation_indexing",
        ],
        "forbidden_uses": [
            "proof",
            "promotion",
            "unsupported_generalization",
            "theorem_status_rewrite",
        ],
    }

    assert _errors(packet) == []


def test_symbolic_motif_packet_rejects_promotion_authority() -> None:
    packet = {
        **BASE,
        **REPRESENTATION,
        "id": "motif_demo",
        "kind": "SymbolicMotifPacket",
        "status": "active",
        "authority": "semantic",
        "authority_origin": "symbolic_navigation",
        "epistemic_layer": "common_unconscious",
        "cognitive_function": "intuition",
        "jung_function": "intuition",
        "jung_attitude": "introverted",
        "psyche_layer": "common_unconscious",
        "jung_dynamic": "compensation",
        "symbolic_stage": "albedo",
        "promotion_allowed": False,
        "motif_label": "coniunctio_oppositorum",
        "motif_family": "jungian_archetype",
        "source_packet_ids": ["src_obs_demo"],
        "allowed_uses": [
            "retrieval_bias",
            "question_generation",
            "candidate_generation",
            "motif_clustering",
            "resonance_ranking",
        ],
        "forbidden_uses": [
            "proof",
            "promotion",
            "canonical_theorem_admission",
            "silent_lean_rewrite",
            "authority_gate_bypass",
        ],
    }

    assert _errors(packet) == []

    promoted = deepcopy(packet)
    promoted["authority"] = "promoted"
    assert any("'semantic' was expected" in error for error in _errors(promoted))


def test_socratic_question_packet_requires_question_not_proof() -> None:
    packet = {
        **BASE,
        **REPRESENTATION,
        "id": "socratic_demo",
        "kind": "SocraticQuestionPacket",
        "status": "open",
        "authority": "semantic",
        "authority_origin": "socratic_interrogation",
        "epistemic_layer": "cognitive_process",
        "cognitive_function": "thinking",
        "jung_function": "thinking",
        "jung_attitude": "introverted",
        "psyche_layer": "conscious",
        "promotion_allowed": False,
        "question": "What is the weakest owner-anchored version of this symbolic bridge?",
        "question_type": "weakest_version",
        "target_packet_ids": ["motif_demo"],
        "allowed_uses": [
            "critique",
            "hypothesis_extraction",
            "candidate_refinement",
            "falsification_pressure",
            "owner_mapping_pressure",
        ],
        "forbidden_uses": [
            "proof",
            "promotion",
            "verification_claim",
            "theorem_status_rewrite",
        ],
    }

    assert _errors(packet) == []

    proof_like = deepcopy(packet)
    proof_like["forbidden_uses"] = ["promotion", "verification_claim"]
    assert any("does not contain items matching" in error for error in _errors(proof_like))
