from __future__ import annotations

from copy import deepcopy

from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet


BASE = {
    "id": "packet_translation_control_demo",
    "kind": "TranslationControlPacket",
    "status": "active",
    "lineage_id": "lineage_translation_control_demo",
    "revision": 1,
    "origin_run_id": "run_demo",
    "created_at": "2026-05-08T00:00:00Z",
    "updated_at": "2026-05-08T00:00:00Z",
    "authority": "semantic",
    "authority_origin": "translation_control",
    "representation_class": "translator",
    "representation_depth": "operatorial",
    "promotion_allowed": False,
    "packet_version": "1.0.0",
    "packet_hash": "sha256:demo",
    "source_class": "Isabelle_HOL_logic_docs",
    "control_scope": "Isabelle/HOL to Lean theorem-intelligence normalization",
    "purpose": "Prevent unsafe symbol-level translation before any AFP bounded-operator theorem mapping.",
    "rules": [
        "Resolve overloaded constants before Lean mapping.",
        "Always map symbol plus inferred type plus local class context, never raw symbol text alone.",
        "Treat SOME/Hilbert choice as witness-gated unless Lean has a native construction.",
    ],
    "symbol_controls": [
        {
            "source_symbol": "0",
            "classification": "overloaded_constant",
            "inference_required": "target_type",
            "lean_strategy": "Infer target type before choosing Nat.zero, Int.zero, Ring.zero, or operator zero.",
            "forbidden_mappings": ["blind Nat.zero"],
        },
        {
            "source_symbol": "=",
            "classification": "overloaded_equality",
            "inference_required": "target_type",
            "lean_strategy": "Distinguish object equality, Bool equality, and Prop-level equivalence before mapping.",
            "forbidden_mappings": ["blind iff"],
        },
        {
            "source_symbol": "SOME",
            "classification": "hilbert_choice",
            "inference_required": "choice_semantics",
            "lean_strategy": "Prefer witness-gated data or native Lean construction over copying Isabelle choice definitions.",
            "forbidden_mappings": ["unconditional Classical.choose"],
        },
    ],
    "choice_controls": [
        {
            "source_construct": "sqrt_op",
            "lean_strategy": "Use theorem intelligence for positive square-root existence, not the Isabelle fallback-zero choice definition.",
            "guard": "Requires functional-calculus or positive square-root datum in Lean before theorem promotion.",
        }
    ],
    "allowed_uses": ["normalization", "translation_control", "source_guidance"],
    "forbidden_uses": ["proof", "promotion", "canonical_theorem_admission", "authority_gate_bypass"],
    "not_proof_authority": True,
}


def _errors(packet: dict) -> list[str]:
    return validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], build_store())


def test_translation_control_packet_validates_type_directed_controls() -> None:
    assert _errors(BASE) == []


def test_translation_control_packet_rejects_proof_authority_and_missing_proof_ban() -> None:
    promoted = deepcopy(BASE)
    promoted["authority"] = "promoted"
    assert any("'semantic' was expected" in error for error in _errors(promoted))

    proof_allowed = deepcopy(BASE)
    proof_allowed["forbidden_uses"] = ["promotion", "authority_gate_bypass"]
    assert any("does not contain items matching" in error for error in _errors(proof_allowed))


def test_translation_control_packet_requires_symbol_controls() -> None:
    missing_symbols = deepcopy(BASE)
    missing_symbols["symbol_controls"] = []
    assert any("should have at least 1 items" in error for error in _errors(missing_symbols))
