"""Resolve and validate immutable declaration-DAG refresh generations."""

from __future__ import annotations

import re
from typing import Any


_COLLECTION_NAME = re.compile(r"^[A-Za-z0-9_]+$")


def validate_generation_id(generation_id: str) -> None:
    """IDs must also be safe suffixes for both generation collection names."""
    if (not isinstance(generation_id, str)
            or not 1 <= len(generation_id) <= 32
            or not _COLLECTION_NAME.fullmatch(generation_id)):
        raise ValueError("generation ID must be 1-32 ASCII letters, digits or '_'")


def validate_generation_metadata(build_fingerprint: str, import_root: str, namespace: str) -> None:
    """Validate receipt syntax, not binary provenance or source/build coherence."""
    if (not isinstance(build_fingerprint, str)
            or re.fullmatch(r"[0-9a-f]{64}", build_fingerprint) is None):
        raise ValueError("buildFingerprint must be a lowercase SHA-256 hex string")
    for field, value in (("importRoot", import_root), ("namespace", namespace)):
        if (not isinstance(value, str) or not value
                or any(not item or item != item.strip() for item in value.split(","))):
            raise ValueError(f"invalid {field}: expected nonempty comma-separated scope")


def validate_generation_counts(
    declaration_count: int, emitted_edge_count: int,
    valid_edge_count: int, removed_orphan_count: int,
) -> None:
    """Immutable v1: nonempty vertices, lossless edges, no orphan removal.

    Zero edges are valid for a nonempty discrete graph. All count fields are
    mandatory integers (not booleans); zero vertices remain rejected.
    """
    for field, value, minimum in (
        ("declarationCount", declaration_count, 1),
        ("emittedEdgeCount", emitted_edge_count, 0),
        ("validEdgeCount", valid_edge_count, 0),
        ("removedOrphanCount", removed_orphan_count, 0),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
            raise ValueError(f"invalid count for {field}")
    if removed_orphan_count != 0:
        raise ValueError("immutable generation must not remove orphan edges")
    if emitted_edge_count != valid_edge_count:
        raise ValueError("edge count mismatch: emittedEdgeCount != validEdgeCount")


def resolve_decl_graph_generation(db: Any, generation_id: str) -> dict[str, Any]:
    """Return a complete generation receipt after validating both collections.

    The receipt published by ``refresh_decl_graph.py`` is the authority for
    collection names and expected counts.  This rejects incomplete receipts,
    malformed collection names, missing collections, and partial generations.
    """
    validate_generation_id(generation_id)
    rows = list(db.aql.execute(
        "FOR g IN decl_graph_generations "
        "FILTER g._key == @generationId "
        "LIMIT 2 RETURN g",
        bind_vars={"generationId": generation_id},
    ))
    if len(rows) != 1:
        raise ValueError(f"declaration generation {generation_id!r} is absent or ambiguous")
    receipt = rows[0]
    if receipt.get("schema") != "info_geometry.decl_graph_generation.v1":
        raise ValueError(f"declaration generation {generation_id!r} has an unknown receipt schema")
    if receipt.get("status") != "complete":
        raise ValueError(f"declaration generation {generation_id!r} is not complete")

    validate_generation_metadata(
        receipt.get("buildFingerprint"), receipt.get("importRoot"), receipt.get("namespace"),
    )
    validate_generation_counts(
        receipt.get("declarationCount"), receipt.get("emittedEdgeCount"),
        receipt.get("validEdgeCount"), receipt.get("removedOrphanCount"),
    )
    expected = {
        "declCollection": receipt.get("declarationCount"),
        "edgeCollection": receipt.get("validEdgeCount"),
    }
    for field, count in expected.items():
        collection = receipt.get(field)
        if not isinstance(collection, str) or not _COLLECTION_NAME.fullmatch(collection):
            raise ValueError(f"generation {generation_id!r} has an invalid {field}")
        if not db.has_collection(collection):
            raise ValueError(f"generation {generation_id!r} collection {collection!r} is missing")
        actual = db.collection(collection).count()
        if actual != count:
            raise ValueError(
                f"generation {generation_id!r} count mismatch for {collection!r}: "
                f"receipt={count}, collection={actual}"
            )
    invalid_edges = list(db.aql.execute(
        "FOR e IN @@edges "
        "FILTER !IS_SAME_COLLECTION(@decls, e._from) "
        "OR !IS_SAME_COLLECTION(@decls, e._to) "
        "OR DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null "
        "LIMIT 1 RETURN e._key",
        bind_vars={"@edges": receipt["edgeCollection"], "decls": receipt["declCollection"]},
    ))
    if invalid_edges:
        raise ValueError(f"generation {generation_id!r} has dangling or foreign endpoints")
    return receipt
