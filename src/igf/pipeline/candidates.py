from __future__ import annotations

from typing import Any

from igf.graph.query_runner import resolve_run_id, run_query


MAXENT_STYLE_QUERY_ID = "patch.maxent_style_candidates"
LOG_BARRIER_QUERY_ID = "patch.log_barrier_candidates"
PRIMITIVE_SOURIAU_OWNER_TARGET = (
    "InfoGeometry.Arithmetic.PrimitiveSouriauPipeline.PrimitiveSouriauPipelineOwnerTarget"
)


def find_maxent_style_patch_candidates(
    db: Any,
    run_id: str | None = None,
    *,
    limit: int = 25,
    min_abs_chiral_bias: float = 0.5,
) -> dict[str, Any]:
    """Return conservative MaxEnt/Jaynes-style patch retrieval candidates.

    This is a routing layer over derived chiral sidecars. It does not promote
    a patch to theorem evidence or certify a physical ground state.
    """
    resolved = resolve_run_id(db, run_id)
    rows = run_query(
        db,
        MAXENT_STYLE_QUERY_ID,
        run_id=resolved,
        limit=int(limit),
        min_abs_chiral_bias=float(min_abs_chiral_bias),
    )
    return {
        "ok": True,
        "run_id": resolved,
        "query_id": MAXENT_STYLE_QUERY_ID,
        "authority_level": "derived",
        "claim_scope": "derived_spectral_neighborhood_sidecar",
        "non_overclaim": True,
        "limit": int(limit),
        "min_abs_chiral_bias": float(min_abs_chiral_bias),
        "candidate_count": len(rows),
        "candidates": rows,
    }


def find_log_barrier_patch_candidates(
    db: Any,
    run_id: str | None = None,
    *,
    limit: int = 25,
    min_abs_chiral_bias: float = 0.5,
    barrier_weight: float = 1.0,
    nullity_weight: float = 1.0,
) -> dict[str, Any]:
    """Return conservative self-concordant-barrier patch retrieval candidates.

    This ranks derived chiral sidecars using a log-det-style barrier proxy and
    points the caller at the Lean owner-target corridor that must discharge any
    real theorem claim. It does not certify modular flow, KMS, or ground states.
    """
    resolved = resolve_run_id(db, run_id)
    rows = run_query(
        db,
        LOG_BARRIER_QUERY_ID,
        run_id=resolved,
        limit=int(limit),
        min_abs_chiral_bias=float(min_abs_chiral_bias),
        barrier_weight=float(barrier_weight),
        nullity_weight=float(nullity_weight),
    )
    return {
        "ok": True,
        "run_id": resolved,
        "query_id": LOG_BARRIER_QUERY_ID,
        "lean_owner_target": PRIMITIVE_SOURIAU_OWNER_TARGET,
        "authority_level": "derived",
        "claim_scope": "derived_spectral_neighborhood_sidecar",
        "non_overclaim": True,
        "limit": int(limit),
        "min_abs_chiral_bias": float(min_abs_chiral_bias),
        "barrier_weight": float(barrier_weight),
        "nullity_weight": float(nullity_weight),
        "candidate_count": len(rows),
        "candidates": rows,
    }
