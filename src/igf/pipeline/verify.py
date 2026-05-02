from __future__ import annotations

from typing import Any

from igf.graph.query_runner import resolve_run_id, run_query


def verify_run(db: Any, run_id: str | None = None, *, limit: int = 25) -> dict[str, Any]:
    resolved = resolve_run_id(db, run_id)
    summary_rows = run_query(db, "verify.run_summary", run_id=resolved)
    summary = summary_rows[0] if summary_rows else {"run_id": resolved}

    orphan_spectral = run_query(db, "verify.orphan_spectral", run_id=resolved)
    orphan_members = run_query(db, "verify.orphan_members", run_id=resolved)
    orphan_edges = run_query(db, "verify.orphan_patch_edges", run_id=resolved)
    policy = run_query(db, "verify.policy_violations", run_id=resolved)

    ok = not orphan_spectral and not orphan_members and not orphan_edges and not policy
    return {
        "ok": ok,
        "run_id": resolved,
        "summary": summary,
        "orphan_spectral_count": len(orphan_spectral),
        "orphan_member_count": len(orphan_members),
        "orphan_patch_edge_count": len(orphan_edges),
        "policy_violation_count": len(policy),
        "samples": {
            "orphan_spectral": orphan_spectral[:limit],
            "orphan_members": orphan_members[:limit],
            "orphan_patch_edges": orphan_edges[:limit],
            "policy_violations": policy[:limit],
        },
    }

