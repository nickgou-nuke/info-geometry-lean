"""Planner policy constants and calibration helpers."""

from __future__ import annotations


PLANNER_POLICY_VERSION = "v1"

# Replacement candidates can participate in multiple top cluster buckets.
REPLACEMENT_CLUSTER_PARTICIPATION_LIMIT = 3

# The corridor rank decay is intentionally conservative and preserves
# a nonzero contribution for secondary/tertiary cluster memberships.
CORRIDOR_PARTICIPATION_DECAY_MODEL = "harmonic"

# The admissibility scaffold remains planning-only, but we still check a short
# replacement window rather than only the top corridor row.
ADMISSIBILITY_REPLACEMENT_WINDOW = 3

PRECHECK_STATUS_PRIORITY = {
    "blocked": 0,
    "needs-review": 1,
    "provisionally-admissible": 2,
}


def cluster_rank_weight(cluster_rank: int) -> float:
    if cluster_rank <= 0:
        return 1.0
    if CORRIDOR_PARTICIPATION_DECAY_MODEL == "harmonic":
        return 1.0 / float(cluster_rank)
    return 1.0


def precheck_status_priority(status: str | None) -> int:
    if not isinstance(status, str):
        return -1
    return PRECHECK_STATUS_PRIORITY.get(status, -1)


def planner_policy_snapshot() -> dict[str, object]:
    return {
        "version": PLANNER_POLICY_VERSION,
        "corridorParticipationDecayModel": CORRIDOR_PARTICIPATION_DECAY_MODEL,
        "replacementClusterParticipationLimit": REPLACEMENT_CLUSTER_PARTICIPATION_LIMIT,
        "admissibilityReplacementWindow": ADMISSIBILITY_REPLACEMENT_WINDOW,
        "precheckStatusPriority": dict(PRECHECK_STATUS_PRIORITY),
    }
