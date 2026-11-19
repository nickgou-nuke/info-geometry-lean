"""E2E Verification & Rubric Suite (E2E_TEST_TRACK, F4.2) for R1/R2/R3 reconciliation."""

from __future__ import annotations

import os
from pathlib import Path

REPO_ROOT: Path = Path(__file__).resolve().parents[2]
SCRATCH_DIR: Path = REPO_ROOT / "scratch" / "e2e_reconciliation"
PROBES_DIR: Path = SCRATCH_DIR / "probes"
REPORTS_DIR: Path = SCRATCH_DIR / "reports"

VALID_MODES: tuple[str, ...] = ("baseline", "m1", "m2", "m3", "full")
ALLOWED_AXIOMS: frozenset[str] = frozenset({"propext", "Quot.sound", "Classical.choice"})


def get_mode(explicit: str | None = None) -> str:
    """Return and validate the active E2E execution mode."""
    mode = (explicit or os.environ.get("E2E_MODE", "baseline")).strip().lower()
    if mode not in VALID_MODES:
        raise ValueError(f"Invalid E2E_MODE {mode!r}; expected one of {VALID_MODES}")
    return mode
