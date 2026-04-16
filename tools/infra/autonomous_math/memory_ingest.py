#!/usr/bin/env python3
"""Memory ingestion stage for autonomous_math pipeline."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .evidence_packet import EvidencePacket


def ingest(*, packet: EvidencePacket, run_state: dict[str, Any], out_file: Path) -> None:
    out_file.parent.mkdir(parents=True, exist_ok=True)
    row = {
        "research_goal": packet.research_goal,
        "evidence_count": len(packet.evidence),
        "open_problem_count": len(packet.open_problems),
        "formalization_target_count": len(packet.formalization_targets),
        "status": run_state.get("status", "unknown"),
        "generated_at": run_state.get("generated_at"),
        "report_out": run_state.get("report_out", ""),
    }
    with out_file.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(row, ensure_ascii=True) + "\n")

