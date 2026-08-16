#!/usr/bin/env python3
"""Shared verification-result contract for checker lane outputs.

The contract is intentionally lightweight and permissive.  It normalizes
heterogeneous checker outputs into declaration-scoped records that can be merged
and policy-filtered later.
"""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.hashing import stable_hash
from igf.common.time_utils import utc_now_iso

utc_now = utc_now_iso

AuthorityLevel = str  # "heuristic" | "policy" | "kernel" | "lean-authority"
Evidence = dict[str, Any]
SCHEMA = "info_geometry.verification_result.v1"
CONTRACT_VERSION = "1"


@dataclass
class VerificationRecord:
    decl: str
    module: str
    lane: str
    ok: bool
    severity: int | str
    checks: list[str]
    reasons: list[str]
    evidence: list[Evidence]
    provenance: dict[str, Any]
    authority_level: AuthorityLevel = "heuristic"

    def to_payload(self) -> dict[str, Any]:
        payload = {
            "decl": self.decl,
            "module": self.module,
            "lane": self.lane,
            "ok": bool(self.ok),
            "severity": self.severity,
            "checks": list(self.checks),
            "reasons": list(self.reasons),
            "evidence": [dict(item) for item in self.evidence],
            "provenance": dict(self.provenance),
            "authority_level": str(self.authority_level),
            "timestamp": utc_now(),
            "schema": SCHEMA,
            "id": "",
        }
        payload["id"] = stable_hash(
            {
                "decl": payload["decl"],
                "lane": payload["lane"],
                "ok": payload["ok"],
                "checks": payload["checks"],
                "reasons": payload["reasons"],
                "timestamp": payload["timestamp"],
            }
        )
        return payload


def read_json_lines(path: Path) -> list[dict[str, Any]]:
    if path is None or not path.exists():
        return []
    out: list[dict[str, Any]] = []
    if path.suffix.lower() == ".jsonl":
        with path.open("r", encoding="utf-8") as handle:
            for raw in handle:
                raw = raw.strip()
                if not raw:
                    continue
                try:
                    row = json.loads(raw)
                except Exception:
                    continue
                if isinstance(row, dict):
                    out.append(row)
    else:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return []
        if isinstance(payload, list):
            out.extend(row for row in payload if isinstance(row, dict))
        elif isinstance(payload, dict):
            out.append(payload)
    return out

