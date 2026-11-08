#!/usr/bin/env python3
"""
CAPA (Corrective and Preventive Action) tracking per docs/ALCHEMICAL_QMS_SOP.md
section 10.

For every REQUEST_CHANGES or REJECT finding, a CAPA record is created with:
  - nonconformance ID
  - finding
  - root cause
  - corrective action
  - preventive action
  - verification command
  - closure status

CAPA records are stored under `artifacts/qms/capa/` as individual JSON files
and an aggregated `artifacts/qms/capa_index.json`.

Usage:
    from tools.qms.capa import CAPARecord, CAPAStore

    store = CAPAStore(ROOT / "artifacts" / "qms" / "capa")
    record = store.create(
        finding="proof relies on unproved zornMul_comm lemma",
        root_cause="G-A assumed auxiliary lemma exists without owner search",
        corrective_action="prove zornMul_comm as auxiliary lemma",
        preventive_action="require owner-first search before auxiliary lemma use",
        verification_command="lake build InfoGeometry.Algebra.ZornMatrix",
    )
    store.close(record.id, "verified")
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root

ROOT = repo_root()

CAPA_SCHEMA = "info_geometry.qms.capa.v1"

CLOSURE_STATUSES = {"open", "closed", "verified"}

NONCONFORMANCE_ID_RE = re.compile(r"^CAPA-[A-Za-z0-9_-]+-[A-Za-z0-9]+$")


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def validate_closure_status(value: str) -> None:
    if value not in CLOSURE_STATUSES:
        raise ValueError(
            f"invalid closure_status: {value!r}; must be one of {sorted(CLOSURE_STATUSES)}"
        )


def validate_nonconformance_id(value: str) -> None:
    if not NONCONFORMANCE_ID_RE.match(value):
        raise ValueError(
            f"invalid nonconformance_id: {value!r}; expected CAPA-<task>-<suffix> format"
        )


class CAPARecord:
    """A single CAPA record."""

    def __init__(
        self,
        *,
        nonconformance_id: str,
        finding: str,
        root_cause: str,
        corrective_action: str,
        preventive_action: str,
        verification_command: str,
        closure_status: str = "open",
        linked_artifact: str | None = None,
        linked_task_id: str | None = None,
    ) -> None:
        validate_nonconformance_id(nonconformance_id)
        validate_closure_status(closure_status)
        self.id = nonconformance_id
        self.finding = finding
        self.root_cause = root_cause
        self.corrective_action = corrective_action
        self.preventive_action = preventive_action
        self.verification_command = verification_command
        self.closure_status = closure_status
        self.linked_artifact = linked_artifact
        self.linked_task_id = linked_task_id
        self.created_at = _now_iso()
        self.closed_at: str | None = None
        self.verified_at: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": CAPA_SCHEMA,
            "nonconformance_id": self.id,
            "finding": self.finding,
            "root_cause": self.root_cause,
            "corrective_action": self.corrective_action,
            "preventive_action": self.preventive_action,
            "verification_command": self.verification_command,
            "closure_status": self.closure_status,
            "linked_artifact": self.linked_artifact,
            "linked_task_id": self.linked_task_id,
            "created_at": self.created_at,
            "closed_at": self.closed_at,
            "verified_at": self.verified_at,
            "record_sha256": _sha256_text(
                json.dumps(
                    {
                        "nonconformance_id": self.id,
                        "finding": self.finding,
                        "root_cause": self.root_cause,
                        "corrective_action": self.corrective_action,
                        "preventive_action": self.preventive_action,
                        "verification_command": self.verification_command,
                        "closure_status": self.closure_status,
                    },
                    sort_keys=True,
                )
            ),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "CAPARecord":
        record = cls(
            nonconformance_id=data["nonconformance_id"],
            finding=data["finding"],
            root_cause=data["root_cause"],
            corrective_action=data["corrective_action"],
            preventive_action=data["preventive_action"],
            verification_command=data["verification_command"],
            closure_status=data.get("closure_status", "open"),
            linked_artifact=data.get("linked_artifact"),
            linked_task_id=data.get("linked_task_id"),
        )
        record.created_at = data.get("created_at", record.created_at)
        record.closed_at = data.get("closed_at")
        record.verified_at = data.get("verified_at")
        return record

    def close(self, status: str = "closed") -> None:
        """Mark the CAPA as closed or verified."""
        validate_closure_status(status)
        if self.closure_status == "verified":
            raise ValueError(f"CAPA {self.id} is already verified; cannot re-close")
        self.closure_status = status
        now = _now_iso()
        if status == "closed":
            self.closed_at = now
        elif status == "verified":
            self.verified_at = now
            self.closed_at = now


class CAPAStore:
    """File-backed store for CAPA records."""

    def __init__(self, directory: Path | str) -> None:
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.index_path = self.directory / "capa_index.json"

    def _record_path(self, nonconformance_id: str) -> Path:
        return self.directory / f"{nonconformance_id}.json"

    def create(
        self,
        *,
        finding: str,
        root_cause: str,
        corrective_action: str,
        preventive_action: str,
        verification_command: str,
        linked_artifact: str | None = None,
        linked_task_id: str | None = None,
        closure_status: str = "open",
    ) -> CAPARecord:
        """Create a new CAPA record with an auto-generated ID."""
        # Auto-generate ID from finding hash + timestamp
        stamp = _now_iso()
        hash_input = f"{finding}|{root_cause}|{stamp}"
        digest = hashlib.sha256(hash_input.encode("utf-8")).hexdigest()[:8]
        task_part = (linked_task_id or "GEN").upper().replace("-", "_")
        nonconformance_id = f"CAPA-{task_part}-{digest}"

        record = CAPARecord(
            nonconformance_id=nonconformance_id,
            finding=finding,
            root_cause=root_cause,
            corrective_action=corrective_action,
            preventive_action=preventive_action,
            verification_command=verification_command,
            closure_status=closure_status,
            linked_artifact=linked_artifact,
            linked_task_id=linked_task_id,
        )
        self.save(record)
        return record

    def save(self, record: CAPARecord) -> None:
        path = self._record_path(record.id)
        path.write_text(json.dumps(record.to_dict(), indent=2) + "\n", encoding="utf-8")
        self._rewrite_index()

    def get(self, nonconformance_id: str) -> CAPARecord | None:
        path = self._record_path(nonconformance_id)
        if not path.is_file():
            return None
        data = json.loads(path.read_text(encoding="utf-8"))
        return CAPARecord.from_dict(data)

    def list_all(self) -> list[CAPARecord]:
        records: list[CAPARecord] = []
        for path in sorted(self.directory.glob("CAPA-*.json")):
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
                records.append(CAPARecord.from_dict(data))
            except (json.JSONDecodeError, KeyError):
                continue
        return records

    def close(self, nonconformance_id: str, status: str = "closed") -> CAPARecord:
        record = self.get(nonconformance_id)
        if record is None:
            raise KeyError(f"CAPA record not found: {nonconformance_id}")
        record.close(status)
        self.save(record)
        return record

    def open_count(self) -> int:
        return sum(1 for r in self.list_all() if r.closure_status == "open")

    def _rewrite_index(self) -> None:
        records = self.list_all()
        index = {
            "schema": CAPA_SCHEMA,
            "generated_at": _now_iso(),
            "count": len(records),
            "open_count": self.open_count(),
            "records": [r.to_dict() for r in records],
        }
        self.index_path.write_text(
            json.dumps(index, indent=2) + "\n", encoding="utf-8"
        )


def example_capa_records() -> list[CAPARecord]:
    """Return the two example CAPA records from SOP section 10."""
    return [
        CAPARecord(
            nonconformance_id="CAPA-MATRIX-001",
            finding="matrix packet was treated as colimit theorem",
            root_cause="finite matrix/CAS evidence promoted to direct-limit claim",
            corrective_action="downgrade claim to finite stage",
            preventive_action="require colimit owner search and direct-limit theorem before future promotion",
            verification_command=(
                "python3 tools/qms/run_qms.py --task-id T-MATRIX "
                "owner-search --artifact path/to/artifact.lean "
                "--query theorem_or_concept"
            ),
            linked_task_id="T-MATRIX",
        ),
        CAPARecord(
            nonconformance_id="CAPA-ZORN-001",
            finding="full Zorn commutator treated as Lie bracket",
            root_cause="nonassociative Zorn commutator incorrectly packaged as LieRing instance",
            corrective_action="cite commutator_jacobi_U_zero_U_one_U_two_ne_zero and redirect to derivation algebra",
            preventive_action="require nonassociative obstruction search before any LieRing instance",
            verification_command="grep -rn commutator_jacobi lean/InfoGeometry/Algebra/ZornVectorMatrix.lean",
            linked_task_id="T-ZORN",
        ),
    ]


def main() -> int:
    store = CAPAStore(ROOT / "artifacts" / "qms" / "capa")
    for rec in example_capa_records():
        store.create(
            finding=rec.finding,
            root_cause=rec.root_cause,
            corrective_action=rec.corrective_action,
            preventive_action=rec.preventive_action,
            verification_command=rec.verification_command,
            linked_artifact=rec.linked_artifact,
            linked_task_id=rec.linked_task_id,
        )
    print(f"[capa] store initialized at {store.directory}")
    print(f"[capa] {store.open_count()} open CAPA records")
    for rec in store.list_all():
        print(f"  - {rec.id}: {rec.closure_status} — {rec.finding[:60]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
