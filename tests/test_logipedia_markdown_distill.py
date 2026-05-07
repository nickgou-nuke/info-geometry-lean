from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from copy import deepcopy

from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
from tools.infra.logipedia_markdown_distill import (
    classify_claim,
    distill_markdown,
    owner_audit_from_entry,
)


BASE = {
    "id": "pkt_demo",
    "status": "classified",
    "lineage_id": "lineage_demo",
    "revision": 1,
    "origin_run_id": "run_demo",
    "created_at": "2026-05-07T00:00:00Z",
    "updated_at": "2026-05-07T00:00:00Z",
}

REPRESENTATION = {
    "representation_class": "translator",
    "representation_depth": "operatorial",
}


def _errors(packet: dict) -> list[str]:
    return validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], build_store())


def test_classify_claim_separates_owner_projection_constructive_gap_and_analytic_gate() -> None:
    assert classify_claim("RealDoubledCliffordFiniteSpine.lean should alias existing owners directly.") == "owner_projection"
    assert classify_claim("Add PrimeBitWittenIndex.lean as a finite theorem owner for Möbius parity.") == "constructive_finite_gap"
    assert classify_claim("Rieffel quantum metric completion and Lapidus spectral operator remain gated.") == "analytic_gate"
    assert classify_claim("Hilbert-Polya physics roadmap for random-walk RH heuristics.") == "roadmap_speculative"
    assert classify_claim("This proves RH from Bost-Connes and zeta-logdet immediately.") == "reject_overclaim"


def test_distill_markdown_extracts_ranked_entries_and_lean_blocks(tmp_path: Path) -> None:
    md = tmp_path / "Logipedia.sample.md"
    md.write_text(
        """
# Logipedia sample

The correct replacement direction is therefore:

```lean
theorem mobius_squarefree_prime_product_eq_parity : True := by
  trivial
```

First, add `PrimeBitWittenIndex.lean`. This is the most important finite theorem hole.

Second, `RealDoubledCliffordFiniteSpine.lean` should alias the owners above and not reprove them.

The random-walk/RH corridor belongs behind `PrimeRandomWalkGate.lean` and must not prove RH.
""".strip(),
        encoding="utf-8",
    )

    entries = distill_markdown(md, source_uri="docs/Logipedia.md")

    classes = {entry["classification"] for entry in entries}
    assert "constructive_finite_gap" in classes
    assert "owner_projection" in classes
    assert "roadmap_speculative" in classes or "analytic_gate" in classes
    assert any("mobius_squarefree_prime_product_eq_parity" in entry["lean_decls"] for entry in entries)
    assert all(entry["rank_score"] >= 0 for entry in entries)
    assert entries == sorted(entries, key=lambda row: (-row["rank_score"], row["source_line_start"]))


def test_theorem_bank_entry_packet_schema_accepts_ranked_non_authority_entry() -> None:
    packet = {
        **BASE,
        **REPRESENTATION,
        "kind": "TheoremBankEntryPacket",
        "status": "classified",
        "authority": "semantic",
        "promotion_allowed": False,
        "packet_version": "1.0.0",
        "packet_hash": "sha256:demo",
        "source_uri": "docs/Logipedia.md",
        "source_line_start": 10,
        "source_line_end": 20,
        "claim_text": "PrimeBitWittenIndex.lean should own the finite Möbius/Witten theorem.",
        "classification": "constructive_finite_gap",
        "rank_score": 90,
        "proposed_lean_files": ["lean/InfoGeometry/Arithmetic/PrimeBitWittenIndex.lean"],
        "proposed_decls": ["mobius_representedNat_eq_fermionParity"],
        "lean_decls": ["mobius_representedNat_eq_fermionParity"],
        "risk_flags": ["finite_constructive_priority"],
        "required_gates": ["lean_checked", "build_checked", "audit_checked"],
    }

    assert _errors(packet) == []

    promoted = deepcopy(packet)
    promoted["authority"] = "promoted"
    assert any("'semantic' was expected" in error for error in _errors(promoted))


def test_owner_audit_packet_schema_requires_non_promoting_owner_decision() -> None:
    entry = {
        "id": "theorem_bank_entry_demo",
        "classification": "owner_projection",
        "claim_text": "RealDoubledCliffordFiniteSpine.lean should alias existing owners.",
        "proposed_lean_files": ["lean/InfoGeometry/Canonical/RealDoubledCliffordFiniteSpine.lean"],
        "proposed_decls": ["K_sq"],
    }
    packet = owner_audit_from_entry(
        entry,
        repo_root=Path.cwd(),
        lineage_id="lineage_demo",
        origin_run_id="run_demo",
        created_at="2026-05-07T00:00:00Z",
    )

    assert packet["kind"] == "OwnerAuditPacket"
    assert packet["authority"] == "semantic"
    assert packet["promotion_allowed"] is False
    assert packet["audit_decision"] in {"owner_exists", "owner_missing", "projection_possible"}
    assert _errors(packet) == []


def test_cli_writes_entries_owner_audits_and_ranked_queue(tmp_path: Path) -> None:
    md = tmp_path / "Logipedia.sample.md"
    entries_out = tmp_path / "entries.jsonl"
    audits_out = tmp_path / "audits.jsonl"
    queue_out = tmp_path / "queue.json"
    md.write_text(
        """
# Sample

`RealDoubledCliffordFiniteSpine.lean` should alias existing Clifford owners.

Add `BilingualHestenesLevelBridge.lean` as a pure dictionary projection.

Rieffel and Lapidus analytic material must remain gated.
""".strip(),
        encoding="utf-8",
    )

    result = subprocess.run(
        [
            sys.executable,
            "tools/infra/logipedia_markdown_distill.py",
            "--input",
            str(md),
            "--entries-out",
            str(entries_out),
            "--owner-audits-out",
            str(audits_out),
            "--queue-out",
            str(queue_out),
            "--lineage-id",
            "test-logipedia",
        ],
        cwd=Path.cwd(),
        text=True,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr
    entries = [json.loads(line) for line in entries_out.read_text(encoding="utf-8").splitlines()]
    audits = [json.loads(line) for line in audits_out.read_text(encoding="utf-8").splitlines()]
    queue = json.loads(queue_out.read_text(encoding="utf-8"))

    assert entries
    assert audits
    assert queue["schema"] == "info_geometry.logipedia_theorem_bank_queue.v1"
    assert queue["classification_counts"]
    assert all(_errors(entry) == [] for entry in entries)
    assert all(_errors(audit) == [] for audit in audits)
