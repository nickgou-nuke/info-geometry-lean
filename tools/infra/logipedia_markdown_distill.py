#!/usr/bin/env python3
"""Distill `docs/Logipedia.md`-style theorem-bank transcripts into Hive packets.

The distiller is deliberately pre-authority.  It classifies claims and performs a
read-only owner audit against the current repo.  It does not promote foreign,
PDF, Logipedia, or markdown claims to Lean/build/audit authority.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

try:
    from tools.infra.hive_packet_build import stable_json
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
except ImportError:  # pragma: no cover - direct script execution
    ROOT_FOR_IMPORT = Path(__file__).resolve().parents[2]
    if str(ROOT_FOR_IMPORT) not in sys.path:
        sys.path.insert(0, str(ROOT_FOR_IMPORT))
    from tools.infra.hive_packet_build import stable_json
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

ROOT = Path(__file__).resolve().parents[2]
REQUIRED_GATES = ["lean_checked", "build_checked", "audit_checked"]
CLASSIFICATION_ORDER = [
    "owner_projection",
    "constructive_finite_gap",
    "external_adapter_candidate",
    "analytic_gate",
    "roadmap_speculative",
    "reject_overclaim",
]

LEAN_FILE_RE = re.compile(r"(?:lean/)?InfoGeometry/[A-Za-z0-9_./-]+\.lean|[A-Za-z0-9_]+\.lean")
LEAN_DECL_RE = re.compile(r"^\s*(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+([A-Za-z0-9_'.]+)", re.M)
CODE_FENCE_RE = re.compile(r"```lean\s*(.*?)```", re.S)


# [lossless-compact] now_iso folded into igf.common.time_utils.now_iso
from igf.common.time_utils import now_iso


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def slug(value: str, max_len: int = 80) -> str:
    out = re.sub(r"[^A-Za-z0-9]+", "_", value).strip("_").lower()
    return (out or "entry")[:max_len]


def classify_claim(text: str) -> str:
    lowered = text.lower()
    overclaim_terms = [
        "prove rh",
        "proves rh",
        "proof of rh",
        "bost-connes→rh",
        "bost-connes -> rh",
        "zeta-logdet→jaynes",
        "zeta-logdet -> jaynes",
        "prime-gas→spacetime",
        "prime-gas -> spacetime",
    ]
    if any(term in lowered for term in overclaim_terms) and not any(
        guard in lowered for guard in ["must not prove rh", "does not prove rh", "cannot prove rh", "not prove rh"]
    ):
        return "reject_overclaim"

    speculative_terms = ["hilbert-polya", "hilbert polya", "random-walk", "random walk", "physics roadmap", "speculative", "heuristic"]
    if any(term in lowered for term in speculative_terms) and any(x in lowered for x in ["roadmap", "gate", "rh", "riemann"]):
        return "roadmap_speculative"

    analytic_terms = [
        "rieffel",
        "lapidus",
        "spectral operator",
        "fractal string",
        "nyman",
        "beurling",
        "gns",
        "car/uhf",
        "uhf",
        "type iii",
        "analytic",
        "completion",
        "convergence",
        "witness-gated",
        "witness gated",
    ]
    if any(term in lowered for term in analytic_terms) and any(x in lowered for x in ["gate", "gated", "remain", "planned", "new analytic"]):
        return "analytic_gate"

    projection_terms = ["project", "projection", "alias", "aliases", "re-export", "reexport", "already exists", "existing owner", "owner file already exists"]
    if any(term in lowered for term in projection_terms):
        return "owner_projection"

    finite_terms = ["finite", "constructive", "primebitwittenindex", "prime-bit", "möbius", "mobius", "witten", "squarefree"]
    if any(term in lowered for term in finite_terms) and any(x in lowered for x in ["add", "owner", "theorem", "prove", "hole", "missing"]):
        return "constructive_finite_gap"

    if any(term in lowered for term in ["isabelle", "coq", "dedukti", "logipedia", "afp", "external theorem", "adapter"]):
        return "external_adapter_candidate"

    return "roadmap_speculative"


def rank_for(classification: str, text: str) -> int:
    base = {
        "constructive_finite_gap": 90,
        "owner_projection": 80,
        "external_adapter_candidate": 65,
        "analytic_gate": 35,
        "roadmap_speculative": 20,
        "reject_overclaim": 5,
    }[classification]
    lowered = text.lower()
    if any(x in lowered for x in ["first", "most important", "immediate", "exact payload", "correct replacement"]):
        base += 8
    if any(x in lowered for x in ["must not", "do not", "hard rule"]):
        base += 5
    return min(base, 100)


def risk_flags_for(classification: str, text: str) -> list[str]:
    flags = [classification]
    lowered = text.lower()
    if classification in {"analytic_gate", "roadmap_speculative", "reject_overclaim"}:
        flags.append("non_authority_guard_required")
    if any(x in lowered for x in ["rh", "riemann", "hilbert-polya", "bost-connes"]):
        flags.append("rh_facing_claim")
    if any(x in lowered for x in ["witness", "gate", "gated"]):
        flags.append("witness_gate_boundary")
    if classification == "constructive_finite_gap":
        flags.append("finite_constructive_priority")
    if classification == "owner_projection":
        flags.append("duplicate_structure_risk")
    return list(dict.fromkeys(flags))


def extract_files(text: str) -> list[str]:
    files = []
    for match in LEAN_FILE_RE.findall(text):
        value = match.strip("` ")
        if value.endswith(".lean"):
            if value.startswith("lean/"):
                files.append(value)
            elif value.startswith("InfoGeometry/"):
                files.append("lean/" + value)
            else:
                files.append(value)
    return list(dict.fromkeys(files))


def extract_decls(text: str) -> list[str]:
    decls = LEAN_DECL_RE.findall(text)
    backtick_candidates = re.findall(r"`([A-Za-z][A-Za-z0-9_'.]{3,})`", text)
    for candidate in backtick_candidates:
        if not candidate.endswith(".lean") and "." not in candidate:
            decls.append(candidate)
    return list(dict.fromkeys(decls))


def line_offsets(lines: list[str]) -> list[int]:
    offsets = []
    total = 0
    for line in lines:
        offsets.append(total)
        total += len(line) + 1
    return offsets


def line_for_offset(offsets: list[int], char_offset: int) -> int:
    # Small enough for docs-scale parsing; avoids importing bisect in older local shims.
    line = 1
    for idx, start in enumerate(offsets, start=1):
        if start <= char_offset:
            line = idx
        else:
            break
    return line


def candidate_chunks(markdown: str) -> list[tuple[int, int, str]]:
    lines = markdown.splitlines()
    chunks: list[tuple[int, int, str]] = []
    start = 1
    buf: list[str] = []
    for idx, line in enumerate(lines, start=1):
        is_boundary = bool(re.match(r"^#{1,4}\s+", line)) or bool(re.match(r"^(First|Second|Third|Fourth|Fifth|Sixth|Seventh|Eighth|Ninth|Tenth),", line.strip()))
        is_blank_boundary = not line.strip() and buf and not buf[-1].strip().startswith("```")
        if (is_boundary or is_blank_boundary) and buf:
            text = "\n".join(buf).strip()
            if len(text) >= 40:
                chunks.append((start, idx - 1, text))
            start = idx + 1 if is_blank_boundary else idx
            buf = [] if is_blank_boundary else [line]
        else:
            if not buf:
                start = idx
            buf.append(line)
    if buf:
        text = "\n".join(buf).strip()
        if len(text) >= 40:
            chunks.append((start, len(lines), text))

    # Add lean code fences as focused chunks so theorem names are not lost in prose.
    offsets = line_offsets(lines)
    for match in CODE_FENCE_RE.finditer(markdown):
        code = match.group(1).strip()
        if code:
            line = line_for_offset(offsets, match.start())
            chunks.append((line, line + code.count("\n") + 2, code))
    return chunks


def packet_from_entry_fields(
    *,
    source_uri: str,
    source_line_start: int,
    source_line_end: int,
    claim_text: str,
    classification: str,
    lineage_id: str,
    origin_run_id: str,
    created_at: str,
) -> dict[str, Any]:
    files = extract_files(claim_text)
    decls = extract_decls(claim_text)
    lean_decls = []
    for block in CODE_FENCE_RE.findall(claim_text):
        lean_decls.extend(extract_decls(block))
    lean_decls.extend(decls)
    lean_decls = list(dict.fromkeys(lean_decls))
    payload_for_hash = {
        "source_uri": source_uri,
        "source_line_start": source_line_start,
        "source_line_end": source_line_end,
        "claim_text": claim_text,
        "classification": classification,
    }
    digest = stable_hash(payload_for_hash)
    packet = {
        "id": f"packet_theorem_bank_{slug(source_uri)}_{digest[-12:]}",
        "kind": "TheoremBankEntryPacket",
        "status": "classified",
        "lineage_id": lineage_id,
        "revision": 1,
        "origin_run_id": origin_run_id,
        "created_at": created_at,
        "updated_at": created_at,
        "created_by_agent": "logipedia-markdown-distiller",
        "agent_role": "source_bee",
        "backend": "local",
        "tags": ["logipedia", "theorem-bank", classification],
        "notes": "markdown theorem-bank intelligence only; not proof authority",
        "authority": "semantic",
        "representation_class": "translator",
        "representation_depth": "operatorial",
        "promotion_allowed": False,
        "packet_version": "1.0.0",
        "packet_hash": digest,
        "source_uri": source_uri,
        "source_line_start": source_line_start,
        "source_line_end": source_line_end,
        "claim_text": claim_text.strip(),
        "classification": classification,
        "rank_score": rank_for(classification, claim_text),
        "proposed_lean_files": files,
        "proposed_decls": decls,
        "lean_decls": lean_decls,
        "cited_owner_files": files if classification == "owner_projection" else [],
        "risk_flags": risk_flags_for(classification, claim_text),
        "required_gates": REQUIRED_GATES,
    }
    return packet


def distill_markdown(path: Path, source_uri: str | None = None, lineage_id: str = "logipedia-theorem-bank", origin_run_id: str = "logipedia-distill") -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    uri = source_uri or str(path)
    created_at = now_iso()
    entries: list[dict[str, Any]] = []
    seen: set[str] = set()
    for start, end, chunk in candidate_chunks(text):
        classification = classify_claim(chunk)
        # Keep all high-signal classes, and skip only generic low-signal roadmap prose.
        if classification == "roadmap_speculative" and not any(x in chunk.lower() for x in ["roadmap", "gate", "rh", "lean", "theorem", "random"]):
            continue
        packet = packet_from_entry_fields(
            source_uri=uri,
            source_line_start=start,
            source_line_end=end,
            claim_text=chunk,
            classification=classification,
            lineage_id=lineage_id,
            origin_run_id=origin_run_id,
            created_at=created_at,
        )
        key = stable_hash({"claim_text": packet["claim_text"], "classification": packet["classification"]})
        if key in seen:
            continue
        seen.add(key)
        entries.append(packet)
    entries.sort(key=lambda row: (-int(row["rank_score"]), int(row["source_line_start"])))
    return entries


def path_exists(repo_root: Path, raw: str) -> bool:
    return (repo_root / raw).exists() or (repo_root / "lean" / raw).exists()


def read_existing_path(repo_root: Path, raw: str) -> str:
    candidates = [repo_root / raw, repo_root / "lean" / raw]
    for path in candidates:
        if path.exists() and path.is_file():
            return path.read_text(encoding="utf-8", errors="replace")
    return ""


def audit_decision(classification: str, found_files: list[str], missing_files: list[str], found_decls: list[str], missing_decls: list[str]) -> tuple[str, str, str]:
    if classification == "reject_overclaim":
        return "overclaim_rejected", "reject_overclaim", "reject_or_quarantine"
    if classification == "analytic_gate":
        return "analytic_gate_confirmed", "analytic_gate", "create_analytic_gate"
    if classification == "roadmap_speculative":
        return "deferred", "roadmap_only", "record_roadmap_only"
    if classification == "external_adapter_candidate":
        return "assessed", "external_adapter_candidate", "build_external_adapter"
    if classification == "constructive_finite_gap":
        if found_files and not missing_decls:
            return "assessed", "owner_exists", "project_existing_owner"
        return "constructive_gap_confirmed", "constructive_gap", "prove_finite_owner"
    if found_files or found_decls:
        return "projection_planned", "projection_possible", "project_existing_owner"
    if missing_files or missing_decls:
        return "assessed", "owner_missing", "manual_review"
    return "assessed", "owner_missing", "manual_review"


def owner_audit_from_entry(
    entry: dict[str, Any],
    repo_root: Path = ROOT,
    lineage_id: str = "logipedia-theorem-bank",
    origin_run_id: str = "logipedia-owner-audit",
    created_at: str | None = None,
) -> dict[str, Any]:
    created = created_at or now_iso()
    files = list(entry.get("proposed_lean_files", []))
    decls = list(entry.get("proposed_decls", [])) + list(entry.get("lean_decls", []))
    decls = list(dict.fromkeys(decls))
    found_files = [path for path in files if path_exists(repo_root, path)]
    missing_files = [path for path in files if not path_exists(repo_root, path)]
    combined_source = "\n".join(read_existing_path(repo_root, path) for path in found_files)
    found_decls = [decl for decl in decls if decl and re.search(rf"\b(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+{re.escape(decl)}\b", combined_source)]
    missing_decls = [decl for decl in decls if decl not in found_decls]
    status, decision, next_step = audit_decision(str(entry.get("classification", "roadmap_speculative")), found_files, missing_files, found_decls, missing_decls)
    payload_for_hash = {
        "entry": entry.get("id", ""),
        "classification": entry.get("classification", ""),
        "found_files": found_files,
        "missing_files": missing_files,
        "found_decls": found_decls,
        "missing_decls": missing_decls,
        "decision": decision,
    }
    digest = stable_hash(payload_for_hash)
    return {
        "id": f"packet_owner_audit_{slug(str(entry.get('id', 'entry')))}_{digest[-12:]}",
        "kind": "OwnerAuditPacket",
        "status": status,
        "lineage_id": lineage_id,
        "revision": 1,
        "origin_run_id": origin_run_id,
        "created_at": created,
        "updated_at": created,
        "created_by_agent": "logipedia-markdown-distiller",
        "agent_role": "owner_audit_bee",
        "backend": "local",
        "tags": ["logipedia", "owner-audit", str(entry.get("classification", "unknown"))],
        "notes": "read-only owner audit; not proof authority",
        "authority": "semantic",
        "representation_class": "translator",
        "representation_depth": "operatorial",
        "promotion_allowed": False,
        "packet_version": "1.0.0",
        "packet_hash": digest,
        "theorem_bank_entry_ref": str(entry.get("id", "")),
        "classification": str(entry.get("classification", "roadmap_speculative")),
        "claim_text": str(entry.get("claim_text", "")),
        "audit_decision": decision,
        "owner_files_found": found_files,
        "owner_files_missing": missing_files,
        "decls_found": found_decls,
        "decls_missing": missing_decls,
        "recommended_next_step": next_step,
        "audit_notes": "Owner audit checks file/declaration presence only; Lean build/audit still decide authority.",
    }


def validate_or_die(packet: dict[str, Any]) -> None:
    errors = validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], build_store())
    if errors:
        raise SystemExit("invalid generated packet " + packet.get("id", "<unknown>") + ":\n" + "\n".join(f"- {e}" for e in errors))


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def write_queue(path: Path, entries: list[dict[str, Any]], audits: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    counts = Counter(entry["classification"] for entry in entries)
    queue = {
        "schema": "info_geometry.logipedia_theorem_bank_queue.v1",
        "created_at": now_iso(),
        "entry_count": len(entries),
        "owner_audit_count": len(audits),
        "classification_counts": dict(sorted(counts.items())),
        "ranked_entry_ids": [entry["id"] for entry in entries],
        "top_entries": [
            {
                "id": entry["id"],
                "classification": entry["classification"],
                "rank_score": entry["rank_score"],
                "source_line_start": entry["source_line_start"],
                "claim_preview": entry["claim_text"][:240],
            }
            for entry in entries[:50]
        ],
        "authority_boundary": "theorem-bank queue is semantic/navigation only; Lean/build/audit gates decide authority",
    }
    path.write_text(stable_json(queue), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="Markdown theorem-bank transcript, e.g. docs/Logipedia.md")
    parser.add_argument("--entries-out", required=True, help="Output TheoremBankEntryPacket JSONL path")
    parser.add_argument("--owner-audits-out", required=True, help="Output OwnerAuditPacket JSONL path")
    parser.add_argument("--queue-out", required=True, help="Output ranked queue summary JSON path")
    parser.add_argument("--lineage-id", default="logipedia-theorem-bank")
    parser.add_argument("--origin-run-id", default="logipedia-markdown-distill")
    parser.add_argument("--source-uri", default="")
    parser.add_argument("--limit", type=int, default=0)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    input_path = Path(args.input)
    if not input_path.is_absolute():
        input_path = (ROOT / input_path).resolve()
    entries = distill_markdown(
        input_path,
        source_uri=args.source_uri or str(Path(args.input)),
        lineage_id=args.lineage_id,
        origin_run_id=args.origin_run_id,
    )
    if args.limit:
        entries = entries[: args.limit]
    created = now_iso()
    audits = [
        owner_audit_from_entry(
            entry,
            repo_root=ROOT,
            lineage_id=args.lineage_id,
            origin_run_id=args.origin_run_id,
            created_at=created,
        )
        for entry in entries
    ]
    write_jsonl(Path(args.entries_out), entries)
    write_jsonl(Path(args.owner_audits_out), audits)
    write_queue(Path(args.queue_out), entries, audits)
    print(f"theorem-bank entries written: {args.entries_out} ({len(entries)} packets)")
    print(f"owner audits written: {args.owner_audits_out} ({len(audits)} packets)")
    print(f"ranked queue written: {args.queue_out}")


if __name__ == "__main__":
    main()
