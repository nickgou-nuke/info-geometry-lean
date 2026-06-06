#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

STRONG_NAME_TOKENS = {
    "theorem", "bridge", "equiv", "equivalence", "classification", "reconstruction",
    "duality", "hodge", "kms", "yang", "mills", "einstein", "boltzmann",
    "hamiltonian", "entropy", "spectral", "canonical", "unified", "universal",
    "stinespring", "reconstruction", "convergence", "perfect", "completeness",
}

STRONG_DOC_TOKENS = {
    "establish", "proves", "classifies", "reconstructs", "equivalence", "universal",
    "canonical", "complete", "full", "foundation", "fundamental", "theorem",
    "duality", "hodge", "spectral", "convergence", "perfect", "exact",
}

OBFUSCATION_TOKENS = {
    "placeholder", "trust", "unsafe", "admit", "admitax", "axiom", "opaque",
    "certificate", "witness", "socket", "readback", "sorryproof", "proofsocket",
    "kms_sorryproof", "fake", "stub", "todo_proof", "proof_placeholder",
}

THEOREM_AS_DATA_TOKENS = {
    "_proof",
    "_law",
    "_certificate",
    "_holds",
    "_valid",
    "_eq_",
    "noncollapse_true",
    "donoho_stark_support",
    "supportlowerbound",
}

HIGH_SEVERITY_KINDS = {
    "obfuscation_suspicion",
    "axiomatic_frontier_review",
    "docstring_statement_mismatch",
    "theorem_as_data_review",
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def stable_id(prefix: str, *parts: str) -> str:
    seed = "|".join(parts)
    digest = hashlib.sha1(seed.encode("utf-8")).hexdigest()
    return f"{prefix}_{digest[:24]}"


def iter_jsonl(path: Path | None) -> Iterable[dict[str, Any]]:
    if path is None or not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            raw = line.strip()
            if not raw:
                continue
            try:
                obj = json.loads(raw)
            except Exception:
                continue
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def as_dict(value: Any) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


def as_list(value: Any) -> list[Any]:
    return value if isinstance(value, list) else []


def lower_words(text: str) -> set[str]:
    lowered = text.lower()
    out: set[str] = set()
    cur: list[str] = []
    for ch in lowered:
        if ch.isalnum() or ch == "_":
            cur.append(ch)
        else:
            if cur:
                out.add("".join(cur))
                cur = []
    if cur:
        out.add("".join(cur))
    # Also catch camel-ish substrings by simple substring checks elsewhere.
    return out


def contains_any(text: str, tokens: set[str]) -> bool:
    lowered = text.lower()
    return any(tok in lowered for tok in tokens)


def is_generated_helper_decl(name: str) -> bool:
    parts = [part for part in str(name).split(".") if part]
    if not parts:
        return False
    last = parts[-1]
    if last in {"casesOn", "ctorIdx", "noConfusion", "noConfusionType", "rec", "recOn", "brecOn", "binductionOn"}:
        return True
    if last == "mk":
        return True
    if len(parts) >= 2 and parts[-2] == "mk" and last in {"inj", "noConfusion", "sizeOf_spec"}:
        return True
    return False


def node_doc(node: dict[str, Any]) -> str:
    attrs = as_dict(node.get("attrs"))
    nested_attrs = as_dict(attrs.get("attrs"))
    candidates = [
        node.get("doc"),
        attrs.get("doc"),
        nested_attrs.get("doc"),
        attrs.get("documentation"),
    ]
    for c in candidates:
        if isinstance(c, str) and c.strip():
            return c
    return ""


def get_role(node: dict[str, Any]) -> str:
    attrs = as_dict(node.get("attrs"))
    vacuity = as_dict(attrs.get("vacuity"))
    role = vacuity.get("role") or attrs.get("role") or node.get("role") or "unknown"
    return str(role)


def get_contamination_state(node: dict[str, Any]) -> str:
    attrs = as_dict(node.get("attrs"))
    contamination = as_dict(attrs.get("contamination"))
    hole = as_dict(attrs.get("hole"))
    state = hole.get("state") or contamination.get("state") or "clean"
    return str(state)


def has_graphrag_educational_alias(node: dict[str, Any]) -> bool:
    attrs = as_dict(node.get("attrs"))
    graphrag = as_dict(attrs.get("graphrag"))
    if bool(graphrag.get("has_educational_alias", False)):
        return True
    if str(graphrag.get("role", "")).lower() in {"educational_alias", "pedagogical_alias"}:
        return True
    doc = node_doc(node)
    return "educational alias" in doc.lower() or "pedagogical" in doc.lower()


def looks_like_theorem_as_data(node: dict[str, Any]) -> bool:
    name = str(node.get("name") or node.get("id") or "").strip().lower()
    doc = node_doc(node).lower()
    if not name:
        return False
    last = name.split(".")[-1]
    if last in THEOREM_AS_DATA_TOKENS:
        return True
    if any(tok in last for tok in THEOREM_AS_DATA_TOKENS):
        return True
    if any(tok in name for tok in THEOREM_AS_DATA_TOKENS):
        return True
    return contains_any(doc, {
        "stored certificate",
        "witness-gated certificate",
        "re-export of the stored",
        "proof-carrying data",
        "theorem-as-data",
        "wrapper theorem",
        "certificate field",
        "readback of the stored",
    })


def direct_evidence_refs(node: dict[str, Any]) -> list[str]:
    attrs = as_dict(node.get("attrs"))
    refs: list[str] = []
    for key in ("vacuity", "contamination", "source_patch", "hodge", "hole"):
        sub = as_dict(attrs.get(key))
        ref = sub.get("certificate_ref") or sub.get("evidence_ref")
        if isinstance(ref, str) and ref:
            refs.append(ref)
    cert = attrs.get("certificate_ref")
    if isinstance(cert, str) and cert:
        refs.append(cert)
    return sorted(set(refs))


def mk_packet(
    *,
    target: str,
    module: str,
    file: str | None,
    critic_kind: str,
    severity: str,
    confidence: float,
    claim: dict[str, Any],
    evidence_refs: list[str],
    recommended_action: str = "human_review",
    allowed_next_actions: list[str] | None = None,
    source_modification_allowed: bool = False,
) -> dict[str, Any]:
    return {
        "packet_id": stable_id("cp", target, critic_kind, json.dumps(claim, sort_keys=True)),
        "packet_stream": "critic",
        "created_at": utc_now(),
        "target": target,
        "module": module,
        "file": file,
        "critic_kind": critic_kind,
        "severity": severity,
        "confidence": round(float(confidence), 4),
        "evidence_refs": evidence_refs,
        "claim": claim,
        "recommended_action": recommended_action,
        "allowed_next_actions": allowed_next_actions or [
            "human_review",
            "mark_protected",
            "open_bridge_obligation",
            "suppress_for_epoch",
        ],
        "source_modification_allowed": source_modification_allowed,
    }


@dataclass
class PacketIndex:
    proof_holes_by_target: dict[str, list[dict[str, Any]]]
    bridge_by_target: dict[str, list[dict[str, Any]]]
    alignment_by_target: dict[str, list[dict[str, Any]]]


def build_packet_index(
    proof_holes: Iterable[dict[str, Any]],
    bridge_packets: Iterable[dict[str, Any]],
    alignment_packets: Iterable[dict[str, Any]],
) -> PacketIndex:
    def add(index: dict[str, list[dict[str, Any]]], key: str, packet: dict[str, Any]) -> None:
        if key:
            index.setdefault(key, []).append(packet)

    holes: dict[str, list[dict[str, Any]]] = {}
    bridges: dict[str, list[dict[str, Any]]] = {}
    alignments: dict[str, list[dict[str, Any]]] = {}

    for p in proof_holes:
        add(holes, str(p.get("target") or p.get("src") or ""), p)
    for p in bridge_packets:
        add(bridges, str(p.get("target") or as_dict(p.get("payload")).get("target_cluster_root") or ""), p)
    for p in alignment_packets:
        payload = as_dict(p.get("payload"))
        add(alignments, str(p.get("target") or payload.get("source_decl") or ""), p)
        add(alignments, str(payload.get("target_decl") or ""), p)

    return PacketIndex(holes, bridges, alignments)


def generate_for_node(node: dict[str, Any], pkt_index: PacketIndex) -> list[dict[str, Any]]:
    if node.get("kind") != "Declaration":
        return []

    name = str(node.get("name") or node.get("id") or "")
    if not name:
        return []
    module = str(node.get("module") or "")
    file = node.get("file") if isinstance(node.get("file"), str) else None
    if is_generated_helper_decl(name):
        return []
    attrs = as_dict(node.get("attrs"))
    vacuity = as_dict(attrs.get("vacuity"))
    hodge = as_dict(attrs.get("hodge"))
    role = get_role(node)
    contamination = get_contamination_state(node)
    doc = node_doc(node)
    evidence_refs = direct_evidence_refs(node)
    packets: list[dict[str, Any]] = []

    name_strong = contains_any(name, STRONG_NAME_TOKENS)
    doc_strong = contains_any(doc, STRONG_DOC_TOKENS)
    is_transport = role in {"fake_transport", "pure_conductor", "dead_socket"}

    if is_transport and name_strong:
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="proof_shape_name_mismatch",
            severity="high" if role == "dead_socket" else "medium",
            confidence=0.86 if role == "fake_transport" else 0.78,
            evidence_refs=evidence_refs,
            claim={
                "surface_name": name,
                "vacuity_role": role,
                "problem": "The declaration name suggests a substantive theorem or bridge, but the proof-shape audit classifies it as transport/conductor/dead socket.",
            },
            allowed_next_actions=[
                "rename theorem",
                "strengthen statement",
                "replace with explicit sorry",
                "route to bridge packet",
                "mark educational alias",
            ],
        ))

    if is_transport and doc_strong:
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="docstring_statement_mismatch",
            severity="high",
            confidence=0.81,
            evidence_refs=evidence_refs,
            claim={
                "doc_excerpt": doc[:360],
                "vacuity_role": role,
                "problem": "The documentation uses strong mathematical language, but the proof-shape audit is weak or transport-only.",
            },
            allowed_next_actions=[
                "weaken docstring",
                "strengthen formal statement",
                "mark educational alias",
                "open human review ticket",
            ],
        ))

    if contamination in {"explicit_sorry", "transitive_sorry", "honest_sorry", "open_hole", "sorryAx"}:
        hole_packets = pkt_index.proof_holes_by_target.get(name, [])
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="honest_sorry_triage",
            severity="medium",
            confidence=0.9 if hole_packets else 0.75,
            evidence_refs=evidence_refs + [str(p.get("packet_id")) for p in hole_packets if p.get("packet_id")],
            claim={
                "hole_state": contamination,
                "problem": "This is visible proof debt. It should be tracked as a proof-hole work item, not hidden or vacuumed.",
                "proof_hole_packets": [p.get("packet_id") for p in hole_packets if p.get("packet_id")],
            },
            recommended_action="proof_hole_review",
            allowed_next_actions=[
                "prove the hole",
                "replace with approved theorem",
                "keep explicit sorry in dev profile",
                "open bridge obligation",
            ],
        ))

    if contamination in {"laundered_sorry", "forbidden_axiom", "opaque_boundary", "local_axiom"} or contains_any(name + " " + doc, OBFUSCATION_TOKENS):
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="obfuscation_suspicion",
            severity="high",
            confidence=0.88 if contamination != "clean" else 0.62,
            evidence_refs=evidence_refs,
            claim={
                "contamination_state": contamination,
                "problem": "The declaration shows signs of hidden proof debt or proof-obligation laundering. Use explicit sorry or a bridge obligation instead.",
            },
            recommended_action="quarantine_or_manual_review",
            allowed_next_actions=[
                "replace hidden debt with explicit sorry",
                "remove local axiom or opaque stand-in",
                "open axiom bridge packet",
                "quarantine downstream cone",
            ],
        ))

    if looks_like_theorem_as_data(node):
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="theorem_as_data_review",
            severity="high",
            confidence=0.91,
            evidence_refs=evidence_refs,
            claim={
                "problem": "The declaration surface looks like theorem-as-data or a wrapper theorem. Move the mathematical inequality/outcome into an explicit theorem with hypotheses, or expose honest owner debt with `sorry`.",
                "name": name,
                "doc_excerpt": doc[:360],
            },
            recommended_action="replace_with_explicit_conditional_theorem",
            allowed_next_actions=[
                "move proof obligation to theorem parameters",
                "remove stored certificate field",
                "replace wrapper theorem with owner theorem",
                "open honest owner debt",
            ],
        ))

    if role == "orphan_genuine":
        bridges = pkt_index.bridge_by_target.get(name, [])
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="orphan_genuine_review",
            severity="medium",
            confidence=0.82,
            evidence_refs=evidence_refs + [str(p.get("packet_id")) for p in bridges if p.get("packet_id")],
            claim={
                "vacuity_role": role,
                "orphan_forest": hodge.get("orphan_forest"),
                "problem": "The component appears mathematically genuine but disconnected. It should be preserved and bridged/exposed, not deleted.",
            },
            recommended_action="bridge_review",
            allowed_next_actions=[
                "emit bridge packet",
                "expose in public API",
                "connect to Mathlib/root theorem",
                "mark protected",
            ],
        ))

    if contamination in {"forbidden_axiom", "opaque_boundary", "local_axiom"}:
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="axiomatic_frontier_review",
            severity="high",
            confidence=0.86,
            evidence_refs=evidence_refs,
            claim={
                "contamination_state": contamination,
                "protected_intersections": hodge.get("protected_intersections", []),
                "problem": "This node is part of an axiomatic or opaque frontier. It may be load-bearing and should be bridged/quarantined, not vacuumed.",
            },
            recommended_action="axiom_bridge_review",
            allowed_next_actions=[
                "open axiom bridge obligation",
                "replace with approved theorem",
                "quarantine dependent cone",
                "mark protected until resolved",
            ],
        ))

    if has_graphrag_educational_alias(node):
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="educational_alias_protection",
            severity="medium",
            confidence=0.76,
            evidence_refs=evidence_refs,
            claim={
                "problem": "GraphRAG/docs suggest this may be an educational or pedagogical alias. Destructive surgery should be blocked or manual.",
            },
            recommended_action="protect_or_manual_review",
            allowed_next_actions=[
                "mark protected",
                "keep as educational alias",
                "manual contraction only",
                "document canonical route",
            ],
        ))

    overlap_candidates = as_list(hodge.get("forest_overlap_candidates"))
    alignments = pkt_index.alignment_by_target.get(name, [])
    if overlap_candidates or alignments:
        packets.append(mk_packet(
            target=name,
            module=module,
            file=file,
            critic_kind="alignment_candidate_review",
            severity="low",
            confidence=0.7 if alignments else 0.62,
            evidence_refs=evidence_refs + [str(p.get("packet_id")) for p in alignments if p.get("packet_id")],
            claim={
                "forest_overlap_candidates": overlap_candidates[:8],
                "alignment_packets": [p.get("packet_id") for p in alignments if p.get("packet_id")],
                "problem": "Structural/Hodge overlap suggests a bridge or deprecate-and-route candidate. Lean must verify any obligation.",
            },
            recommended_action="alignment_compare_review",
            allowed_next_actions=[
                "open 4-pane Compare view",
                "generate temporary kernel obligation",
                "emit bridge packet",
                "suppress false match",
            ],
        ))

    return packets


def dedupe_packets(packets: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[str] = set()
    out: list[dict[str, Any]] = []
    for p in packets:
        pid = str(p.get("packet_id", ""))
        if pid in seen:
            continue
        seen.add(pid)
        out.append(p)
    out.sort(key=lambda p: (-(float(p.get("confidence", 0))), str(p.get("severity", "")), str(p.get("target", ""))))
    return out


def render_md(packets: list[dict[str, Any]], out_jsonl: Path, top_n: int) -> str:
    lines = [
        "# LeanTrail Critic Packet Report",
        "",
        f"- generated_at: `{utc_now()}`",
        f"- output_jsonl: `{out_jsonl}`",
        f"- packet_count: `{len(packets)}`",
        "",
        "## Top Packets",
        "",
        "| rank | kind | severity | confidence | target | recommendation |",
        "|---:|---|---|---:|---|---|",
    ]
    for idx, p in enumerate(packets[: max(0, top_n)], start=1):
        lines.append(
            f"| {idx} | `{p.get('critic_kind','')}` | `{p.get('severity','')}` | "
            f"{float(p.get('confidence', 0.0)):.2f} | `{p.get('target','')}` | "
            f"`{p.get('recommended_action','')}` |"
        )
    return "\n".join(lines) + "\n"


def run(
    *,
    snapshot_path: Path,
    proof_holes_path: Path | None,
    bridge_packets_path: Path | None,
    alignment_packets_path: Path | None,
    out_jsonl: Path,
    json_out: Path,
    md_out: Path | None,
    top_n: int,
) -> dict[str, Any]:
    snapshot = load_json(snapshot_path)
    nodes = [n for n in snapshot.get("nodes", []) if isinstance(n, dict)]

    pkt_index = build_packet_index(
        iter_jsonl(proof_holes_path),
        iter_jsonl(bridge_packets_path),
        iter_jsonl(alignment_packets_path),
    )

    packets: list[dict[str, Any]] = []
    for node in nodes:
        packets.extend(generate_for_node(node, pkt_index))
    packets = dedupe_packets(packets)

    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with out_jsonl.open("w", encoding="utf-8") as handle:
        for p in packets:
            handle.write(json.dumps(p, ensure_ascii=True, sort_keys=True) + "\n")

    if md_out is not None:
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(render_md(packets, out_jsonl, top_n), encoding="utf-8")

    counts_by_kind: dict[str, int] = {}
    counts_by_severity: dict[str, int] = {}
    for p in packets:
        kind = str(p.get("critic_kind", "unknown"))
        sev = str(p.get("severity", "unknown"))
        counts_by_kind[kind] = counts_by_kind.get(kind, 0) + 1
        counts_by_severity[sev] = counts_by_severity.get(sev, 0) + 1

    report = {
        "created_at": utc_now(),
        "snapshot": str(snapshot_path),
        "output_jsonl": str(out_jsonl),
        "output_md": str(md_out) if md_out else None,
        "packet_count": len(packets),
        "counts_by_kind": counts_by_kind,
        "counts_by_severity": counts_by_severity,
        "source_modification_allowed": False,
    }
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate LeanTrail critic packets from vacuity/graph evidence.")
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.vacuity.json")
    parser.add_argument("--proof-holes", default="artifacts/leantrail/proof_hole_packets.jsonl")
    parser.add_argument("--bridge-packets", default="artifacts/leantrail/bridge_packets.jsonl")
    parser.add_argument("--alignment-packets", default="artifacts/leantrail/alignment_packets.jsonl")
    parser.add_argument("--out", default="artifacts/leantrail/critic_packets.jsonl")
    parser.add_argument("--json-out", default="artifacts/leantrail/critic_report.json")
    parser.add_argument("--md-out", default="artifacts/leantrail/critic_report.md")
    parser.add_argument("--top-n", type=int, default=50)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    snapshot_path = Path(args.snapshot).resolve()
    if not snapshot_path.exists():
        raise FileNotFoundError(f"Snapshot not found: {snapshot_path}")
    report = run(
        snapshot_path=snapshot_path,
        proof_holes_path=Path(args.proof_holes).resolve() if str(args.proof_holes).strip() else None,
        bridge_packets_path=Path(args.bridge_packets).resolve() if str(args.bridge_packets).strip() else None,
        alignment_packets_path=Path(args.alignment_packets).resolve() if str(args.alignment_packets).strip() else None,
        out_jsonl=Path(args.out).resolve(),
        json_out=Path(args.json_out).resolve(),
        md_out=Path(args.md_out).resolve() if str(args.md_out).strip() else None,
        top_n=max(0, int(args.top_n)),
    )
    print(f"Critic packets written: {report['output_jsonl']} (packets={report['packet_count']})")
    if report.get("output_md"):
        print(f"Critic report markdown written: {report['output_md']}")
    print(f"Operation report written: {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
