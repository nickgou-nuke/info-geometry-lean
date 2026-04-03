#!/usr/bin/env python3
"""Planning-only vacuity planner skeleton.

This tool aggregates read-only compiler bridge payloads, vacuity reports,
dependency metadata, and ownership metadata to produce ranked planning outputs:

- ranked vacuity candidates
- ranked owner candidates
- ranked replacement candidates

Boundary:
- no mutation surface
- no automatic replacement
- no proof repair
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, cast
from urllib.parse import unquote, urlparse

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


JsonObj = dict[str, Any]


HEAD_SOURCE_WEIGHT = {
    "exprSemantic": 1.00,
    "textHeuristic": 0.55,
    "unavailable": 0.20,
}

DIAG_PROVENANCE_WEIGHT = {
    "leanTag": 1.00,
    "messagePattern": 0.75,
    "bridgeRule": 0.60,
    "fallback": 0.40,
}

VIOLATION_LEVEL_WEIGHT = {
    "error": 1.00,
    "warning": 0.70,
    "info": 0.45,
}

VACUITY_TAGS = {
    "wrapper-candidate",
    "dead-candidate",
    "rfl-like",
    "proof-infrastructure",
}


@dataclass
class Signal:
    name: str
    contribution: float
    reliability: float
    evidence: str


@dataclass
class RankedEntry:
    key: str
    score: float
    confidence: float
    payload: dict[str, Any]


def clamp01(x: float) -> float:
    if x < 0.0:
        return 0.0
    if x > 1.0:
        return 1.0
    return x


def safe_mean(values: list[float], default: float = 0.0) -> float:
    if not values:
        return default
    return sum(values) / len(values)


def relpath_or_self(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except Exception:
        return str(path)


def parse_uri_or_path(value: str | None, root: Path) -> str | None:
    if not value:
        return None
    if value.startswith("file://"):
        parsed = urlparse(value)
        fs_path = Path(unquote(parsed.path))
        return relpath_or_self(fs_path, root)
    path = Path(value)
    if path.is_absolute():
        return relpath_or_self(path, root)
    return str(path)


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_jsonl(path: Path) -> list[JsonObj]:
    rows: list[JsonObj] = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            rows.append(cast(JsonObj, json.loads(s)))
    return rows


def resolve_existing(*paths: Path) -> Path | None:
    for p in paths:
        if p.exists():
            return p
    return None


def load_decl_index(path: Path) -> dict[str, JsonObj]:
    out: dict[str, JsonObj] = {}
    for row in load_jsonl(path):
        out[row["name"]] = row
    return out


def load_edges(path: Path) -> tuple[dict[str, list[tuple[str, str]]], dict[str, list[tuple[str, str]]]]:
    forward: dict[str, list[tuple[str, str]]] = defaultdict(list)
    reverse: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for row in load_jsonl(path):
        src = row.get("src")
        dst = row.get("dst")
        kind = row.get("kind", "value")
        if not src or not dst:
            continue
        forward[src].append((dst, kind))
        reverse[dst].append((src, kind))
    return dict(forward), dict(reverse)


def load_module_regions(path: Path, root: Path) -> tuple[dict[str, str], dict[str, str]]:
    raw = load_json(path)
    module_to_region: dict[str, str] = {}
    file_to_region: dict[str, str] = {}
    for node in raw.get("nodes", []):
        module = node.get("id")
        region = node.get("region", "unknown")
        path_str = node.get("path")
        if module:
            module_to_region[module] = region
        if path_str:
            rel = parse_uri_or_path(path_str, root)
            if rel:
                file_to_region[rel] = region
    return module_to_region, file_to_region


def load_owner_index(path: Path) -> list[JsonObj]:
    raw = load_json(path)
    entries: list[JsonObj] = []
    for row in raw.get("files", []):
        if row.get("kind") == "owner":
            entries.append(row)
    return entries


def load_proof_hole_counts(path: Path) -> dict[str, int]:
    out: dict[str, int] = {}
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            parts = s.split("\t")
            if len(parts) < 2:
                continue
            try:
                count = int(parts[0].strip())
            except ValueError:
                continue
            out[parts[1].strip()] = count
    return out


def source_weight(source: str | None) -> float:
    return HEAD_SOURCE_WEIGHT.get(source or "unavailable", HEAD_SOURCE_WEIGHT["unavailable"])


def diag_weight(diag_provs: list[str]) -> float:
    if not diag_provs:
        return DIAG_PROVENANCE_WEIGHT["fallback"]
    vals = [DIAG_PROVENANCE_WEIGHT.get(p, DIAG_PROVENANCE_WEIGHT["fallback"]) for p in diag_provs]
    return safe_mean(vals, default=DIAG_PROVENANCE_WEIGHT["fallback"])


def summarize_signals(signals: list[Signal]) -> tuple[float, float, list[JsonObj]]:
    if not signals:
        return 0.0, 0.0, []
    score = clamp01(sum(max(0.0, s.contribution) for s in signals))
    denom = sum(abs(s.contribution) for s in signals)
    confidence = 0.0
    if denom > 0:
        confidence = clamp01(sum(abs(s.contribution) * s.reliability for s in signals) / denom)
    provenance: list[JsonObj] = [
        {
            "signal": s.name,
            "contribution": round(s.contribution, 4),
            "reliability": round(s.reliability, 4),
            "evidence": s.evidence,
        }
        for s in signals
    ]
    return score, confidence, provenance


def collect_bridge_json_paths(raw_inputs: list[str], root: Path) -> list[Path]:
    candidates: list[Path] = []
    seen: set[Path] = set()

    def add_file(p: Path) -> None:
        q = p.resolve()
        if q in seen:
            return
        seen.add(q)
        candidates.append(q)

    def collect_from_path(p: Path) -> None:
        if p.is_file() and p.suffix == ".json":
            add_file(p)
            return
        if p.is_dir():
            for child in sorted(p.rglob("*.json")):
                add_file(child)

    if raw_inputs:
        for item in raw_inputs:
            if any(ch in item for ch in "*?[]"):
                for match in sorted(root.glob(item)):
                    collect_from_path(match)
                continue
            resolved = normalize_user_path(item, root / item)
            collect_from_path(resolved)
        return candidates

    auto_dirs = [
        root / ".artifacts" / "ci" / "compiler_bridge_smoke",
        root / "reports" / "vacuity",
    ]
    auto_files = [
        root / "reports" / "bridge_payload_demo.json",
        root / "reports" / "vacuity" / "bridge_payload_demo.json",
    ]
    for d in auto_dirs:
        collect_from_path(d)
    for f in auto_files:
        collect_from_path(f)
    return candidates


def extract_bridge_payload_objects(data: Any) -> list[JsonObj]:
    found: list[JsonObj] = []

    def visit(node: Any) -> None:
        if isinstance(node, dict):
            node_dict = cast(JsonObj, node)
            if isinstance(node_dict.get("goals"), list) and isinstance(node_dict.get("diagnostics", []), list):
                found.append(node_dict)
            for key in ("result", "payload", "data", "entries", "responses"):
                if key in node_dict:
                    visit(node_dict[key])
        elif isinstance(node, list):
            for item in cast(list[Any], node):
                visit(item)

    visit(data)
    return found


def observe_bridge_payload(
    payload: JsonObj,
    payload_path: Path,
    root: Path,
) -> list[JsonObj]:
    response_meta = payload.get("responseMeta", {})
    session = response_meta.get("sessionId", {}).get("value")
    source_file = parse_uri_or_path(session, root)

    diag_provs: list[str] = []
    for diag_any in payload.get("diagnostics", []):
        if isinstance(diag_any, dict):
            diag = cast(JsonObj, diag_any)
            prov = diag.get("classificationProvenance")
            if isinstance(prov, str):
                diag_provs.append(prov)

    out: list[JsonObj] = []
    for goal_any in payload.get("goals", []):
        if not isinstance(goal_any, dict):
            continue
        goal = cast(JsonObj, goal_any)
        out.append(
            {
                "payloadFile": relpath_or_self(payload_path, root),
                "sourceFile": source_file,
                "surface": "target",
                "head": goal.get("targetHead"),
                "headSource": goal.get("targetHeadSource", "unavailable"),
                "fingerprint": goal.get("targetHeadFingerprint"),
                "diagnosticProvenance": diag_provs,
            }
        )
        for local_any in goal.get("locals", []):
            if not isinstance(local_any, dict):
                continue
            local = cast(JsonObj, local_any)
            out.append(
                {
                    "payloadFile": relpath_or_self(payload_path, root),
                    "sourceFile": source_file,
                    "surface": "local",
                    "head": local.get("typeHead"),
                    "headSource": local.get("typeHeadSource", "unavailable"),
                    "fingerprint": local.get("typeHeadFingerprint"),
                    "diagnosticProvenance": diag_provs,
                }
            )
    return out


def normalize_bridge_observations(observations: list[JsonObj]) -> tuple[JsonObj, dict[str, JsonObj]]:
    semantic_groups: dict[tuple[str, str], JsonObj] = {}
    fingerprint_groups: dict[tuple[str, str], JsonObj] = {}
    file_signals: dict[str, JsonObj] = defaultdict(
        lambda: {"semanticCount": 0, "fingerprintCount": 0, "confSamples": []}
    )

    for obs in observations:
        surface = str(obs.get("surface") or "unknown")
        head = obs.get("head")
        source = str(obs.get("headSource") or "unavailable")
        fingerprint = obs.get("fingerprint")
        source_file = obs.get("sourceFile")
        diag_provs = [str(p) for p in obs.get("diagnosticProvenance", [])]

        s_weight = source_weight(source)
        d_weight = diag_weight(diag_provs)
        obs_conf = clamp01(0.7 * s_weight + 0.3 * d_weight)

        if source_file:
            fstats = file_signals[source_file]
            fstats["confSamples"].append(obs_conf)
            if source == "exprSemantic" and head:
                fstats["semanticCount"] += 1
            if source == "exprSemantic" and fingerprint:
                fstats["fingerprintCount"] += 1

        if source == "exprSemantic" and isinstance(head, str) and head:
            gkey = (surface, head)
            group = semantic_groups.setdefault(
                gkey,
                {
                    "surface": surface,
                    "head": head,
                    "count": 0,
                    "files": set(),
                    "fingerprints": Counter(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                },
            )
            group["count"] += 1
            if source_file:
                group["files"].add(source_file)
            if isinstance(fingerprint, str) and fingerprint:
                group["fingerprints"][fingerprint] += 1
            for prov in diag_provs:
                group["diagProvenance"][prov] += 1
            group["confSamples"].append(obs_conf)

        if source == "exprSemantic" and isinstance(fingerprint, str) and fingerprint:
            fkey = (surface, fingerprint)
            group2 = fingerprint_groups.setdefault(
                fkey,
                {
                    "surface": surface,
                    "fingerprint": fingerprint,
                    "count": 0,
                    "heads": Counter(),
                    "files": set(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                },
            )
            group2["count"] += 1
            if isinstance(head, str) and head:
                group2["heads"][head] += 1
            if source_file:
                group2["files"].add(source_file)
            for prov in diag_provs:
                group2["diagProvenance"][prov] += 1
            group2["confSamples"].append(obs_conf)

    semantic_out: list[JsonObj] = []
    for group in semantic_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        semantic_out.append(
            {
                "surface": group["surface"],
                "head": group["head"],
                "count": group["count"],
                "files": sorted(group["files"]),
                "fingerprints": group["fingerprints"].most_common(),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    fingerprint_out: list[JsonObj] = []
    for group in fingerprint_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        fingerprint_out.append(
            {
                "surface": group["surface"],
                "fingerprint": group["fingerprint"],
                "count": group["count"],
                "heads": group["heads"].most_common(),
                "files": sorted(group["files"]),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    semantic_out.sort(key=lambda x: (-x["count"], -x["groupConfidence"], x["surface"], x["head"]))
    fingerprint_out.sort(key=lambda x: (-x["count"], -x["groupConfidence"], x["surface"], x["fingerprint"]))

    file_signal_out: dict[str, JsonObj] = {}
    for fpath, stats in file_signals.items():
        file_signal_out[fpath] = {
            "semanticCount": stats["semanticCount"],
            "fingerprintCount": stats["fingerprintCount"],
            "avgConfidence": round(safe_mean(stats["confSamples"], default=0.0), 4),
        }

    summary: JsonObj = {
        "payloadObservationCount": len(observations),
        "semanticHeadGroupCount": len(semantic_out),
        "fingerprintGroupCount": len(fingerprint_out),
        "semanticHeadGroups": semantic_out,
        "fingerprintGroups": fingerprint_out,
    }
    return summary, file_signal_out


def file_domain(file_path: str | None) -> str | None:
    if not file_path:
        return None
    parts = Path(file_path).parts
    if len(parts) >= 3 and parts[0] == "lean" and parts[1] == "InfoGeometry":
        return parts[2]
    return None


def rank_vacuity_candidates(
    theorem_entries: list[JsonObj],
    module_region: dict[str, str],
    file_region: dict[str, str],
    hole_counts: dict[str, int],
    bridge_file_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    ranked: list[RankedEntry] = []

    for row in theorem_entries:
        if row.get("kind") != "theorem":
            continue
        tags = set(row.get("tags") or [])
        raw_violations = row.get("violations")
        violations = raw_violations if isinstance(raw_violations, list) else []
        if not (tags & VACUITY_TAGS or violations):
            continue

        name = str(row.get("name") or "")
        if not name:
            continue

        file_path = row.get("file") if isinstance(row.get("file"), str) else None
        module = row.get("module") if isinstance(row.get("module"), str) else None
        if module:
            region = module_region.get(module, file_region.get(file_path or "", "unknown"))
        else:
            region = file_region.get(file_path or "", "unknown")

        signals: list[Signal] = []

        if "wrapper-candidate" in tags:
            signals.append(Signal("tag.wrapper-candidate", 0.34, 0.82, "wrapper-candidate"))
        if "dead-candidate" in tags:
            signals.append(Signal("tag.dead-candidate", 0.28, 0.84, "dead-candidate"))
        if "rfl-like" in tags:
            signals.append(Signal("tag.rfl-like", 0.18, 0.74, "rfl-like"))
        if "proof-infrastructure" in tags:
            signals.append(Signal("tag.proof-infrastructure", 0.10, 0.72, "proof-infrastructure"))

        levels: list[str] = []
        for violation_any in violations:
            if isinstance(violation_any, dict):
                violation = cast(JsonObj, violation_any)
                level = violation.get("level")
                if isinstance(level, str):
                    levels.append(level)
        if "error" in levels:
            signals.append(Signal("violation.error", 0.20, VIOLATION_LEVEL_WEIGHT["error"], "error-level violation present"))
        elif "warning" in levels:
            signals.append(Signal("violation.warning", 0.12, VIOLATION_LEVEL_WEIGHT["warning"], "warning-level violation present"))

        if int(row.get("reverse_type", 0)) == 0:
            signals.append(Signal("graph.zero-reverse-type", 0.06, 0.70, "reverse_type = 0"))
        if int(row.get("reverse_value", 0)) == 0:
            signals.append(Signal("graph.zero-reverse-value", 0.05, 0.68, "reverse_value = 0"))
        if bool(row.get("is_sink", False)):
            signals.append(Signal("graph.sink", 0.03, 0.62, "is_sink = true"))

        if isinstance(file_path, str):
            hole_count = hole_counts.get(file_path, 0)
            if hole_count > 0:
                hole_boost = min(0.18, 0.04 * hole_count)
                signals.append(
                    Signal(
                        "proof-holes.by-file",
                        hole_boost,
                        0.88,
                        f"explicit proof holes in file: {hole_count}",
                    )
                )

            bridge = bridge_file_signals.get(file_path)
            if bridge:
                sem_count = int(bridge.get("semanticCount", 0))
                fp_count = int(bridge.get("fingerprintCount", 0))
                bridge_conf = float(bridge.get("avgConfidence", 0.0))
                if sem_count > 0:
                    sem_boost = 0.11 * min(1.0, sem_count / 3.0)
                    signals.append(
                        Signal(
                            "bridge.semantic-head-overlap",
                            sem_boost,
                            clamp01(bridge_conf),
                            f"semantic observations in file: {sem_count}",
                        )
                    )
                if fp_count > 0:
                    fp_boost = 0.06 * min(1.0, fp_count / 3.0)
                    signals.append(
                        Signal(
                            "bridge.fingerprint-overlap",
                            fp_boost,
                            clamp01(bridge_conf),
                            f"fingerprint observations in file: {fp_count}",
                        )
                    )

        score, confidence, provenance = summarize_signals(signals)
        payload: JsonObj = {
            "name": name,
            "file": file_path,
            "module": module,
            "region": region,
            "tags": sorted(tags),
            "violations": violations,
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=name, score=score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_owner_candidates(
    vacuity_candidates: list[JsonObj],
    owner_entries: list[JsonObj],
    file_region: dict[str, str],
    top_k: int,
) -> list[JsonObj]:
    agg_score: dict[str, float] = defaultdict(float)
    agg_signals: dict[str, list[Signal]] = defaultdict(list)
    support: dict[str, set[str]] = defaultdict(set)

    owner_by_file: dict[str, JsonObj] = {str(e.get("file")): e for e in owner_entries if e.get("file")}

    for cand in vacuity_candidates:
        cand_name = str(cand.get("name"))
        cand_file = cand.get("file")
        cand_region = cand.get("region") or file_region.get(str(cand_file), "unknown")
        cand_domain = file_domain(str(cand_file) if isinstance(cand_file, str) else None)
        cand_score = float(cand.get("score", 0.0))

        for owner_file, owner in owner_by_file.items():
            owner_region = file_region.get(owner_file, "unknown")
            owner_domain = file_domain(owner_file)

            local_signals: list[Signal] = []
            if cand_file == owner_file:
                local_signals.append(Signal("owner.exact-file", 0.75 * cand_score, 0.95, f"{cand_name} is in owner file"))
            if cand_region != "unknown" and cand_region == owner_region:
                local_signals.append(Signal("owner.same-region", 0.35 * cand_score, 0.76, f"shared region: {cand_region}"))
            if cand_domain and owner_domain and cand_domain == owner_domain:
                local_signals.append(Signal("owner.same-domain", 0.20 * cand_score, 0.72, f"shared domain: {cand_domain}"))

            if not local_signals:
                continue

            base = sum(max(0.0, s.contribution) for s in local_signals)
            agg_score[owner_file] += base
            agg_signals[owner_file].extend(local_signals)
            support[owner_file].add(cand_name)

    ranked: list[RankedEntry] = []
    for owner_file, _score in agg_score.items():
        signals = agg_signals[owner_file]
        final_score, confidence, provenance = summarize_signals(signals)
        owner = owner_by_file[owner_file]
        payload: JsonObj = {
            "ownerFile": owner_file,
            "sourceDepth": owner.get("source_depth"),
            "targetDepth": owner.get("target_depth"),
            "notes": owner.get("notes", ""),
            "supportingVacuityCandidates": sorted(support[owner_file]),
            "score": round(final_score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=owner_file, score=final_score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_replacement_candidates(
    vacuity_candidates: list[JsonObj],
    forward_edges: dict[str, list[tuple[str, str]]],
    decls: dict[str, JsonObj],
    theorem_by_name: dict[str, JsonObj],
    file_region: dict[str, str],
    owner_candidates: list[JsonObj],
    top_k: int,
) -> list[JsonObj]:
    owner_by_region: dict[str, list[str]] = defaultdict(list)
    for owner in owner_candidates:
        owner_file = owner.get("ownerFile")
        if not isinstance(owner_file, str):
            continue
        reg = file_region.get(owner_file, "unknown")
        owner_by_region[reg].append(owner_file)

    agg_score: dict[str, float] = defaultdict(float)
    agg_signals: dict[str, list[Signal]] = defaultdict(list)
    support: dict[str, set[str]] = defaultdict(set)

    for cand in vacuity_candidates:
        src_name = str(cand.get("name") or "")
        src_file = cand.get("file")
        src_region = cand.get("region") or file_region.get(str(src_file), "unknown")
        src_score = float(cand.get("score", 0.0))
        if not src_name:
            continue

        for dst, edge_kind in forward_edges.get(src_name, []):
            decl = decls.get(dst)
            if not decl:
                continue

            dst_kind = str(decl.get("kind", ""))
            if dst_kind not in {"theorem", "def", "lemma", "abbrev"}:
                continue

            dst_file = parse_uri_or_path(decl.get("file"), repo_root())
            dst_region = file_region.get(dst_file or "", "unknown")

            signals: list[Signal] = []
            if edge_kind == "value":
                signals.append(Signal("edge.value", 0.55 * src_score, 0.84, f"value-edge from {src_name}"))
            else:
                signals.append(Signal("edge.type", 0.35 * src_score, 0.74, f"type-edge from {src_name}"))

            dst_meta = theorem_by_name.get(dst)
            if dst_meta:
                dst_tags = set(dst_meta.get("tags") or [])
                if "dead-candidate" in dst_tags:
                    signals.append(Signal("dst.dead-penalty", -0.12 * src_score, 0.86, "destination tagged dead-candidate"))
                elif "wrapper-candidate" in dst_tags:
                    signals.append(Signal("dst.wrapper-penalty", -0.08 * src_score, 0.80, "destination tagged wrapper-candidate"))
                elif "statement-bearing" in dst_tags:
                    signals.append(Signal("dst.statement-bearing", 0.14 * src_score, 0.78, "destination tagged statement-bearing"))

            if src_region != "unknown" and src_region == dst_region:
                signals.append(Signal("region.match", 0.06 * src_score, 0.70, f"shared region: {src_region}"))

            if owner_by_region.get(dst_region):
                signals.append(Signal("owner.corridor-present", 0.05 * src_score, 0.68, f"owner corridor in region {dst_region}"))

            if not signals:
                continue

            local_score = sum(s.contribution for s in signals)
            if local_score <= 0:
                continue

            agg_score[dst] += local_score
            agg_signals[dst].extend(signals)
            support[dst].add(src_name)

    ranked: list[RankedEntry] = []
    for dst, _score in agg_score.items():
        decl = decls[dst]
        dst_file = parse_uri_or_path(decl.get("file"), repo_root())
        dst_region = file_region.get(dst_file or "", "unknown")
        score_clamped, confidence, provenance = summarize_signals(agg_signals[dst])
        payload: JsonObj = {
            "replacementDecl": dst,
            "kind": decl.get("kind"),
            "file": dst_file,
            "module": decl.get("module"),
            "region": dst_region,
            "ownerCorridor": owner_by_region.get(dst_region, [])[:3],
            "supportingVacuityCandidates": sorted(support[dst]),
            "score": round(score_clamped, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=dst, score=score_clamped, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def make_markdown_report(report: JsonObj) -> str:
    lines: list[str] = []
    lines.append("# Vacuity Planner Report")
    lines.append("")
    lines.append("## Boundary")
    lines.append("")
    boundary = report.get("boundary", {})
    lines.append(f"- plannerMode: {boundary.get('plannerMode')}")
    lines.append(f"- mutationSurface: {boundary.get('mutationSurface')}")
    lines.append(f"- automaticReplacement: {boundary.get('automaticReplacement')}")
    lines.append(f"- proofRepair: {boundary.get('proofRepair')}")
    lines.append("")

    lines.append("## Input Coverage")
    lines.append("")
    inputs = report.get("inputs", {})
    lines.append(f"- theoremSignificanceEntries: {inputs.get('theoremSignificanceEntries', 0)}")
    lines.append(f"- declarationCount: {inputs.get('declarationCount', 0)}")
    lines.append(f"- edgeCount: {inputs.get('edgeCount', 0)}")
    lines.append(f"- ownerEntries: {inputs.get('ownerEntries', 0)}")
    lines.append(f"- bridgePayloadFiles: {inputs.get('bridgePayloadFiles', 0)}")
    lines.append(f"- bridgePayloadObjects: {inputs.get('bridgePayloadObjects', 0)}")
    lines.append("")

    norm = report.get("normalization", {})
    lines.append("## Normalization Snapshot")
    lines.append("")
    lines.append("### Top exprSemantic head groups")
    lines.append("")
    lines.append("| rank | surface | head | count | confidence |")
    lines.append("|---:|---|---|---:|---:|")
    for i, row in enumerate(norm.get("semanticHeadGroups", [])[:10], start=1):
        lines.append(
            f"| {i} | {row.get('surface')} | {row.get('head')} | {row.get('count')} | {row.get('groupConfidence')} |"
        )
    if not norm.get("semanticHeadGroups"):
        lines.append("| - | - | - | 0 | 0.0 |")
    lines.append("")

    lines.append("### Top fingerprint groups")
    lines.append("")
    lines.append("| rank | surface | fingerprint | count | confidence |")
    lines.append("|---:|---|---|---:|---:|")
    for i, row in enumerate(norm.get("fingerprintGroups", [])[:10], start=1):
        lines.append(
            f"| {i} | {row.get('surface')} | {row.get('fingerprint')} | {row.get('count')} | {row.get('groupConfidence')} |"
        )
    if not norm.get("fingerprintGroups"):
        lines.append("| - | - | - | 0 | 0.0 |")
    lines.append("")

    def emit_ranked_table(title: str, rows: list[JsonObj], cols: list[tuple[str, str]]) -> None:
        lines.append(f"## {title}")
        lines.append("")
        header = "| " + " | ".join(label for _, label in cols) + " |"
        sep = "|" + "|".join("---" for _ in cols) + "|"
        lines.append(header)
        lines.append(sep)
        for row in rows[:20]:
            values = [str(row.get(key, "")) for key, _ in cols]
            lines.append("| " + " | ".join(values) + " |")
        if not rows:
            lines.append("| - | - | - | - |")
        lines.append("")

    emit_ranked_table(
        "Ranked Vacuity Candidates",
        report.get("rankedVacuityCandidates", []),
        [("rank", "rank"), ("name", "declaration"), ("score", "score"), ("confidence", "confidence")],
    )
    emit_ranked_table(
        "Ranked Owner Candidates",
        report.get("rankedOwnerCandidates", []),
        [("rank", "rank"), ("ownerFile", "ownerFile"), ("score", "score"), ("confidence", "confidence")],
    )
    emit_ranked_table(
        "Ranked Replacement Candidates",
        report.get("rankedReplacementCandidates", []),
        [("rank", "rank"), ("replacementDecl", "replacementDecl"), ("score", "score"), ("confidence", "confidence")],
    )

    lines.append("## Confidence Provenance Weights")
    lines.append("")
    lines.append("- headSourceWeight: " + json.dumps(HEAD_SOURCE_WEIGHT, sort_keys=True))
    lines.append("- diagnosticProvenanceWeight: " + json.dumps(DIAG_PROVENANCE_WEIGHT, sort_keys=True))
    lines.append("- violationLevelWeight: " + json.dumps(VIOLATION_LEVEL_WEIGHT, sort_keys=True))
    lines.append("")

    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    root = repo_root()

    parser = argparse.ArgumentParser(description="Planning-only vacuity planner skeleton")
    parser.add_argument("--bridge-input", action="append", default=[], help="JSON file/dir/glob with bridge payload data")
    parser.add_argument(
        "--theorem-significance",
        type=Path,
        default=root / "reports" / "theorem-significance.json",
        help="JSON report from tools/theorem_significance.py",
    )
    parser.add_argument(
        "--decls",
        type=Path,
        default=resolve_existing(
            root / "index" / "decls.jsonl",
            root / "artifacts" / "dag" / "index" / "decls.jsonl",
            root / ".build" / "index" / "decls.jsonl",
        )
        or (root / "index" / "decls.jsonl"),
        help="Declaration metadata JSONL",
    )
    parser.add_argument(
        "--edges",
        type=Path,
        default=resolve_existing(
            root / "index" / "edges.jsonl",
            root / "artifacts" / "dag" / "index" / "edges.jsonl",
            root / ".build" / "index" / "edges.jsonl",
        )
        or (root / "index" / "edges.jsonl"),
        help="Dependency edge metadata JSONL",
    )
    parser.add_argument(
        "--module-graph",
        type=Path,
        default=root / "docs-map" / "module_graph.json",
        help="Module graph JSON",
    )
    parser.add_argument(
        "--owner-index",
        type=Path,
        default=root / "reports" / "dag" / "representation-depth-index.json",
        help="Ownership index JSON",
    )
    parser.add_argument(
        "--proof-holes-by-file",
        type=Path,
        default=root / "reports" / "vacuity" / "wholecode-explicit-proof-holes-20260309.by-file.txt",
        help="Optional proof-hole count by file",
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=root / "reports" / "vacuity-planner.json",
        help="Planner JSON output",
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=root / "reports" / "vacuity-planner.md",
        help="Planner Markdown output",
    )
    parser.add_argument("--top-k", type=int, default=50, help="Maximum rows per ranked output")
    return parser.parse_args()


def main() -> None:
    root = repo_root()
    args = parse_args()

    theorem_significance_path = normalize_user_path(str(args.theorem_significance), args.theorem_significance)
    decls_path = normalize_user_path(str(args.decls), args.decls)
    edges_path = normalize_user_path(str(args.edges), args.edges)
    module_graph_path = normalize_user_path(str(args.module_graph), args.module_graph)
    owner_index_path = normalize_user_path(str(args.owner_index), args.owner_index)
    proof_holes_path = normalize_user_path(str(args.proof_holes_by_file), args.proof_holes_by_file)
    out_json_path = normalize_user_path(str(args.out_json), args.out_json)
    out_md_path = normalize_user_path(str(args.out_md), args.out_md)

    theorem_entries_raw = load_json(theorem_significance_path)
    if not isinstance(theorem_entries_raw, list):
        raise RuntimeError(f"Expected list in theorem significance report: {theorem_significance_path}")
    theorem_entries: list[JsonObj] = [cast(JsonObj, row) for row in theorem_entries_raw if isinstance(row, dict)]

    decls = load_decl_index(decls_path)
    forward_edges, _ = load_edges(edges_path)
    module_region, file_region = load_module_regions(module_graph_path, root)
    owner_entries = load_owner_index(owner_index_path)

    hole_counts: dict[str, int] = {}
    if proof_holes_path.exists():
        hole_counts = load_proof_hole_counts(proof_holes_path)

    bridge_json_paths = collect_bridge_json_paths(args.bridge_input, root)
    bridge_payload_count = 0
    observations: list[JsonObj] = []
    for p in bridge_json_paths:
        try:
            parsed = load_json(p)
        except Exception:
            continue
        payloads = extract_bridge_payload_objects(parsed)
        bridge_payload_count += len(payloads)
        for payload in payloads:
            observations.extend(observe_bridge_payload(payload, p, root))

    normalization, bridge_file_signals = normalize_bridge_observations(observations)

    theorem_by_name = {
        str(row.get("name")): row for row in theorem_entries if isinstance(row, dict) and row.get("name")
    }

    vacuity_candidates = rank_vacuity_candidates(
        theorem_entries=theorem_entries,
        module_region=module_region,
        file_region=file_region,
        hole_counts=hole_counts,
        bridge_file_signals=bridge_file_signals,
        top_k=args.top_k,
    )

    owner_candidates = rank_owner_candidates(
        vacuity_candidates=vacuity_candidates,
        owner_entries=owner_entries,
        file_region=file_region,
        top_k=args.top_k,
    )

    replacement_candidates = rank_replacement_candidates(
        vacuity_candidates=vacuity_candidates,
        forward_edges=forward_edges,
        decls=decls,
        theorem_by_name=theorem_by_name,
        file_region=file_region,
        owner_candidates=owner_candidates,
        top_k=args.top_k,
    )

    report: JsonObj = {
        "schema": "ig.vacuity-planner.v0",
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "boundary": {
            "plannerMode": "planning-only",
            "mutationSurface": False,
            "automaticReplacement": False,
            "proofRepair": False,
        },
        "inputs": {
            "theoremSignificancePath": relpath_or_self(theorem_significance_path, root),
            "declsPath": relpath_or_self(decls_path, root),
            "edgesPath": relpath_or_self(edges_path, root),
            "moduleGraphPath": relpath_or_self(module_graph_path, root),
            "ownerIndexPath": relpath_or_self(owner_index_path, root),
            "proofHolesByFilePath": relpath_or_self(proof_holes_path, root) if proof_holes_path.exists() else None,
            "bridgeInputPaths": [relpath_or_self(p, root) for p in bridge_json_paths],
            "theoremSignificanceEntries": len(theorem_entries),
            "declarationCount": len(decls),
            "edgeCount": sum(len(v) for v in forward_edges.values()),
            "ownerEntries": len(owner_entries),
            "bridgePayloadFiles": len(bridge_json_paths),
            "bridgePayloadObjects": bridge_payload_count,
        },
        "normalization": normalization,
        "rankedVacuityCandidates": vacuity_candidates,
        "rankedOwnerCandidates": owner_candidates,
        "rankedReplacementCandidates": replacement_candidates,
        "confidenceWeights": {
            "headSource": HEAD_SOURCE_WEIGHT,
            "diagnosticProvenance": DIAG_PROVENANCE_WEIGHT,
            "violationLevel": VIOLATION_LEVEL_WEIGHT,
        },
    }

    out_json_path.parent.mkdir(parents=True, exist_ok=True)
    with out_json_path.open("w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    out_md_path.parent.mkdir(parents=True, exist_ok=True)
    with out_md_path.open("w", encoding="utf-8") as f:
        f.write(make_markdown_report(report))

    print(f"[vacuity-planner] JSON report -> {out_json_path}")
    print(f"[vacuity-planner] Markdown report -> {out_md_path}")
    print(
        "[vacuity-planner] summary: "
        f"vacuity={len(vacuity_candidates)}, "
        f"owners={len(owner_candidates)}, "
        f"replacements={len(replacement_candidates)}, "
        f"bridge_payloads={bridge_payload_count}"
    )


if __name__ == "__main__":
    main()
