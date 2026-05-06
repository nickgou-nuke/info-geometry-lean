#!/usr/bin/env python3
"""Run side-effect-free LLM ensemble infusion over a compressed cone packet.

Input:
  info_geometry.epistemic_reactor.compressed_cone.v1

Outputs:
  - ensemble_samples.jsonl
  - ensemble_consensus.json

This script does not write to ArangoDB and does not promote claims.  It only
turns SCC-compressed context into proposal samples and a consensus summary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any
from urllib.request import Request, urlopen


SAMPLE_SCHEMA = "info_geometry.epistemic_reactor.ensemble_sample.v1"
CONSENSUS_SCHEMA = "info_geometry.epistemic_reactor.ensemble_consensus.v1"

AUTHORITY_BOUNDARY = {
    "ensemble_samples_are_not_proofs": True,
    "consensus_is_not_truth": True,
    "packet_is_side_effect_free": True,
    "lean_remains_proof_authority": True,
    "audits_remain_admission_authority": True,
}

FORBIDDEN_AUTHORITY_CLAIMS = [
    "ensemble_consensus_is_truth",
    "hive_purified_is_admitted",
    "graph_is_proof",
    "sample_is_proof",
    "proposal_is_lean_checked",
]


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def stable_hash(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit(f"expected JSON object packet: {path}")
    return data


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(canonical_json(row) + "\n")


def parse_temperatures(raw: str | None, packet: dict[str, Any]) -> list[float]:
    if raw:
        values = [float(piece.strip()) for piece in raw.split(",") if piece.strip()]
    else:
        sampling = packet.get("ensemble_payload", {}).get("sampling", {})
        values = [float(value) for value in sampling.get("temperatures", [0.0, 0.2, 0.5, 0.8])]
    if not values:
        raise SystemExit("no temperatures supplied")
    return values


def samples_per_temperature(raw: int | None, packet: dict[str, Any]) -> int:
    if raw is not None:
        return raw
    sampling = packet.get("ensemble_payload", {}).get("sampling", {})
    value = int(sampling.get("samples", 1))
    return max(1, value)


def consensus_threshold(raw: float | None, packet: dict[str, Any]) -> float:
    if raw is not None:
        return raw
    sampling = packet.get("ensemble_payload", {}).get("sampling", {})
    return float(sampling.get("consensus_threshold", 0.9))


def compact_context(packet: dict[str, Any], *, max_components: int, max_edges: int, max_excerpts: int) -> dict[str, Any]:
    return {
        "target_decl": packet.get("target_decl"),
        "apex": packet.get("apex"),
        "compressed_components": (packet.get("compressed_components") or [])[:max_components],
        "compressed_edges": (packet.get("compressed_edges") or [])[:max_edges],
        "source_excerpts": (packet.get("source_excerpts") or [])[:max_excerpts],
        "forbidden_authority_claims": packet.get("forbidden_authority_claims") or FORBIDDEN_AUTHORITY_CLAIMS,
        "authority_boundary": packet.get("authority_boundary") or AUTHORITY_BOUNDARY,
    }


def render_prompt(context: dict[str, Any]) -> str:
    return (
        "You are a Lean theorem-factory proposal worker.\n"
        "You will receive SCC-compressed graph context and raw Lean excerpts.\n"
        "Return only JSON: an array of candidate proposal objects.\n"
        "Each object must have keys: kind, claim, lean_owner_candidates, source_refs, risk, required_descent.\n"
        "Allowed kind values: owner_map, lemma_candidate, hypothesis_packet, guard, reject.\n"
        "Authority rule: do not claim proof, admission, or Lean verification.\n"
        "Every candidate must name raw Lean/source evidence when possible.\n\n"
        f"CONTEXT:\n{json.dumps(context, indent=2, ensure_ascii=False)}"
    )


def normalize_claim(text: str) -> str:
    text = re.sub(r"\s+", " ", text.strip().lower())
    text = re.sub(r"[^a-z0-9_ .:/+-]+", "", text)
    return text[:240]


def candidate_key(candidate: dict[str, Any]) -> str:
    return stable_hash(
        {
            "kind": str(candidate.get("kind") or "proposal").lower(),
            "claim": normalize_claim(str(candidate.get("claim") or "")),
        }
    )


def edge_component_key(value: Any) -> str:
    text = str(value or "")
    if "/" in text:
        return text.split("/", 1)[-1]
    return text


def heuristic_candidates(packet: dict[str, Any], *, limit: int = 12) -> list[dict[str, Any]]:
    edges = list(packet.get("compressed_edges") or [])
    edges.sort(
        key=lambda row: (
            int(row.get("source_multiplicity") or 0) + int(row.get("multiplicity") or 0),
            float(row.get("witness_count") or 0),
        ),
        reverse=True,
    )
    components_by_id = {
        str(row.get("id") or ""): row
        for row in packet.get("compressed_components") or []
        if row.get("id")
    }
    candidates: list[dict[str, Any]] = []
    for edge in edges[:limit]:
        src_id = str(edge.get("from") or "")
        dst_id = str(edge.get("to") or "")
        src = components_by_id.get(src_id, {})
        dst = components_by_id.get(dst_id, {})
        src_name = src.get("representative") or edge_component_key(src_id)
        dst_name = dst.get("representative") or edge_component_key(dst_id)
        multiplicity = int(edge.get("source_multiplicity") or edge.get("multiplicity") or 1)
        kind = "lemma_candidate" if multiplicity >= 2 else "owner_map"
        candidates.append(
            {
                "kind": kind,
                "claim": f"{src_name} has compressed dependency/correlation edge to {dst_name}",
                "lean_owner_candidates": [str(src_name), str(dst_name)],
                "source_refs": [src_id, dst_id],
                "risk": "proposal",
                "required_descent": "raw_lean_witness",
                "edge_multiplicity": multiplicity,
            }
        )
    if not candidates:
        candidates.append(
            {
                "kind": "reject",
                "claim": "No compressed edge evidence was available for proposal generation",
                "lean_owner_candidates": [],
                "source_refs": [],
                "risk": "unsupported",
                "required_descent": "raw_lean_witness",
            }
        )
    return candidates


def parse_llm_candidates(raw: str) -> list[dict[str, Any]]:
    match = re.search(r"\[[\s\S]*\]", raw)
    if match:
        raw = match.group(0)
    parsed = json.loads(raw)
    if not isinstance(parsed, list):
        raise ValueError("LLM response was not a JSON array")
    candidates: list[dict[str, Any]] = []
    for item in parsed:
        if not isinstance(item, dict):
            continue
        claim = str(item.get("claim") or "").strip()
        if not claim:
            continue
        candidates.append(
            {
                "kind": str(item.get("kind") or "proposal"),
                "claim": claim,
                "lean_owner_candidates": item.get("lean_owner_candidates") if isinstance(item.get("lean_owner_candidates"), list) else [],
                "source_refs": item.get("source_refs") if isinstance(item.get("source_refs"), list) else [],
                "risk": str(item.get("risk") or "proposal"),
                "required_descent": str(item.get("required_descent") or "raw_lean_witness"),
            }
        )
    return candidates


def openai_compatible_candidates(
    *,
    prompt: str,
    endpoint: str,
    model: str,
    temperature: float,
    timeout: float,
) -> tuple[list[dict[str, Any]], str]:
    body = {
        "model": model,
        "messages": [
            {"role": "system", "content": "Return only JSON. Do not claim proof authority."},
            {"role": "user", "content": prompt},
        ],
        "temperature": temperature,
        "max_tokens": 8192,
    }
    req = Request(endpoint.rstrip("/") + "/chat/completions", data=json.dumps(body).encode("utf-8"))
    req.add_header("Content-Type", "application/json")
    with urlopen(req, timeout=timeout) as resp:
        payload = json.loads(resp.read().decode("utf-8"))
    raw = str(((payload.get("choices") or [{}])[0].get("message") or {}).get("content") or "")
    return parse_llm_candidates(raw), raw


def sample_once(
    *,
    packet: dict[str, Any],
    prompt: str,
    source_packet_id: str,
    sample_index: int,
    temperature: float,
    mode: str,
    endpoint: str,
    model: str,
    timeout: float,
    heuristic_limit: int,
) -> dict[str, Any]:
    generator = mode
    raw_response = None
    error = None
    fallback_reason = None
    try:
        if mode == "heuristic":
            candidates = heuristic_candidates(packet, limit=heuristic_limit)
        elif mode == "openai-compatible":
            candidates, raw_response = openai_compatible_candidates(
                prompt=prompt,
                endpoint=endpoint,
                model=model,
                temperature=temperature,
                timeout=timeout,
            )
        elif mode == "auto":
            try:
                candidates, raw_response = openai_compatible_candidates(
                    prompt=prompt,
                    endpoint=endpoint,
                    model=model,
                    temperature=temperature,
                    timeout=timeout,
                )
                generator = "openai-compatible"
            except Exception as exc:  # noqa: BLE001
                fallback_reason = str(exc)
                candidates = heuristic_candidates(packet, limit=heuristic_limit)
                generator = "heuristic"
        else:
            raise ValueError(f"unknown mode: {mode}")
        status = "ok"
    except Exception as exc:  # noqa: BLE001
        candidates = []
        status = "error"
        error = str(exc)
    row = {
        "schema": SAMPLE_SCHEMA,
        "id": "",
        "source_packet_id": source_packet_id,
        "authority": "proposal",
        "sample_index": sample_index,
        "temperature": temperature,
        "generator": generator,
        "status": status,
        "fallback_reason": fallback_reason,
        "error": error,
        "candidates": candidates,
        "raw_response": raw_response,
        "forbidden_authority_claims": list(FORBIDDEN_AUTHORITY_CLAIMS),
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }
    row["id"] = stable_hash(row)
    return row


def build_consensus(
    *,
    source_packet: dict[str, Any],
    source_packet_id: str,
    samples: list[dict[str, Any]],
    threshold: float,
) -> dict[str, Any]:
    total_ok = sum(1 for sample in samples if sample.get("status") == "ok")
    counts: Counter[str] = Counter()
    representatives: dict[str, dict[str, Any]] = {}
    support_samples: dict[str, list[str]] = defaultdict(list)
    for sample in samples:
        if sample.get("status") != "ok":
            continue
        seen_in_sample: set[str] = set()
        for candidate in sample.get("candidates") or []:
            if not isinstance(candidate, dict):
                continue
            key = candidate_key(candidate)
            if key in seen_in_sample:
                continue
            seen_in_sample.add(key)
            counts[key] += 1
            representatives.setdefault(key, candidate)
            support_samples[key].append(str(sample.get("id")))

    consensus_items: list[dict[str, Any]] = []
    for key, count in counts.most_common():
        support = 0.0 if total_ok == 0 else count / total_ok
        if support < threshold:
            continue
        item = dict(representatives[key])
        item.update(
            {
                "consensus_key": key,
                "support_count": count,
                "support_fraction": support,
                "support_sample_ids": support_samples[key],
                "authority": "proposal",
                "required_descent": item.get("required_descent") or "raw_lean_witness",
            }
        )
        consensus_items.append(item)

    return {
        "schema": CONSENSUS_SCHEMA,
        "id": "",
        "source_packet_id": source_packet_id,
        "target_decl": source_packet.get("target_decl"),
        "authority": "proposal",
        "threshold": threshold,
        "sample_count": len(samples),
        "ok_sample_count": total_ok,
        "error_sample_count": len(samples) - total_ok,
        "fallback_count": sum(1 for sample in samples if sample.get("fallback_reason")),
        "consensus_items": consensus_items,
        "non_consensus_candidate_count": max(0, len(counts) - len(consensus_items)),
        "forbidden_authority_claims": list(FORBIDDEN_AUTHORITY_CLAIMS),
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Compressed cone JSON packet")
    parser.add_argument("--samples-out", type=Path, required=True)
    parser.add_argument("--consensus-out", type=Path, required=True)
    parser.add_argument("--prompt-out", type=Path)
    parser.add_argument("--mode", default="auto", choices=["auto", "heuristic", "openai-compatible"])
    parser.add_argument("--endpoint", default="http://localhost:11434/v1")
    parser.add_argument("--model", default="llama3.1:8b")
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--temperatures")
    parser.add_argument("--samples-per-temperature", type=int)
    parser.add_argument("--consensus-threshold", type=float)
    parser.add_argument("--max-components", type=int, default=80)
    parser.add_argument("--max-edges", type=int, default=120)
    parser.add_argument("--max-excerpts", type=int, default=40)
    parser.add_argument("--heuristic-limit", type=int, default=12)
    args = parser.parse_args(argv)

    packet = read_json(args.input)
    source_packet_id = str(packet.get("id") or stable_hash(packet))
    temperatures = parse_temperatures(args.temperatures, packet)
    per_temperature = samples_per_temperature(args.samples_per_temperature, packet)
    threshold = consensus_threshold(args.consensus_threshold, packet)
    if not (0 <= threshold <= 1):
        raise SystemExit("--consensus-threshold must be between 0 and 1")
    if per_temperature <= 0:
        raise SystemExit("--samples-per-temperature must be positive")

    context = compact_context(
        packet,
        max_components=args.max_components,
        max_edges=args.max_edges,
        max_excerpts=args.max_excerpts,
    )
    prompt = render_prompt(context)
    if args.prompt_out:
        args.prompt_out.parent.mkdir(parents=True, exist_ok=True)
        args.prompt_out.write_text(prompt, encoding="utf-8")

    samples: list[dict[str, Any]] = []
    sample_index = 0
    for temperature in temperatures:
        for _ in range(per_temperature):
            sample_index += 1
            samples.append(
                sample_once(
                    packet=packet,
                    prompt=prompt,
                    source_packet_id=source_packet_id,
                    sample_index=sample_index,
                    temperature=temperature,
                    mode=args.mode,
                    endpoint=args.endpoint,
                    model=args.model,
                    timeout=args.timeout,
                    heuristic_limit=args.heuristic_limit,
                )
            )

    consensus = build_consensus(
        source_packet=packet,
        source_packet_id=source_packet_id,
        samples=samples,
        threshold=threshold,
    )
    consensus["id"] = stable_hash(consensus)
    write_jsonl(args.samples_out, samples)
    write_json(args.consensus_out, consensus)
    print(json.dumps(consensus, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

