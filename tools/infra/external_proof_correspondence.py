#!/usr/bin/env python3
"""Derive Lean adapter/reconstruction plans from ExternalTheoremCandidatePacket batches.

This is a non-authoritative correspondence normalizer.  It turns harvested foreign theorem
intelligence into adapter-first Lean work items, but never marks anything as Lean-checked.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]


# [lossless-compact] read_jsonl folded into igf.common.json_io.read_jsonl
from igf.common.json_io import read_jsonl


def classify(packet: dict[str, Any]) -> str:
    status = packet.get("translation_status", "unclassified")
    if status != "unclassified":
        return status
    text = " ".join(
        [
            str(packet.get("source_decl", "")),
            str(packet.get("source_statement_raw", "")),
            str(packet.get("normalized_statement", "")),
        ]
    ).lower()
    if any(term in text for term in ["adj", "norm", "projection", "projector", "matrix"]):
        return "matched_to_mathlib"
    if any(term in text for term in ["bounded", "l2", "lp", "loewner", "blt", "closed subspace"]):
        return "requires_adapter"
    return "missing_in_lean"


def plan_for(packet: dict[str, Any], *, target_module: str) -> dict[str, Any]:
    outcome = classify(packet)
    decl = packet.get("source_decl", "external_theorem")
    namespace = packet.get("lean_target_namespace", "InfoGeometry.ExternalTheoremHive")
    imports = packet.get("lean_import_candidates", [])
    symbol_map = packet.get("symbol_map", {})
    base = {
        "kind": "ExternalProofCorrespondencePlan",
        "source_packet_id": packet["id"],
        "source_system": packet.get("source_system"),
        "source_library": packet.get("source_library"),
        "source_decl": decl,
        "translation_status": outcome,
        "authority": "proposal",
        "promotion_allowed": False,
        "target_module": target_module,
        "target_namespace": namespace,
        "imports": imports,
        "symbol_map": symbol_map,
        "authority_boundary": "Foreign proof status is guidance only; Lean/build/audit gates decide authority.",
    }
    if outcome == "matched_to_mathlib":
        base["recommended_action"] = "create bridge alias or theorem-facing #check audit around existing mathlib declaration"
        base["lean_work_mode"] = "name_match"
    elif outcome == "requires_adapter":
        base["recommended_action"] = "create adapter-first Lean wrapper using mathlib primitives and prove local lemmas"
        base["lean_work_mode"] = "adapter_first"
    else:
        base["recommended_action"] = "create residue packet and theorem target for proof reconstruction"
        base["lean_work_mode"] = "residue_then_reconstruct"
    base["prompt_template"] = (
        "Given this foreign formal theorem, do not translate the proof. Identify the Lean-native "
        "mathematical object, search for the nearest mathlib construction, expose a small adapter "
        "API, prove only adapter lemmas using existing mathlib facts, and return build-gated Lean code."
    )
    return base


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--candidates", required=True, help="External theorem packet JSONL.")
    p.add_argument("--target-module", default="InfoGeometry.OperatorAlgebra.ExternalTheoremHive")
    p.add_argument("--out", required=True, help="Correspondence plan JSONL output.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    candidates = Path(args.candidates)
    if not candidates.is_absolute():
        candidates = (ROOT / candidates).resolve()
    out = Path(args.out)
    if not out.is_absolute():
        out = (ROOT / out).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    plans = [plan_for(packet, target_module=args.target_module) for packet in read_jsonl(candidates)]
    with out.open("w", encoding="utf-8") as handle:
        for plan in plans:
            handle.write(json.dumps(plan, ensure_ascii=False, sort_keys=True) + "\n")
    print(f"external proof correspondence plans written: {out} ({len(plans)} plans)")


if __name__ == "__main__":
    main()
