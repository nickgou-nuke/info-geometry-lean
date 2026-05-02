#!/usr/bin/env python3
"""
tools/infra/identity_protocol_metrics.py

Mixed-mode metric evaluator for Identity Protocol v1.
- kappa can be real from structural fingerprints (dag_transport.v1)
- tau_A/tau_B/tau_C_proxy/epsilon_majorana/delta_M remain proxy in v1
"""

from __future__ import annotations

import math
from typing import Any


def _as_float(value: Any, default: float = math.nan) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def _pass(value: float, max_value: float) -> bool:
    return math.isfinite(value) and value <= max_value


def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))


def jaccard_distance(a: set[str], b: set[str]) -> float:
    if not a and not b:
        return 0.0
    union = a | b
    if not union:
        return 0.0
    return 1.0 - (len(a & b) / len(union))


def extract_invariant_fingerprints(snapshot: dict[str, Any]) -> dict[str, Any]:
    return {
        "debruijn_hashes": list(snapshot.get("debruijn_hashes", [])),
        "scc_basin_ids": list(snapshot.get("scc_basin_ids", [])),
        "motif_hashes": list(snapshot.get("motif_hashes", [])),
        "node_count": max(1, int(snapshot.get("node_count", 1))),
    }


def unresolved_fingerprint() -> dict[str, Any]:
    return {
        "debruijn_hashes": [],
        "scc_basin_ids": [],
        "motif_hashes": [],
        "node_count": 1,
        "unresolved": True,
    }


def compute_kappa_from_fingerprints(fp_a: dict[str, Any], fp_b: dict[str, Any]) -> float:
    debruijn_a = set(str(x) for x in fp_a.get("debruijn_hashes", []))
    debruijn_b = set(str(x) for x in fp_b.get("debruijn_hashes", []))
    scc_a = set(str(x) for x in fp_a.get("scc_basin_ids", []))
    scc_b = set(str(x) for x in fp_b.get("scc_basin_ids", []))
    motif_a = set(str(x) for x in fp_a.get("motif_hashes", []))
    motif_b = set(str(x) for x in fp_b.get("motif_hashes", []))

    size_a = max(1, int(fp_a.get("node_count", 1)))
    size_b = max(1, int(fp_b.get("node_count", 1)))
    size_delta = abs(size_a - size_b) / max(size_a, size_b)

    kappa = (
        0.40 * jaccard_distance(debruijn_a, debruijn_b)
        + 0.30 * jaccard_distance(scc_a, scc_b)
        + 0.20 * jaccard_distance(motif_a, motif_b)
        + 0.10 * size_delta
    )
    return clamp01(kappa)


def evaluate_gates(metrics: dict[str, float], thresholds: dict[str, Any]) -> dict[str, bool]:
    t = thresholds["thresholds"]
    return {
        "tau_A_pass": _pass(metrics["tau_A"], t["tau_A_max"]),
        "tau_B_pass": _pass(metrics["tau_B"], t["tau_B_max"]),
        "tau_C_proxy_pass": _pass(metrics["tau_C_proxy"], t["tau_C_proxy_max"]),
        "epsilon_pass": _pass(metrics["epsilon_majorana"], t["epsilon_majorana_max"]),
        "kappa_pass": _pass(metrics["kappa"], t["kappa_max"]),
        "delta_M_pass": _pass(metrics["delta_M"], t["delta_M_max"]),
    }


def resolve_verdict(gates: dict[str, bool]) -> tuple[str, list[str]]:
    hard_gates = ["tau_A_pass", "tau_B_pass", "epsilon_pass", "delta_M_pass"]
    hard_failures = [g for g in hard_gates if not gates.get(g, False)]
    if hard_failures:
        return "BIFURCATED", hard_failures
    soft_failures = [g for g in ["tau_C_proxy_pass", "kappa_pass"] if not gates.get(g, False)]
    if soft_failures:
        return "CONDITIONAL", soft_failures
    return "UNIFIED", []


def proxy_metrics_from_fixture(fixture: dict[str, Any]) -> dict[str, float]:
    raw = fixture.get("expected_metrics", fixture.get("metrics", {}))
    return {
        "tau_A": _as_float(raw.get("tau_A", 0.0)),
        "tau_B": _as_float(raw.get("tau_B", 0.0)),
        "tau_C_proxy": _as_float(raw.get("tau_C_proxy", 0.0)),
        "epsilon_majorana": _as_float(raw.get("epsilon_majorana", 0.0)),
        "kappa": _as_float(raw.get("kappa", 0.0)),
        "delta_M": _as_float(raw.get("delta_M", 0.0)),
    }


def evaluate_identity_fixture(fixture: dict[str, Any], thresholds: dict[str, Any]) -> dict[str, Any]:
    metrics = proxy_metrics_from_fixture(fixture)
    blockers: list[str] = []
    metric_sources = {
        "kappa": "proxy",
        "tau_A": "proxy",
        "tau_B": "proxy",
        "tau_C_proxy": "proxy",
        "epsilon_majorana": "proxy",
        "delta_M": "proxy",
    }

    fp_a_raw = fixture.get("state_a")
    fp_b_raw = fixture.get("state_b")
    if isinstance(fp_a_raw, dict) and isinstance(fp_b_raw, dict):
        fp_a = extract_invariant_fingerprints(fp_a_raw)
        fp_b = extract_invariant_fingerprints(fp_b_raw)
        metrics["kappa"] = compute_kappa_from_fingerprints(fp_a, fp_b)
        metric_sources["kappa"] = "dag_transport.v1"
    else:
        metric_sources["kappa"] = "proxy_unresolved_snapshot"
        blockers.append("kappa_unavailable")
        fp_a = unresolved_fingerprint()
        fp_b = unresolved_fingerprint()

    gates = evaluate_gates(metrics, thresholds)
    verdict, verdict_blockers = resolve_verdict(gates)
    blockers.extend(verdict_blockers)

    if fp_a.get("unresolved"):
        blockers.append("snapshot_a_unresolved")
    if fp_b.get("unresolved"):
        blockers.append("snapshot_b_unresolved")
    if fp_a.get("unresolved") or fp_b.get("unresolved"):
        if verdict == "UNIFIED":
            verdict = "CONDITIONAL"

    metric_mode = "mixed" if metric_sources["kappa"] == "dag_transport.v1" else "proxy"

    return {
        "metric_mode": metric_mode,
        "metric_sources": metric_sources,
        "metrics": metrics,
        "gates": gates,
        "verdict": verdict,
        "blockers": sorted(set(blockers)),
        "fingerprints": fixture.get(
            "fingerprints",
            {
                "debruijn_hashes": [],
                "scc_basin_ids": [],
                "motif_hashes": [],
            },
        ),
        "notes": [
            "v1 mixed evaluator: kappa may be computed from structural fingerprints; other metrics remain proxy"
        ],
    }
