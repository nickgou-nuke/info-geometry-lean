#!/usr/bin/env python3
"""Apex-local defect profiler on the SCC-condensed declaration DAG.

For a given apex, computes a structured **obstruction dossier** rather than
a single importance score.  Each dossier contains raw continuous metrics,
a discretized severity vector, thin-shell chokepoints, thin transitions,
facade/unsound inventories, and thin-shell repair candidates.

Doctrine: docs/apex_defect_diagnosis.md
Prompt template: tools/prompts/apex_diagnosis.md
Cone primitives: tools/infra/causal_cone_spectrum.py
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import defaultdict
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.causal_cone_spectrum import (
        OwnParityCache,
        SigCache,
        binding_mass,
        declaration_mass,
        find_binding_witnesses,
        find_boundary_nodes,
        forward_cone_bfs,
        load_decl_index,
        load_depth_tags,
        load_structure,
        past_cone_bfs,
        precompute_own_parities,
        precompute_signatures,
        role_overlay,
        select_apexes,
        shell_decomposition,
        verify_edge_pair_consistency,
        verify_edge_semantics,
    )
    from tools.pathing import repo_root
else:
    from tools.infra.causal_cone_spectrum import (
        OwnParityCache,
        SigCache,
        binding_mass,
        declaration_mass,
        find_binding_witnesses,
        find_boundary_nodes,
        forward_cone_bfs,
        load_decl_index,
        load_depth_tags,
        load_structure,
        past_cone_bfs,
        precompute_own_parities,
        precompute_signatures,
        role_overlay,
        select_apexes,
        shell_decomposition,
        verify_edge_pair_consistency,
        verify_edge_semantics,
    )
    from tools.pathing import repo_root

DEFAULT_STRUCTURE = "artifacts/dag/structural-topology.json"
DEFAULT_DEPTH_TAGS = "artifacts/dag/representation-depth-tags.json"
DEFAULT_SIGNIFICANCE = "reports/theorem-significance.json"
DEFAULT_JSON_OUT = "reports/dag/apex-defect-dossier.json"
DEFAULT_MD_OUT = "reports/dag/apex-defect-dossier.md"

NON_OWNER_JUDGMENTS = {"wrapper", "facade", "regression", "wormhole"}
METADATA_DEBT_JUDGMENTS = {"untagged"}
ADJACENT_LIFT = {"vertical", "primitive_translator"}
FACADE_JUDGMENTS = {"wrapper", "facade"}
SKIP_JUDGMENTS = {"wormhole", "regression"}


# ── sorry / unsound support index ────────────────────────────

def load_sorry_set(sig_path: Path) -> set[str]:
    """Extract declaration names that are sorry-dependent from theorem-significance.json.

    Currently the repo has zero sorry proofs, so this returns empty.
    The channel activates if sorry usage appears and significance output adds
    has_sorry / sorry_count fields or sorry-related violation codes.
    """
    if not sig_path.exists():
        return set()
    data = json.loads(sig_path.read_text())
    entries = data if isinstance(data, list) else data.get("theorems", data.get("declarations", []))
    sorry: set[str] = set()
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        name = entry.get("name", "")
        # check multiple possible fields
        if entry.get("has_sorry") or entry.get("sorry_count", 0) > 0:
            sorry.add(name)
            continue
        # check violations for sorry-related codes
        for v in entry.get("violations", []):
            code = v.get("code", "") if isinstance(v, dict) else str(v)
            if "sorry" in code.lower():
                sorry.add(name)
                break
    return sorry


# ── dominant judgment for a component ────────────────────────

def _dominant_judgment(cid: str, comp_by_id: dict[str, dict],
                       depth_tags: dict[str, dict]) -> str:
    row = comp_by_id.get(cid, {})
    bag: dict[str, int] = defaultdict(int)
    for member in row.get("members", [row.get("representative", "")]):
        tag = depth_tags.get(member, {})
        bag[tag.get("judgment", "untagged")] += 1
    return max(bag, key=lambda k: (bag[k], k)) if bag else "untagged"


# ── defect computations ─────────────────────────────────────

def compute_shell_thinness(shells: dict[int, list[str]]) -> tuple[float, list[dict]]:
    """Min adjacent-shell width ratio and list of thin transitions."""
    if len(shells) <= 1:
        return 1.0, []
    keys = sorted(shells.keys())
    min_ratio = float("inf")
    thin: list[dict] = []
    for i in range(len(keys) - 1):
        k0, k1 = keys[i], keys[i + 1]
        s0, s1 = len(shells[k0]), len(shells[k1])
        ratio = s1 / max(1, s0)
        if ratio < min_ratio:
            min_ratio = ratio
        if ratio < 0.3 or s1 <= 1:
            thin.append({"from_shell": k0, "to_shell": k1,
                         "size_from": s0, "size_to": s1,
                         "ratio": round(ratio, 4)})
    return round(min_ratio, 4) if min_ratio != float("inf") else 1.0, thin


def compute_singleton_shell_pressure(shells: dict[int, list[str]]) -> float:
    """Fraction of adjacent-shell transitions where one shell has size 1.

    This is a shell-width proxy, not a true graph-theoretic dominator
    computation.  See compute_replacement_fragility for edge-level analysis."""
    if len(shells) <= 1:
        return 0.0
    keys = sorted(shells.keys())
    bottlenecks = 0
    for i in range(len(keys) - 1):
        k0, k1 = keys[i], keys[i + 1]
        if len(shells[k0]) == 1 or len(shells[k1]) == 1:
            bottlenecks += 1
    return round(bottlenecks / max(1, len(keys) - 1), 4)


def compute_witness_deficit(shells: dict[int, list[str]],
                            witnesses: list[dict]) -> tuple[float, list[int]]:
    """Fraction of shells (1..max) with zero binding witnesses, and the list of deficit shells."""
    if not shells:
        return 0.0, []
    max_shell = max(shells.keys())
    witness_shells = {w["shell"] for w in witnesses}
    deficit_shells = [k for k in range(1, max_shell + 1) if k not in witness_shells]
    frac = len(deficit_shells) / max(1, max_shell)
    return round(frac, 4), deficit_shells


def compute_non_owner_mediation(past_dist: dict[str, int],
                                comp_by_id: dict[str, dict],
                                depth_tags: dict[str, dict]) -> float:
    """Fraction of cone members with dominant judgment in NON_OWNER_JUDGMENTS.

    Excludes untagged components — those are metadata-coverage debt,
    not genuine facade/skip dependence."""
    if not past_dist:
        return 0.0
    non_owner = 0
    for cid in past_dist:
        j = _dominant_judgment(cid, comp_by_id, depth_tags)
        if j in NON_OWNER_JUDGMENTS:
            non_owner += 1
    return round(non_owner / len(past_dist), 4)


def compute_skip_layer_density(past_dist: dict[str, int],
                               comp_by_id: dict[str, dict],
                               depth_tags: dict[str, dict]) -> tuple[float, list[dict]]:
    """wormhole + regression count / past_cone_size, plus inventory."""
    if not past_dist:
        return 0.0, []
    inventory: list[dict] = []
    for cid in past_dist:
        j = _dominant_judgment(cid, comp_by_id, depth_tags)
        if j in SKIP_JUDGMENTS:
            row = comp_by_id.get(cid, {})
            inventory.append({
                "componentId": cid,
                "representative": row.get("representative", ""),
                "shell": past_dist[cid],
                "judgment": j,
            })
    density = len(inventory) / len(past_dist)
    return round(density, 4), inventory


def compute_judgment_mismatch_density(
        shells: dict[int, list[str]], past_dist: dict[str, int],
        comp_by_id: dict[str, dict], depth_tags: dict[str, dict]) -> float:
    """Fraction of cross-shell edges where source judgment is wormhole/regression
    into a transition otherwise dominated by adjacent-lift judgments."""
    past_set = set(past_dist.keys())
    total_cross = 0
    mismatch = 0
    # classify each shell's dominant judgment set
    shell_dominant: dict[int, str] = {}
    for k, cids in shells.items():
        jbag: dict[str, int] = defaultdict(int)
        for cid in cids:
            jbag[_dominant_judgment(cid, comp_by_id, depth_tags)] += 1
        shell_dominant[k] = max(jbag, key=lambda k: (jbag[k], k)) if jbag else "untagged"

    for cid in past_dist:
        j_src = _dominant_judgment(cid, comp_by_id, depth_tags)
        row = comp_by_id.get(cid, {})
        shell_src = past_dist[cid]
        for dep_cid in row.get("dependencyComponentIds", []):
            if dep_cid not in past_set:
                continue
            shell_tgt = past_dist[dep_cid]
            if shell_tgt == shell_src:
                continue
            total_cross += 1
            # mismatch: source is skip-judgment, target shell is dominated by adjacent-lift
            if j_src in SKIP_JUDGMENTS and shell_dominant.get(shell_tgt, "") in ADJACENT_LIFT:
                mismatch += 1
    return round(mismatch / max(1, total_cross), 4)


def compute_replacement_fragility(shells: dict[int, list[str]],
                                   comp_by_id: dict[str, dict]) -> float:
    """Fraction of adjacent-shell transitions where removal of one lower-shell
    component disconnects at least one upper-shell component from the next shell.

    For each shell pair (k, k+1), build the per-upper-component support set
    (which lower-shell components it depends on).  The transition is fragile if
    there exists a single lower-shell component whose removal leaves at least
    one upper-shell component with an empty support set.
    """
    if len(shells) <= 1:
        return 0.0
    keys = sorted(shells.keys())
    fragile = 0

    for i in range(len(keys) - 1):
        k_upper, k_lower = keys[i], keys[i + 1]
        upper_set = set(shells[k_upper])
        lower_set = set(shells[k_lower])

        support_map: dict[str, set[str]] = {}
        all_targets: set[str] = set()

        for cid in upper_set:
            row = comp_by_id.get(cid, {})
            deps = {d for d in row.get("dependencyComponentIds", []) if d in lower_set}
            if deps:
                support_map[cid] = deps
                all_targets |= deps

        if not support_map:
            continue

        is_fragile = False
        for lower_cid in all_targets:
            if any((deps - {lower_cid}) == set() for deps in support_map.values()):
                is_fragile = True
                break

        if is_fragile:
            fragile += 1

    return round(fragile / max(1, len(keys) - 1), 4)


def compute_boundary_load(boundary: list[dict], past_dist: dict[str, int]) -> float:
    # Denominator excludes the apex (which is never a boundary node).
    return round(len(boundary) / max(1, len(past_dist) - 1), 4)


def find_non_owner_inventory(past_dist: dict[str, int],
                             comp_by_id: dict[str, dict],
                             depth_tags: dict[str, dict]) -> tuple[list[dict], list[dict], list[dict]]:
    """Components whose dominant judgment is in NON_OWNER_JUDGMENTS or METADATA_DEBT_JUDGMENTS.

    Returns three lists:
      - facade_only: dominant judgment in FACADE_JUDGMENTS (wrapper, facade)
      - skip_only: dominant judgment in SKIP_JUDGMENTS (regression, wormhole)
      - untagged_only: dominant judgment is 'untagged' (metadata-coverage debt)
    """
    facade_only: list[dict] = []
    skip_only: list[dict] = []
    untagged_only: list[dict] = []
    for cid in past_dist:
        j = _dominant_judgment(cid, comp_by_id, depth_tags)
        row = comp_by_id.get(cid, {})
        entry = {
            "componentId": cid,
            "representative": row.get("representative", ""),
            "shell": past_dist[cid],
            "judgment": j,
        }
        if j in FACADE_JUDGMENTS:
            facade_only.append(entry)
        elif j in SKIP_JUDGMENTS:
            skip_only.append(entry)
        elif j in METADATA_DEBT_JUDGMENTS:
            untagged_only.append(entry)
    return facade_only, skip_only, untagged_only


def find_unsound_support(past_dist: dict[str, int],
                         comp_by_id: dict[str, dict],
                         sorry_set: set[str]) -> list[dict]:
    """Components in the cone that contain sorry-dependent members."""
    result = []
    for cid in past_dist:
        row = comp_by_id.get(cid, {})
        members = row.get("members", [row.get("representative", "")])
        sorry_members = [m for m in members if m in sorry_set]
        if sorry_members:
            result.append({
                "componentId": cid,
                "representative": row.get("representative", ""),
                "shell": past_dist[cid],
                "sorry_members": sorry_members,
            })
    return result


def find_thin_shell_chokepoints(shells: dict[int, list[str]],
                                past_dist: dict[str, int],
                                comp_by_id: dict[str, dict]) -> list[dict]:
    """Components in thin shells (size ≤ 2) that are potential chokepoints.

    This is a width-based proxy: it flags components in narrow shells on
    the assumption that support narrows there.  It does not verify
    cross-shell connector uniqueness (see compute_replacement_fragility
    for that stronger test)."""
    past_set = set(past_dist.keys())
    bottlenecks = []
    for k, cids in shells.items():
        if len(cids) <= 2:
            for cid in cids:
                row = comp_by_id.get(cid, {})
                # how many closer-to-apex components in the cone depend on this one?
                desc_in_cone = [d for d in row.get("reverseDependentComponentIds", [])
                                if d in past_set and past_dist.get(d, k) < k]
                bottlenecks.append({
                    "componentId": cid,
                    "representative": row.get("representative", ""),
                    "shell": k,
                    "shell_size": len(cids),
                    "downstream_dependents_in_cone": len(desc_in_cone),
                })
    return bottlenecks


def compute_suggested_read_order(shells: dict[int, list[str]],
                                 past_dist: dict[str, int],
                                 comp_by_id: dict[str, dict],
                                 depth_tags: dict[str, dict],
                                 bottlenecks: list[dict],
                                 witnesses: list[dict],
                                 decl_index: dict[str, dict] | None = None,
                                 limit: int = 20) -> list[dict]:
    """Source-aware topological read order:
    owner support → translators → binding points → apex.
    Deduplicates by componentId."""
    ROLE_PRIORITY = {
        "vertical": 0,
        "primitive_translator": 1,
        "capstone_coherence": 2,
        "wormhole": 3,
        "regression": 3,
        "untagged": 4,
    }
    bottleneck_cids = {b["componentId"] for b in bottlenecks}
    witness_cids = {w["componentId"] for w in witnesses}

    scored = []
    for cid in past_dist:
        j = _dominant_judgment(cid, comp_by_id, depth_tags)
        shell = past_dist[cid]
        is_bottleneck = cid in bottleneck_cids
        is_witness = cid in witness_cids
        scored.append((
            -shell,
            ROLE_PRIORITY.get(j, 5),
            -(1 if is_bottleneck else 0),
            -(1 if is_witness else 0),
            cid,
        ))
    scored.sort()

    result = []
    seen_cids: set[str] = set()
    for _, _, _, _, cid in scored:
        if cid in seen_cids:
            continue
        seen_cids.add(cid)
        row = comp_by_id.get(cid, {})
        rep = row.get("representative", "")
        j = _dominant_judgment(cid, comp_by_id, depth_tags)
        # Resolve file: try depth_tags first, then decl_index
        tag = depth_tags.get(rep, {})
        f = tag.get("file", "")
        if not f and decl_index:
            f = decl_index.get(rep, {}).get("file", "")
        result.append({
            "componentId": cid,
            "representative": rep,
            "shell": past_dist[cid],
            "judgment": j,
            "file": f,
        })
        if len(result) >= limit:
            break
    return result


def collect_source_paths(read_order: list[dict],
                         bottlenecks: list[dict],
                         comp_by_id: dict[str, dict],
                         depth_tags: dict[str, dict],
                         decl_index: dict[str, dict] | None = None) -> list[str]:
    """Lean file paths for read-order, bottleneck, and repair components."""
    paths: set[str] = set()
    for item in read_order:
        f = item.get("file", "")
        if f:
            paths.add(f)
    for b in bottlenecks:
        rep = b.get("representative", "")
        tag = depth_tags.get(rep, {})
        f = tag.get("file", "")
        if not f and decl_index:
            f = decl_index.get(rep, {}).get("file", "")
        if f:
            paths.add(f)
    return sorted(paths)


# ── severity discretization ──────────────────────────────────

def discretize(value: float, mild_threshold: float, structural_threshold: float) -> int:
    if value >= structural_threshold:
        return 2
    if value >= mild_threshold:
        return 1
    return 0


def severity_vector(raw: dict) -> dict:
    return {
        "shell_thinness": discretize(1.0 - raw["shell_thinness"], 0.5, 0.8),
        "singleton_shell_pressure": discretize(raw["singleton_shell_pressure"], 0.2, 0.5),
        "witness_deficit": discretize(raw["witness_deficit"], 0.3, 0.6),
        "non_owner_mediation": discretize(raw["non_owner_mediation"], 0.2, 0.5),
        "skip_layer_density": discretize(raw["skip_layer_density"], 0.05, 0.15),
        "judgment_mismatch_density": discretize(raw["judgment_mismatch_density"], 0.05, 0.15),
        "replacement_fragility": discretize(raw["replacement_fragility"], 0.2, 0.5),
        "boundary_load": discretize(raw["boundary_load"], 0.5, 0.8),
    }


def _component_metadata(cid: str, comp_by_id: dict[str, dict],
                        depth_tags: dict[str, dict]) -> dict:
    """Component-level apex metadata: dominant judgment, judgment bag,
    max depthNat, and depthNat range across all members."""
    row = comp_by_id.get(cid, {})
    members = row.get("members", [row.get("representative", "")])
    jbag: dict[str, int] = defaultdict(int)
    depths: list[int] = []
    for m in members:
        tag = depth_tags.get(m, {})
        jbag[tag.get("judgment", "untagged")] += 1
        d = tag.get("depthNat")
        if d is not None:
            depths.append(d)
    dominant_j = max(jbag, key=lambda k: (jbag[k], k)) if jbag else "untagged"
    n_members = len(members)
    is_mixed = len([j for j, c in jbag.items() if c > 0]) > 1
    return {
        "dominant_judgment": dominant_j,
        "is_mixed_judgment": is_mixed,
        "judgment_bag": dict(jbag),
        "max_depthNat": max(depths) if depths else None,
        "depthNat_range": [min(depths), max(depths)] if depths else None,
        "n_members": n_members,
    }


# ── per-apex dossier ─────────────────────────────────────────

def build_dossier(apex_cid: str, comp_by_id: dict[str, dict],
                  depth_tags: dict[str, dict],
                  sorry_set: set[str],
                  sig_cache: SigCache | None = None,
                  own_parity_cache: OwnParityCache | None = None,
                  decl_index: dict[str, dict] | None = None,
                  forward_radius: int = 3) -> dict:
    row = comp_by_id.get(apex_cid)
    if row is None:
        raise ValueError(
            f"apex component {apex_cid!r} not found in the component index — "
            f"stale or invalid component ID"
        )
    rep = row.get("representative", apex_cid)
    apex_meta = _component_metadata(apex_cid, comp_by_id, depth_tags)

    # cones
    past_dist = past_cone_bfs(apex_cid, comp_by_id)
    fwd_dist = forward_cone_bfs(apex_cid, comp_by_id)
    # bound forward cone (strict descendants only — exclude the apex itself)
    fwd_bounded = {cid: dist for cid, dist in fwd_dist.items() if 0 < dist <= forward_radius}

    shells = shell_decomposition(past_dist)
    overlay = role_overlay(shells, comp_by_id, depth_tags)
    max_shell = max(shells.keys()) if shells else 0

    # witnesses
    witnesses = find_binding_witnesses(past_dist, comp_by_id, depth_tags, sig_cache)

    # masses (retained as supplementary coordinates)
    mass, mass_contributors, _ = declaration_mass(apex_cid, comp_by_id, depth_tags, sig_cache)
    bmass = binding_mass(
        witnesses, past_dist, comp_by_id, depth_tags,
        own_parity_cache=own_parity_cache,
    )

    # boundary
    boundary = find_boundary_nodes(apex_cid, shells, past_dist, comp_by_id, depth_tags, sig_cache)

    # defect metrics
    shell_thin, thin_transitions = compute_shell_thinness(shells)
    dom_pressure = compute_singleton_shell_pressure(shells)
    wit_deficit, deficit_shells = compute_witness_deficit(shells, witnesses)
    non_owner = compute_non_owner_mediation(past_dist, comp_by_id, depth_tags)
    skip_density, skip_inventory = compute_skip_layer_density(past_dist, comp_by_id, depth_tags)
    j_mismatch = compute_judgment_mismatch_density(shells, past_dist, comp_by_id, depth_tags)
    repl_fragility = compute_replacement_fragility(shells, comp_by_id)
    b_load = compute_boundary_load(boundary, past_dist)

    # structured inventories
    facade_only, skip_only, untagged_only = find_non_owner_inventory(past_dist, comp_by_id, depth_tags)
    unsound = find_unsound_support(past_dist, comp_by_id, sorry_set)
    chokepoints = find_thin_shell_chokepoints(shells, past_dist, comp_by_id)
    read_order = compute_suggested_read_order(
        shells, past_dist, comp_by_id, depth_tags, chokepoints, witnesses, decl_index)
    source_paths = collect_source_paths(read_order, chokepoints, comp_by_id, depth_tags, decl_index)

    raw = {
        "shell_thinness": shell_thin,
        "singleton_shell_pressure": dom_pressure,
        "witness_deficit": wit_deficit,
        "non_owner_mediation": non_owner,
        "skip_layer_density": skip_density,
        "judgment_mismatch_density": j_mismatch,
        "replacement_fragility": repl_fragility,
        "boundary_load": b_load,
    }

    return {
        "apex": rep,
        "componentId": apex_cid,
        "apex_metadata": apex_meta,
        "carrier_scope": {
            "past_cone_size": len(past_dist),
            "max_shell": max_shell,
            "forward_cone_size": len(fwd_bounded),
            "forward_radius": forward_radius,
        },
        "raw_metrics": raw,
        "severity_vector": severity_vector(raw),
        "supplementary": {
            "declaration_mass": round(mass, 4),
            "binding_mass": round(bmass, 4),
            "mass_contributors": mass_contributors,
        },
        "thin_shell_chokepoints": chokepoints[:15],
        "thin_transitions": thin_transitions,
        "witness_deficits": deficit_shells,
        "facade_mediation": facade_only[:15],
        "non_owner_skip": skip_only[:15],
        "metadata_debt_untagged": untagged_only[:15],
        "n_untagged": len(untagged_only),
        "unsound_support": unsound[:15],
        "skip_layer_inventory": skip_inventory[:15],
        "boundary_fragility": [b for b in boundary
                               if b.get("desc_in_cone", 0) <= 1
                               and b.get("coh_support", 0) <= 1][:15],
        "suggested_read_order": read_order,
        "thin_shell_repair_candidates": chokepoints[:10],
        "source_paths": source_paths,
        "role_overlay": overlay,
        "binding_witness_sample": witnesses[:10],
    }


# ── markdown rendering ───────────────────────────────────────

def _relative_path(abs_path: str) -> str:
    """Strip repo root prefix for readable display."""
    marker = "/lean/"
    idx = abs_path.find(marker)
    if idx >= 0:
        return abs_path[idx + 1:]  # "lean/..."
    return abs_path


def render_markdown(dossiers: list[dict], elapsed: float) -> str:
    lines = [
        "# Apex Defect Dossiers",
        "",
        "Per-apex obstruction profiles on the **SCC-condensed** declaration DAG.",
        "Doctrine: `docs/apex_defect_diagnosis.md`.",
        "",
    ]
    for d in dossiers:
        raw = d["raw_metrics"]
        sev = d["severity_vector"]
        scope = d["carrier_scope"]
        meta = d["apex_metadata"]
        SEV_LABEL = {0: "-", 1: "mild", 2: "**structural**"}

        lines.extend([
            f"## Apex: `{d['apex']}`",
            "",
            f"| Scope | Value |",
            f"|---|---|",
            f"| Past cone | {scope['past_cone_size']} components |",
            f"| Max shell | {scope['max_shell']} |",
            f"| Forward cone (r={scope['forward_radius']}) | {scope['forward_cone_size']} components |",
            f"| Dominant judgment | {meta['dominant_judgment']}{'  *(mixed)' if meta['is_mixed_judgment'] else ''} |",
            f"| Judgment bag | {meta['judgment_bag']} |",
            f"| Max depthNat | {meta['max_depthNat']} |",
            f"| depthNat range | {meta['depthNat_range']} |",
            f"| Members | {meta['n_members']} |",
            "",
            "### Raw Metrics + Severity",
            "",
            "| Metric | Raw | Severity |",
            "|---|---|---|",
        ])
        for key in raw:
            lines.append(f"| {key} | {raw[key]} | {SEV_LABEL[sev[key]]} |")
        lines.append("")

        # metadata coverage
        n_untagged = d.get("n_untagged", len(d.get("metadata_debt_untagged", [])))
        cone_size = scope["past_cone_size"]
        if n_untagged > 0:
            pct = round(100 * n_untagged / max(1, cone_size), 1)
            lines.extend([
                "### Metadata Coverage",
                "",
                f"**{n_untagged}** of {cone_size} cone components "
                f"({pct}%) are **untagged** (no `@[rep_depth]` annotation).  "
                "Role-dependent metrics (non-owner mediation, witness deficit, "
                "binding mass) are sensitive to tagging coverage; untagged nodes "
                "are metadata-coverage debt, not structural defects.",
                "",
            ])

        # thin transitions
        if d["thin_transitions"]:
            lines.extend(["### Thin Transitions", "",
                          "| From shell | To shell | Size from | Size to | Ratio |",
                          "|---|---|---|---|---|"])
            for t in d["thin_transitions"]:
                lines.append(f"| {t['from_shell']} | {t['to_shell']} | {t['size_from']} | {t['size_to']} | {t['ratio']} |")
            lines.append("")

        # witness deficits
        if d["witness_deficits"]:
            lines.append(f"### Witness Deficit Shells: {d['witness_deficits']}")
            lines.append("")

        # chokepoints
        if d["thin_shell_chokepoints"]:
            lines.extend(["### Thin-Shell Chokepoints (sample)", "",
                          "| Representative | Shell | Shell size |",
                          "|---|---|---|"])
            for b in d["thin_shell_chokepoints"][:10]:
                lines.append(f"| `{b['representative'][:60]}` | {b['shell']} | {b['shell_size']} |")
            lines.append("")

        # unsound support
        if d["unsound_support"]:
            lines.extend(["### Unsound Support (sorry-dependent, sample)", "",
                          "| Representative | Shell |",
                          "|---|---|"])
            for u in d["unsound_support"][:10]:
                lines.append(f"| `{u['representative'][:60]}` | {u['shell']} |")
            lines.append("")

        # read order
        if d["suggested_read_order"]:
            lines.extend(["### Suggested Read Order", "",
                          "| # | Representative | Shell | Judgment | File |",
                          "|---|---|---|---|---|"])
            for i, r in enumerate(d["suggested_read_order"][:15], 1):
                f = _relative_path(r.get("file", ""))
                lines.append(f"| {i} | `{r['representative']}` | {r['shell']} | {r['judgment']} | {f} |")
            lines.append("")

        lines.append("")

    lines.append(f"*Computed in {elapsed:.1f}s.*")
    return "\n".join(lines) + "\n"


# ── main ─────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Apex defect profiler (SCC-condensed DAG)")
    ap.add_argument("--structure", default=DEFAULT_STRUCTURE)
    ap.add_argument("--depth-tags", default=DEFAULT_DEPTH_TAGS)
    ap.add_argument("--significance", default=DEFAULT_SIGNIFICANCE)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--apex", nargs="*", default=[],
                    help="Apex declaration names or component IDs")
    ap.add_argument("--n-default", type=int, default=5)
    ap.add_argument("--selection-policy", choices=["capstone_fanin", "corridor"],
                    default="corridor",
                    help="Apex choice policy (corridor: depth-tagged bias; capstone_fanin: sinks by prerequisite fan-in)")
    ap.add_argument("--forward-radius", type=int, default=3)
    args = ap.parse_args()

    root = repo_root()
    t0 = time.time()

    print("[defect] loading structural topology ...")
    payload, comp_by_id, comp_by_rep, comp_by_member = load_structure(root / args.structure)
    verify_edge_pair_consistency(comp_by_id)
    verify_edge_semantics(payload, comp_by_id)
    depth_tags = load_depth_tags(root / args.depth_tags)
    decl_index = load_decl_index(root / "artifacts" / "dag" / "index" / "decls.jsonl")
    sorry_set = load_sorry_set(root / args.significance)
    n_comp = len(comp_by_id)
    print(f"[defect] {n_comp} components, {len(depth_tags)} depth-tagged, {len(sorry_set)} sorry-dependent")

    sig_cache = precompute_signatures(comp_by_id, depth_tags)
    own_parity_cache = precompute_own_parities(comp_by_id, depth_tags)
    print(f"[defect] precomputed {len(sig_cache)} signatures + own-parities")

    apex_cids = select_apexes(payload, comp_by_id, comp_by_rep, comp_by_member,
                              args.apex, args.n_default, args.selection_policy,
                              depth_tags, decl_index)
    print(f"[defect] analyzing {len(apex_cids)} apexes")

    dossiers = []
    for cid in apex_cids:
        rep = comp_by_id.get(cid, {}).get("representative", cid)
        print(f"[defect]   {rep} ...")
        d = build_dossier(cid, comp_by_id, depth_tags, sorry_set,
                          sig_cache, own_parity_cache, decl_index, args.forward_radius)
        sev = d["severity_vector"]
        structural = sum(1 for v in sev.values() if v == 2)
        mild = sum(1 for v in sev.values() if v == 1)
        print(f"[defect]     severity: {structural} structural, {mild} mild")
        dossiers.append(d)

    elapsed = time.time() - t0
    print(f"[defect] done in {elapsed:.1f}s")

    out = {
        "scope": "SCC-condensed DAG (structural-topology.json)",
        "components": n_comp,
        "apexes_analyzed": len(dossiers),
        "dossiers": dossiers,
        "elapsed_seconds": round(elapsed, 1),
    }
    json_out = root / args.json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(out, indent=2))

    md_out = root / args.md_out
    md_out.write_text(render_markdown(dossiers, elapsed))

    print(f"[defect] wrote {json_out}")
    print(f"[defect] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
