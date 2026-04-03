#!/usr/bin/env python3
"""Causal-cone diagnostics on the SCC-condensed declaration DAG.

For a given apex node, computes:
- Past cone via BFS on the condensed DAG
- Shell decomposition by shortest-path distance
- RepDepth role overlay per shell (judgment histogram)
- Binding witnesses: components receiving multi-parity causal chains
- Declaration mass: weighted coherence-bearing strict descendants
- Binding mass: cross-parity synergy at convergence points
- Boundary nodes: light atoms on the cone perimeter

Operates on artifacts/dag/structural-topology.json (the SCC-condensed DAG)
and artifacts/dag/representation-depth-tags.json (RepDepth + judgment data).

Edge-orientation invariant:
  dependencyComponentIds        = direct prerequisites of this component
  reverseDependentComponentIds  = components that depend on this component

Past(a) follows dependencyComponentIds.
Desc(a) follows reverseDependentComponentIds.

If the export convention flips, all metrics silently invert.

The formal definitions follow docs/causal_cone_formal_definitions.md.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import defaultdict, deque
from pathlib import Path
from typing import Any, TypeAlias

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pathing import repo_root


DEFAULT_STRUCTURE = "artifacts/dag/structural-topology.json"
DEFAULT_DEPTH_TAGS = "artifacts/dag/representation-depth-tags.json"
DEFAULT_JSON_OUT = "reports/dag/causal-cone-spectrum.json"
DEFAULT_MD_OUT = "reports/dag/causal-cone-spectrum.md"

# Only coherence-bearing roles contribute to mass and witness logic.
COHERENCE_ROLE_WEIGHTS = {
    "primitive_translator": 2,
    "capstone_coherence": 3,
}
COHERENCE_ROLES = set(COHERENCE_ROLE_WEIGHTS)

# Preferred corridor modules from docs/Theory.md anchor corridors.
CORRIDOR_MODULES = {
    "InfoGeometry.Canonical.RelativePotentialCountBridge",
    "InfoGeometry.Canonical.PositiveRayCore",
    "InfoGeometry.Canonical.RelativePotentialCore",
    "InfoGeometry.Canonical.RelativeSurprisalOperatorLift",
    "InfoGeometry.Canonical.InformationCalculus",
    "InfoGeometry.Krein.SplitQuadratic",
    "InfoGeometry.Krein.SplitQuadraticSheets",
    "InfoGeometry.Krein.PolarizedSector",
    "InfoGeometry.Canonical.SpectralInference",
    "InfoGeometry.Canonical.DiracMetricCompatibility",
    "InfoGeometry.Canonical.BogoliubovTransport",
    "InfoGeometry.Canonical.BogoliubovProjectorFlux",
    "InfoGeometry.Canonical.BogoliubovPolarizationBridge",
    "InfoGeometry.Canonical.KreinDiracPolarizationBridge",
    "InfoGeometry.Canonical.KreinDiracSpectralLift",
    "InfoGeometry.Canonical.Attention",
    "InfoGeometry.Canonical.AttentionPolarizedGibbsBridge",
    "InfoGeometry.Quantum.TriadicWeylBridge",
    "InfoGeometry.Canonical.WeylGaugeField",
    "InfoGeometry.Canonical.WeylTransport",
    "InfoGeometry.Canonical.RealBdG",
    "InfoGeometry.Canonical.RealBdGSheetBridge",
    "InfoGeometry.Convex.HessianGeometry",
}

# Aligned with depthNat: thermo is the deepest layer (depthNat 5),
# count is the shallowest (depthNat 0).  Corridor sort uses reverse=True
# so deeper layers are selected first.
DEPTH_PRIORITY = {
    "count": 0,
    "projective": 1,
    "operator": 2,
    "krein": 3,
    "transport": 4,
    "thermo": 5,
}

EXPECTED_ORIENTATION_MARKER = "declaration -> dependency"

JsonDict: TypeAlias = dict[str, Any]
SigCache: TypeAlias = dict[str, tuple[set[int], set[int], set[str]]]
OwnParityCache: TypeAlias = dict[str, set[int]]


# ── helpers ──────────────────────────────────────────────────

def _iter_component_members(row: JsonDict) -> list[str]:
    members = row.get("members")
    if isinstance(members, list) and members:
        return [str(m) for m in members]
    rep = row.get("representative", "")
    return [str(rep)] if rep else []


def _require_components(payload: JsonDict) -> list[JsonDict]:
    comps = payload.get("components")
    if not isinstance(comps, list):
        sys.exit("[cone] FATAL: structural-topology.json is missing a top-level 'components' list.")
    return comps


def _strict_int_list(value: Any) -> list[int]:
    if not isinstance(value, list):
        return []
    out: list[int] = []
    for x in value:
        if isinstance(x, int):
            out.append(x)
    return out


def _strict_int(value: Any) -> int | None:
    return value if isinstance(value, int) else None


# ── data loading ─────────────────────────────────────────────

def load_decl_index(path: Path) -> dict[str, dict]:
    """Build name → {module, file} map from decls.jsonl."""
    idx: dict[str, dict] = {}
    if not path.exists():
        return idx

    with path.open("r", encoding="utf-8") as f:
        for lineno, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                d = json.loads(line)
            except json.JSONDecodeError as e:
                sys.exit(f"[cone] FATAL: malformed JSON in {path} at line {lineno}: {e}")

            name = d.get("name")
            if not isinstance(name, str) or not name:
                continue
            idx[name] = {
                "module": d.get("module", "") if isinstance(d.get("module", ""), str) else "",
                "file": d.get("file", "") if isinstance(d.get("file", ""), str) else "",
            }
    return idx


def load_structure(path: Path):
    if not path.exists():
        sys.exit(f"[cone] FATAL: structure file not found: {path}")

    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        sys.exit(f"[cone] FATAL: could not parse {path}: {e}")

    comp_by_id: dict[str, dict] = {}
    comp_by_rep: dict[str, dict] = {}
    comp_by_member: dict[str, dict] = {}

    for row in _require_components(payload):
        if not isinstance(row, dict):
            sys.exit("[cone] FATAL: every element of 'components' must be an object.")

        cid = row.get("componentId")
        rep = row.get("representative")

        if not isinstance(cid, str) or not cid:
            sys.exit("[cone] FATAL: encountered component without a valid string componentId.")
        if not isinstance(rep, str) or not rep:
            sys.exit(f"[cone] FATAL: component {cid} has no valid representative.")

        if cid in comp_by_id:
            sys.exit(f"[cone] FATAL: duplicate componentId detected: {cid}")
        if rep in comp_by_rep:
            sys.exit(f"[cone] FATAL: duplicate representative detected: {rep}")

        comp_by_id[cid] = row
        comp_by_rep[rep] = row

        for member in _iter_component_members(row):
            prior = comp_by_member.get(member)
            if prior is not None and prior.get("componentId") != cid:
                sys.exit(
                    f"[cone] FATAL: member {member!r} appears in multiple components: "
                    f"{prior.get('componentId')} and {cid}"
                )
            comp_by_member[member] = row

    return payload, comp_by_id, comp_by_rep, comp_by_member


def load_depth_tags(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}

    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        sys.exit(f"[cone] FATAL: could not parse {path}: {e}")

    entries = obj.get("declarations", obj.get("tags", obj)) if isinstance(obj, dict) else obj
    if not isinstance(entries, list):
        return {}

    out: dict[str, dict] = {}
    for e in entries:
        if not isinstance(e, dict):
            continue
        name = e.get("name")
        if isinstance(name, str) and name:
            out[name] = e
    return out


# ── orientation verification ────────────────────────────────

def verify_edge_pair_consistency(comp_by_id: dict[str, dict]) -> None:
    """Check that dependency and reverse-dependent adjacency lists are mutually consistent."""
    dep_sets: dict[str, set[str]] = {}
    rev_sets: dict[str, set[str]] = {}

    for cid, row in comp_by_id.items():
        dep_sets[cid] = set(str(v) for v in row.get("dependencyComponentIds", []) if isinstance(v, str))
        rev_sets[cid] = set(str(v) for v in row.get("reverseDependentComponentIds", []) if isinstance(v, str))

    for uid in comp_by_id:
        for vid in dep_sets[uid]:
            if vid not in comp_by_id:
                sys.exit(
                    f"[cone] FATAL: component {uid} lists dependency {vid}, "
                    f"which does not exist in the component index."
                )
            if uid not in rev_sets[vid]:
                sys.exit(
                    f"[cone] FATAL: adjacency inconsistency — "
                    f"{uid}.dependencyComponentIds contains {vid}, but "
                    f"{vid}.reverseDependentComponentIds does not contain {uid}."
                )

        for vid in rev_sets[uid]:
            if vid not in comp_by_id:
                sys.exit(
                    f"[cone] FATAL: component {uid} lists reverse dependent {vid}, "
                    f"which does not exist in the component index."
                )
            if uid not in dep_sets[vid]:
                sys.exit(
                    f"[cone] FATAL: adjacency inconsistency — "
                    f"{uid}.reverseDependentComponentIds contains {vid}, but "
                    f"{vid}.dependencyComponentIds does not contain {uid}."
                )


def verify_edge_semantics(payload: dict, comp_by_id: dict[str, dict]) -> None:
    """Verify that dependencyComponentIds = prerequisites, reverseDependentComponentIds = dependents."""
    orientation = str(payload.get("orientation", ""))
    if EXPECTED_ORIENTATION_MARKER not in orientation:
        sys.exit(
            f"[cone] FATAL: structural-topology.json orientation field does not contain "
            f"expected marker {EXPECTED_ORIENTATION_MARKER!r}.\n"
            f"  Found: {orientation!r}\n"
            f"  The edge convention may have changed. All cone metrics would be silently inverted."
        )

    for cid, row in comp_by_id.items():
        deps = row.get("dependencyComponentIds", [])
        revs = row.get("reverseDependentComponentIds", [])

        if row.get("isRoot") and deps:
            sys.exit(
                f"[cone] FATAL: root component {cid} has non-empty dependencyComponentIds "
                f"({len(deps)} edges). This contradicts the root definition."
            )
        if row.get("isCapstone") and revs:
            sys.exit(
                f"[cone] FATAL: capstone component {cid} has non-empty reverseDependentComponentIds "
                f"({len(revs)} edges). This contradicts the capstone definition."
            )


# ── past / forward cones ─────────────────────────────────────

def past_cone_bfs(apex_cid: str, comp_by_id: dict[str, dict]) -> dict[str, int]:
    """BFS from apex following dependencyComponentIds → Past(a) with shell distances."""
    dist: dict[str, int] = {apex_cid: 0}
    queue = deque([apex_cid])

    while queue:
        u = queue.popleft()
        row = comp_by_id.get(u, {})
        for v in row.get("dependencyComponentIds", []):
            if isinstance(v, str) and v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)

    return dist


def forward_cone_bfs(apex_cid: str, comp_by_id: dict[str, dict]) -> dict[str, int]:
    """BFS from apex following reverseDependentComponentIds → dependents of apex."""
    dist: dict[str, int] = {apex_cid: 0}
    queue = deque([apex_cid])

    while queue:
        u = queue.popleft()
        row = comp_by_id.get(u, {})
        for v in row.get("reverseDependentComponentIds", []):
            if isinstance(v, str) and v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)

    return dist


def shell_decomposition(dist: dict[str, int]) -> dict[int, list[str]]:
    shells: dict[int, list[str]] = defaultdict(list)
    for cid, d in dist.items():
        shells[d].append(cid)
    return dict(sorted(shells.items()))


# ── signatures ───────────────────────────────────────────────

def component_signature(cid: str, comp_by_id: dict[str, dict], depth_tags: dict[str, dict]):
    """Aggregate depth classes, parities, and judgments across a component's members."""
    row = comp_by_id.get(cid, {})
    depths: set[int] = set()
    parities: set[int] = set()
    judgments: set[str] = set()

    for member in _iter_component_members(row):
        tag = depth_tags.get(member, {})
        judgments.add(tag.get("judgment", "untagged"))
        for d in _strict_int_list(tag.get("directDepDepthNats", [])):
            depths.add(d)
            parities.add(d % 2)

    if not judgments:
        judgments.add("untagged")

    return depths, parities, judgments


def precompute_signatures(comp_by_id: dict[str, dict], depth_tags: dict[str, dict]) -> SigCache:
    return {cid: component_signature(cid, comp_by_id, depth_tags) for cid in comp_by_id}


def component_own_parities(cid: str, comp_by_id: dict[str, dict], depth_tags: dict[str, dict]) -> set[int]:
    """Parities derived from each member's own depthNat, not dependency depths."""
    row = comp_by_id.get(cid, {})
    parities: set[int] = set()

    for member in _iter_component_members(row):
        dn = _strict_int(depth_tags.get(member, {}).get("depthNat"))
        if dn is not None:
            parities.add(dn % 2)

    return parities


def precompute_own_parities(comp_by_id: dict[str, dict], depth_tags: dict[str, dict]) -> OwnParityCache:
    return {cid: component_own_parities(cid, comp_by_id, depth_tags) for cid in comp_by_id}


# ── overlays / witnesses ─────────────────────────────────────

def role_overlay(shells: dict[int, list[str]], comp_by_id: dict[str, dict], depth_tags: dict[str, dict]):
    """Per-shell histograms at component granularity."""
    result = {}

    for shell, cids in shells.items():
        judgment_counts: dict[str, int] = defaultdict(int)
        depth_counts: dict[str, int] = defaultdict(int)

        for cid in cids:
            row = comp_by_id.get(cid, {})
            j_bag: dict[str, int] = defaultdict(int)
            d_bag: dict[str, int] = defaultdict(int)

            for member in _iter_component_members(row):
                tag = depth_tags.get(member, {})
                j_bag[str(tag.get("judgment", "untagged"))] += 1
                d_bag[str(tag.get("depth", "untagged"))] += 1

            if not j_bag:
                j_bag["untagged"] = 1
            if not d_bag:
                d_bag["untagged"] = 1

            dominant_j = max(j_bag, key=lambda k: (j_bag[k], k))
            dominant_d = max(d_bag, key=lambda k: (d_bag[k], k))

            judgment_counts[dominant_j] += 1
            depth_counts[dominant_d] += 1

        result[shell] = {
            "size": len(cids),
            "judgments": dict(judgment_counts),
            "depths": dict(depth_counts),
        }

    return result


def find_binding_witnesses(
    past_dist: dict[str, int],
    comp_by_id: dict[str, dict],
    depth_tags: dict[str, dict],
    sig_cache: SigCache | None = None,
):
    """Binding witness = component in Past(a) that
    (a) contains at least one coherence-bearing member,
    (b) spans at least two direct-dependency depth classes.

    This is a local proxy for the chain-level definition in
    docs/causal_cone_formal_definitions.md §5.  It checks condition (3)
    locally but does not verify the two-chain essentiality conditions
    (2) and (3) from the formal definition.
    """
    _sig = (lambda c: sig_cache[c]) if sig_cache else (lambda c: component_signature(c, comp_by_id, depth_tags))

    witnesses = []
    for cid in past_dist:
        depths, parities, judgments = _sig(cid)

        if not (judgments & COHERENCE_ROLES):
            continue
        if len(depths) < 2:
            continue

        row = comp_by_id.get(cid, {})
        witnesses.append(
            {
                "representative": row.get("representative", cid),
                "componentId": cid,
                "shell": past_dist[cid],
                "judgments": sorted(judgments - {"untagged"}),
                "depthClasses": sorted(depths),
                "depthParities": sorted(parities),
                "mixedParity": len(parities) >= 2,
            }
        )

    return witnesses


# ── masses ───────────────────────────────────────────────────

def declaration_mass(
    apex_cid: str,
    comp_by_id: dict[str, dict],
    depth_tags: dict[str, dict],
    sig_cache: SigCache | None = None,
):
    """mass(a) = Σ over coherence-bearing strict descendants:
        w(role) · atten(a, d) / split(d)
    """
    fwd = forward_cone_bfs(apex_cid, comp_by_id)

    total_mass = 0.0
    contributors = 0
    strict_descendants = 0

    for cid, dist in fwd.items():
        if dist == 0:
            continue  # strict descendants only

        strict_descendants += 1
        row = comp_by_id.get(cid, {})
        _, _, judgments = (
            sig_cache[cid] if sig_cache and cid in sig_cache else component_signature(cid, comp_by_id, depth_tags)
        )

        best_w = max((COHERENCE_ROLE_WEIGHTS.get(j, 0) for j in judgments), default=0)
        if best_w == 0:
            continue

        atten = 1.0 / (1 + dist)
        fan_in = len(row.get("dependencyComponentIds", []))
        split = max(1, fan_in)

        total_mass += best_w * atten / split
        contributors += 1

    return total_mass, contributors, strict_descendants


def binding_mass(
    witnesses: list[dict],
    past_dist: dict[str, int],
    comp_by_id: dict[str, dict],
    depth_tags: dict[str, dict],
    own_parity_cache: OwnParityCache | None = None,
):
    """bindmass(a) = Σ over binding witnesses:
        |even-parity pred components| × |odd-parity pred components| / split(c)^2
    """
    _own = (
        (lambda c: own_parity_cache[c])
        if own_parity_cache
        else (lambda c: component_own_parities(c, comp_by_id, depth_tags))
    )

    total = 0.0

    for w in witnesses:
        cid = w["componentId"]
        row = comp_by_id.get(cid, {})
        dep_cids = [d for d in row.get("dependencyComponentIds", []) if d in past_dist]

        even_count = 0
        odd_count = 0

        for dep_cid in dep_cids:
            parities = _own(dep_cid)
            if 0 in parities:
                even_count += 1
            if 1 in parities:
                odd_count += 1

        fan_in = len(row.get("dependencyComponentIds", []))
        split = max(1, fan_in)

        total += (even_count * odd_count) / (split * split)

    return total


# ── exact transitive support inside the cone ─────────────────

def _restricted_reverse_adjacency(past_set: set[str], comp_by_id: dict[str, dict]) -> dict[str, list[str]]:
    """Adjacency within the cone along reverseDependentComponentIds."""
    adj: dict[str, list[str]] = {}
    for cid in past_set:
        row = comp_by_id.get(cid, {})
        adj[cid] = [v for v in row.get("reverseDependentComponentIds", []) if v in past_set]
    return adj


def _toposort_restricted(adj: dict[str, list[str]]) -> list[str]:
    """Topological sort of the restricted DAG."""
    indeg: dict[str, int] = {u: 0 for u in adj}
    for u, vs in adj.items():
        for v in vs:
            indeg[v] = indeg.get(v, 0) + 1

    q = deque(sorted([u for u, d in indeg.items() if d == 0]))
    order: list[str] = []

    while q:
        u = q.popleft()
        order.append(u)
        for v in adj.get(u, []):
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)

    if len(order) != len(adj):
        sys.exit(
            "[cone] FATAL: restricted past-cone subgraph is not acyclic. "
            "The input is expected to be SCC-condensed."
        )

    return order


def _transitive_coh_support(
    past_set: set[str],
    comp_by_id: dict[str, dict],
    depth_tags: dict[str, dict],
    sig_cache: SigCache | None = None,
) -> dict[str, int]:
    """Exact downstream coherence support within the cone.

    Computes, for each node in the cone, the number of distinct coherence-bearing
    downstream nodes reachable via reverseDependentComponentIds while staying in the cone.

    Uses a topological pass with integer bitsets over the restricted DAG.
    """
    _sig = (lambda c: sig_cache[c]) if sig_cache else (lambda c: component_signature(c, comp_by_id, depth_tags))

    past_nodes = sorted(past_set)
    idx_of = {cid: i for i, cid in enumerate(past_nodes)}
    adj = _restricted_reverse_adjacency(past_set, comp_by_id)
    topo = _toposort_restricted(adj)

    is_coh: dict[str, bool] = {}
    for cid in past_nodes:
        _, _, judgments = _sig(cid)
        is_coh[cid] = bool(judgments & COHERENCE_ROLES)

    reach_bits: dict[str, int] = {cid: 0 for cid in past_nodes}

    for u in reversed(topo):
        bits = 0
        for v in adj.get(u, []):
            bits |= reach_bits[v]
            if is_coh.get(v, False):
                bits |= 1 << idx_of[v]
        reach_bits[u] = bits

    return {cid: reach_bits[cid].bit_count() for cid in past_nodes}


def find_boundary_nodes(
    apex_cid: str,
    shells: dict[int, list[str]],
    past_dist: dict[str, int],
    comp_by_id: dict[str, dict],
    depth_tags: dict[str, dict],
    sig_cache: SigCache | None = None,
):
    """Boundary nodes: outermost shell, or low downstream reuse within cone,
    or low transitive coherence support within cone.

    The apex is never classified as a boundary node.
    """
    max_shell = max(shells.keys()) if shells else 0
    outermost = set(shells.get(max_shell, []))
    past_set = set(past_dist.keys())

    coh_reach = _transitive_coh_support(past_set, comp_by_id, depth_tags, sig_cache)

    boundary = []
    for cid in past_dist:
        if cid == apex_cid:
            continue

        row = comp_by_id.get(cid, {})
        desc_in_cone = [d for d in row.get("reverseDependentComponentIds", []) if d in past_set]

        is_outer = cid in outermost
        is_low_outdeg = (len(desc_in_cone) <= 1) and not is_outer
        is_low_coh = coh_reach.get(cid, 0) <= 1

        if is_outer or is_low_outdeg or is_low_coh:
            boundary.append(
                {
                    "componentId": cid,
                    "representative": row.get("representative", ""),
                    "shell": past_dist[cid],
                    "is_outermost": is_outer,
                    "is_low_reuse": is_low_outdeg,
                    "is_low_coherence_support": is_low_coh,
                    "desc_in_cone": len(desc_in_cone),
                    "coh_support": coh_reach.get(cid, 0),
                }
            )

    boundary.sort(key=lambda r: (r["shell"], r["representative"], r["componentId"]))
    return boundary


# ── apex selection ───────────────────────────────────────────

def select_apexes(
    payload,
    comp_by_id,
    comp_by_rep,
    comp_by_member,
    user_apexes: list[str],
    n_default: int = 5,
    policy: str = "capstone_fanin",
    depth_tags: dict[str, dict] | None = None,
    decl_index: dict[str, dict] | None = None,
):
    """Resolve apexes.

    Policies:
      capstone_fanin — top capstones by prerequisite fan-in.  Capstones are sinks,
                       so forward-cone diagnostics are trivially zero under this
                       policy.  Use when backward-cone analysis is the primary goal.
      corridor       — deeper tagged corridor nodes first, then corridor capstones,
                       then general capstones by fan-in.  Preferred default because
                       phase-1 nodes are not necessarily sinks and can exhibit
                       nontrivial forward cones.
    """
    selected: list[str] = []
    seen: set[str] = set()

    def _add(cid: str):
        if cid in comp_by_id and cid not in seen:
            selected.append(cid)
            seen.add(cid)

    if user_apexes:
        for name in user_apexes:
            if name in comp_by_id:
                _add(name)
            elif name in comp_by_rep:
                _add(comp_by_rep[name]["componentId"])
            elif name in comp_by_member:
                _add(comp_by_member[name]["componentId"])
            else:
                print(f"[cone] WARNING: could not resolve apex '{name}'", file=sys.stderr)
        return selected

    if policy == "corridor":
        if depth_tags:
            by_depth: dict[str, dict[str, int]] = defaultdict(dict)
            for name, tag in depth_tags.items():
                row = comp_by_member.get(name)
                if row is None:
                    continue
                cid = row["componentId"]
                depth_label = str(tag.get("depth", "untagged"))
                rev_count = len(comp_by_id.get(cid, {}).get("reverseDependentComponentIds", []))
                prev = by_depth[depth_label].get(cid)
                if prev is None or rev_count > prev:
                    by_depth[depth_label][cid] = rev_count

            # Deepest first: larger DEPTH_PRIORITY first.
            for depth_label in sorted(by_depth, key=lambda d: DEPTH_PRIORITY.get(d, -1), reverse=True):
                candidates = sorted(
                    by_depth[depth_label].items(),
                    key=lambda item: (-item[1], comp_by_id[item[0]].get("representative", item[0])),
                )
                if candidates:
                    _add(candidates[0][0])
                if len(selected) >= n_default:
                    break

        if len(selected) < n_default and decl_index:
            corridor_caps: list[tuple[int, str, str]] = []
            for comp in _require_components(payload):
                if not comp.get("isCapstone"):
                    continue
                cid = comp["componentId"]
                if cid in seen:
                    continue
                rep = comp["representative"]
                module = decl_index.get(rep, {}).get("module", "")
                if any(module == cm or module.startswith(cm + ".") for cm in CORRIDOR_MODULES):
                    fan_in = len(comp.get("dependencyComponentIds", []))
                    corridor_caps.append((-fan_in, rep, cid))

            corridor_caps.sort()
            for _, _, cid in corridor_caps:
                _add(cid)
                if len(selected) >= n_default:
                    break

    if len(selected) < n_default:
        capstones = [
            r
            for r in _require_components(payload)
            if r.get("isCapstone") and r["componentId"] not in seen
        ]
        capstones.sort(
            key=lambda r: (-len(r.get("dependencyComponentIds", [])), r.get("representative", r["componentId"]))
        )
        for r in capstones:
            _add(r["componentId"])
            if len(selected) >= n_default:
                break

    return selected[:n_default]


# ── per-apex analysis ────────────────────────────────────────

def analyze_apex(
    apex_cid: str,
    comp_by_id: dict[str, dict],
    depth_tags: dict[str, dict],
    sig_cache: SigCache | None = None,
    own_parity_cache: OwnParityCache | None = None,
):
    row = comp_by_id.get(apex_cid)
    if row is None:
        raise ValueError(
            f"apex component {apex_cid!r} not found in the component index — stale or invalid component ID"
        )

    rep = row.get("representative", apex_cid)

    past_dist = past_cone_bfs(apex_cid, comp_by_id)
    if len(past_dist) <= 1:
        print(
            f"[cone] WARNING: apex {rep} has trivial past cone (size {len(past_dist)}); "
            f"check whether the component ID is valid and edges are oriented correctly.",
            file=sys.stderr,
        )

    shells = shell_decomposition(past_dist)
    overlay = role_overlay(shells, comp_by_id, depth_tags)
    witnesses = find_binding_witnesses(past_dist, comp_by_id, depth_tags, sig_cache)

    mass, mass_contributors, strict_fwd_size = declaration_mass(apex_cid, comp_by_id, depth_tags, sig_cache)
    bmass = binding_mass(witnesses, past_dist, comp_by_id, depth_tags, own_parity_cache)

    boundary = find_boundary_nodes(apex_cid, shells, past_dist, comp_by_id, depth_tags, sig_cache)

    max_shell = max(shells.keys()) if shells else 0

    is_sink = not row.get("reverseDependentComponentIds")

    return {
        "apex": rep,
        "componentId": apex_cid,
        "is_sink": is_sink,
        "past_cone_size": len(past_dist),
        "max_shell": max_shell,
        "shell_sizes": {k: len(v) for k, v in shells.items()},
        "role_overlay": overlay,
        "binding_witnesses": len(witnesses),
        "binding_witness_sample": witnesses[:10],
        "declaration_mass": round(mass, 4),
        "mass_contributors": mass_contributors,
        "forward_cone_size": strict_fwd_size,
        "binding_mass": round(bmass, 4),
        "boundary_nodes": len(boundary),
        "boundary_sample": boundary[:10],
    }


# ── markdown rendering ───────────────────────────────────────

def render_markdown(results: list[dict], elapsed: float) -> str:
    lines = [
        "# Causal Cone Spectrum",
        "",
        "Per-apex diagnostics on the **SCC-condensed** declaration DAG.",
        "Definitions follow `docs/causal_cone_formal_definitions.md`.",
        "",
    ]

    for r in results:
        sink_note = " *(sink — forward mass is structurally zero)*" if r.get("is_sink") else ""
        lines.extend(
            [
                f"## Apex: `{r['apex']}`{sink_note}",
                "",
                "| Metric | Value |",
                "|---|---|",
                f"| Past cone size | {r['past_cone_size']} |",
                f"| Max shell depth | {r['max_shell']} |",
                f"| Forward cone size | {r['forward_cone_size']} |",
                f"| Declaration mass | {r['declaration_mass']} |",
                f"| Mass contributors | {r['mass_contributors']} |",
                f"| Binding witnesses | {r['binding_witnesses']} |",
                f"| Binding mass | {r['binding_mass']} |",
                f"| Boundary nodes | {r['boundary_nodes']} |",
                "",
            ]
        )

        shell_sizes = r["shell_sizes"]
        if shell_sizes:
            lines.extend(["### Shell Decomposition", "", "| Shell | Size |", "|---|---|"])
            keys = sorted(shell_sizes.keys())
            show = keys[:10]
            if len(keys) > 10:
                show.append(keys[-1])
            for k in show:
                lines.append(f"| {k} | {shell_sizes[k]} |")
            omitted = len(keys) - len(show)
            if omitted > 0:
                lines.append(f"| ... ({omitted} shells omitted) | |")
            lines.append("")

        if r["binding_witness_sample"]:
            lines.extend(
                [
                    "### Binding Witnesses (sample)",
                    "",
                    "| Representative | Shell | Judgments | Depth classes | Mixed parity |",
                    "|---|---|---|---|---|",
                ]
            )
            for w in r["binding_witness_sample"]:
                name = w["representative"][:80]
                lines.append(
                    f"| `{name}` | {w['shell']} | {', '.join(w['judgments'])} | "
                    f"{w['depthClasses']} | {w['mixedParity']} |"
                )
            lines.append("")

        if r["boundary_sample"]:
            lines.extend(
                [
                    "### Boundary Nodes (sample)",
                    "",
                    "| Representative | Shell | Outermost | Low reuse | Low coherence support | Desc in cone | Coh support |",
                    "|---|---|---|---|---|---|---|",
                ]
            )
            for b in r["boundary_sample"]:
                name = b["representative"][:80]
                lines.append(
                    f"| `{name}` | {b['shell']} | {b['is_outermost']} | {b['is_low_reuse']} | "
                    f"{b['is_low_coherence_support']} | {b['desc_in_cone']} | {b['coh_support']} |"
                )
            lines.append("")

        lines.append("")

    lines.append(f"*Computed in {elapsed:.1f}s.*")
    return "\n".join(lines) + "\n"


# ── main ─────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Causal cone spectrum (SCC-condensed DAG)")
    ap.add_argument("--structure", default=DEFAULT_STRUCTURE)
    ap.add_argument("--depth-tags", default=DEFAULT_DEPTH_TAGS)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument(
        "--apex",
        nargs="*",
        default=[],
        help="Apex declaration names or component IDs (default: selected automatically)",
    )
    ap.add_argument("--n-default", type=int, default=5, help="Number of default apexes when none specified")
    ap.add_argument(
        "--selection-policy",
        choices=["capstone_fanin", "corridor"],
        default="corridor",
        help="Apex choice policy (corridor: depth-tagged non-sinks first; capstone_fanin: sinks by prerequisite fan-in)",
    )
    args = ap.parse_args()

    root = repo_root()
    t0 = time.time()

    print("[cone] loading structural topology ...")
    payload, comp_by_id, comp_by_rep, comp_by_member = load_structure(root / args.structure)
    verify_edge_pair_consistency(comp_by_id)
    verify_edge_semantics(payload, comp_by_id)

    depth_tags = load_depth_tags(root / args.depth_tags)
    decl_index = load_decl_index(root / "artifacts" / "dag" / "index" / "decls.jsonl")

    n_comp = len(comp_by_id)
    print(f"[cone] {n_comp} components, {len(depth_tags)} depth-tagged declarations")

    sig_cache = precompute_signatures(comp_by_id, depth_tags)
    own_parity_cache = precompute_own_parities(comp_by_id, depth_tags)
    print(f"[cone] precomputed {len(sig_cache)} component signatures")

    apex_cids = select_apexes(
        payload,
        comp_by_id,
        comp_by_rep,
        comp_by_member,
        args.apex,
        args.n_default,
        args.selection_policy,
        depth_tags,
        decl_index,
    )
    if not apex_cids:
        sys.exit("[cone] FATAL: no apexes resolved. Check the selection policy and artifact contents.")

    print(f"[cone] analyzing {len(apex_cids)} apexes")

    results = []
    for cid in apex_cids:
        rep = comp_by_id.get(cid, {}).get("representative", cid)
        print(f"[cone]   {rep} ...")
        r = analyze_apex(cid, comp_by_id, depth_tags, sig_cache, own_parity_cache)
        print(
            f"[cone]     past={r['past_cone_size']}  shells={r['max_shell']}"
            f"  witnesses={r['binding_witnesses']}  mass={r['declaration_mass']}"
            f"  bmass={r['binding_mass']}  boundary={r['boundary_nodes']}"
        )
        results.append(r)

    elapsed = time.time() - t0
    print(f"[cone] done in {elapsed:.1f}s")

    out = {
        "scope": "SCC-condensed DAG (structural-topology.json)",
        "components": n_comp,
        "apexes_analyzed": len(results),
        "results": results,
        "elapsed_seconds": round(elapsed, 1),
    }

    json_out = root / args.json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(out, indent=2), encoding="utf-8")

    md_out = root / args.md_out
    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(render_markdown(results, elapsed), encoding="utf-8")

    print(f"[cone] wrote {json_out}")
    print(f"[cone] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
