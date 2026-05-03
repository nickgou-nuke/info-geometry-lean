#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, cast

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root

DEFAULT_INPUT_DIR = "artifacts/dag/process-flow"
DEFAULT_JSON_OUT = "reports/dag/semantic-flow-report.json"
DEFAULT_MD_OUT = "reports/dag/semantic-flow-report.md"
EXPECTED_INPUT_SCHEMA_VERSION = 4
REPORT_SCHEMA_VERSION = 1

ROLE_CREDIT: dict[str, int] = {
    "head": 5,
    "transportArg": 6,
    "requiredArg": 3,
    "witness": 2,
    "closureSupport": 1,
    "ornament": 0,
    "remoteSupport": 0,
    "unknown": 0,
}

BOUNDARY_CREDIT: dict[str, int] = {
    "bridge": 2,
    "localInterface": 1,
    "internal": 0,
    "capstone": 0,
    "mixed": 0,
    "unclear": 0,
}

DEFECT_SEVERITY: dict[str, int] = {
    "illicitBoundaryCrossing": 5,
    "regressiveFlow": 5,
    "boundaryBypass": 4,
    "remoteAttachment": 3,
    "failedLocalFactorization": 3,
    "mixedPolarity": 2,
    "unclearPolarity": 2,
    "typeOnlySupport": 1,
    "unresolvedComparison": 1,
}

EPS = 1e-9

JsonDict = dict[str, Any]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate a semantic flow report over process-flow artifacts using "
            "scalable graph algorithms (signed diffusion, entropy production, SCC loop obstruction)."
        )
    )
    parser.add_argument("--input-dir", default=DEFAULT_INPUT_DIR, help="Directory containing process-flow JSONL artifacts.")
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="JSON summary output path.")
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT, help="Markdown summary output path.")
    parser.add_argument(
        "--allow-missing-input",
        action="store_true",
        help="If artifacts are missing, write an empty report and exit 0 instead of failing.",
    )
    parser.add_argument("--iterations", type=int, default=12, help="Diffusion/relaxation iteration budget.")
    parser.add_argument("--alpha", type=float, default=0.2, help="Diffusion injection coefficient in [0, 1].")
    parser.add_argument("--top", type=int, default=20, help="Top-N rows per section.")
    return parser.parse_args()


def load_jsonl(path: Path) -> list[JsonDict]:
    rows: list[JsonDict] = []
    if not path.exists():
        return rows
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line:
            continue
        obj = json.loads(line)
        if isinstance(obj, dict):
            rows.append(cast(JsonDict, obj))
    return rows


def validate_schema(rows: list[JsonDict], label: str, expected: int) -> None:
    if not rows:
        return
    versions = {row.get("schemaVersion") for row in rows}
    if versions != {expected}:
        raise SystemExit(
            f"unexpected {label} schemaVersion set {sorted(str(v) for v in versions)!r}; expected only {expected}"
        )


def edge_use_has_value(edge_use: str) -> bool:
    return edge_use in {"valueOnly", "both"}


def edge_use_has_type(edge_use: str) -> bool:
    return edge_use in {"typeOnly", "both"}


def compute_transport_credit(edge: JsonDict) -> int:
    edge_use = str(edge.get("edgeUse", ""))
    base = 4 if edge_use_has_value(edge_use) else 1 if edge_use_has_type(edge_use) else 0
    role = str(edge.get("inferredRole", "unknown"))
    boundary = str(edge.get("inferredBoundary", "unclear"))
    return base + ROLE_CREDIT.get(role, 0) + BOUNDARY_CREDIT.get(boundary, 0)


def compute_defect_debt(edge: JsonDict) -> int:
    tags = edge.get("defectTags", [])
    if not isinstance(tags, list):
        return 0
    return sum(DEFECT_SEVERITY.get(str(tag), 1) for tag in tags)


def chirality_sign_from_polarity(polarity: str) -> int:
    if polarity in {"descending", "sameLayer"}:
        return 1
    if polarity in {"remote", "regressive", "mixed"}:
        return -1
    return 0


def stable_rate(transport_credit: int, defect_debt: int) -> float:
    return float(1.0 + max(0, transport_credit) + 0.5 * max(0, defect_debt))


def build_index(
    flow_edges: list[JsonDict],
    process_events: list[JsonDict],
) -> tuple[list[str], dict[str, int], list[str], dict[str, str]]:
    nodes: set[str] = set()
    modules: dict[str, str] = {}
    boundaries: dict[str, str] = {}

    for edge in flow_edges:
        src = str(edge.get("src", ""))
        dst = str(edge.get("dst", ""))
        if src:
            nodes.add(src)
        if dst:
            nodes.add(dst)

    for ev in process_events:
        node = str(ev.get("node", ""))
        if not node:
            continue
        nodes.add(node)
        modules[node] = str(ev.get("module", ""))
        boundaries[node] = str(ev.get("boundaryClass", ""))

    ordered = sorted(nodes)
    node_to_idx = {name: i for i, name in enumerate(ordered)}
    idx_to_node = ordered
    idx_to_module = [modules.get(name, "") for name in ordered]
    idx_to_boundary = {name: boundaries.get(name, "") for name in ordered}
    return idx_to_node, node_to_idx, idx_to_module, idx_to_boundary


def diffusion_relaxation(
    n: int,
    src_idx: list[int],
    dst_idx: list[int],
    edge_rate: list[float],
    edge_charge: list[float],
    iterations: int,
    alpha: float,
) -> tuple[list[float], float]:
    q = [0.0] * n
    out_rate = [0.0] * n
    for u, v, rate, charge in zip(src_idx, dst_idx, edge_rate, edge_charge):
        q[u] += charge
        q[v] -= charge
        out_rate[u] += rate

    x = [0.0] * n
    iters = max(1, iterations)
    alpha = max(0.0, min(1.0, alpha))
    damp = 1.0 - alpha
    max_delta = 0.0

    for _ in range(iters):
        nxt = [alpha * q_i for q_i in q]
        for i in range(n):
            if out_rate[i] <= EPS:
                nxt[i] += damp * x[i]
        for u, v, rate in zip(src_idx, dst_idx, edge_rate):
            if out_rate[u] > EPS:
                nxt[v] += damp * (rate / out_rate[u]) * x[u]
        delta = max(abs(a - b) for a, b in zip(nxt, x))
        max_delta = max(max_delta, delta)
        x = nxt
    return x, max_delta


def kosaraju_scc(n: int, src_idx: list[int], dst_idx: list[int]) -> tuple[list[int], list[int]]:
    adj: list[list[int]] = [[] for _ in range(n)]
    radj: list[list[int]] = [[] for _ in range(n)]
    for u, v in zip(src_idx, dst_idx):
        adj[u].append(v)
        radj[v].append(u)

    visited = [False] * n
    order: list[int] = []

    for start in range(n):
        if visited[start]:
            continue
        stack: list[tuple[int, int]] = [(start, 0)]
        visited[start] = True
        while stack:
            node, nxt = stack[-1]
            if nxt < len(adj[node]):
                nbr = adj[node][nxt]
                stack[-1] = (node, nxt + 1)
                if not visited[nbr]:
                    visited[nbr] = True
                    stack.append((nbr, 0))
            else:
                order.append(node)
                stack.pop()

    comp = [-1] * n
    comp_sizes: list[int] = []
    cid = 0
    for start in reversed(order):
        if comp[start] != -1:
            continue
        size = 0
        stack = [start]
        comp[start] = cid
        while stack:
            node = stack.pop()
            size += 1
            for nbr in radj[node]:
                if comp[nbr] == -1:
                    comp[nbr] = cid
                    stack.append(nbr)
        comp_sizes.append(size)
        cid += 1
    return comp, comp_sizes


def signed_component_frustration(
    n: int,
    src_idx: list[int],
    dst_idx: list[int],
    edge_sign: list[int],
) -> list[JsonDict]:
    # Z2 gauge / Wilson-style frustration proxy on the undirected shadow.
    # Complexity: O(V + E).
    adj: list[list[tuple[int, int]]] = [[] for _ in range(n)]
    for u, v, s in zip(src_idx, dst_idx, edge_sign):
        sig = s if s != 0 else 1
        adj[u].append((v, sig))
        adj[v].append((u, sig))

    spin = [0] * n
    comp_id = [-1] * n
    cid = 0

    for start in range(n):
        if comp_id[start] != -1:
            continue
        stack = [start]
        comp_id[start] = cid
        spin[start] = 1
        while stack:
            u = stack.pop()
            for v, sig in adj[u]:
                expected = spin[u] * sig
                if comp_id[v] == -1:
                    comp_id[v] = cid
                    spin[v] = expected
                    stack.append(v)
                elif spin[v] == 0:
                    spin[v] = expected
        cid += 1

    node_count = [0] * cid
    edge_count = [0] * cid
    frustrated = [0] * cid
    for c in comp_id:
        node_count[c] += 1

    for u, v, s in zip(src_idx, dst_idx, edge_sign):
        c = comp_id[u]
        if c != comp_id[v]:
            continue
        sig = s if s != 0 else 1
        edge_count[c] += 1
        if spin[u] * sig != spin[v]:
            frustrated[c] += 1

    rows: list[JsonDict] = []
    for c in range(cid):
        if edge_count[c] == 0:
            continue
        ratio = frustrated[c] / max(1, edge_count[c])
        rows.append(
            {
                "componentId": c,
                "nodeCount": node_count[c],
                "edgeCount": edge_count[c],
                "frustratedEdgeCount": frustrated[c],
                "wilsonFrustrationProxy": ratio,
            }
        )
    return rows


def markdown_table(headers: list[str], rows: list[list[Any]]) -> str:
    if not rows:
        return "_None._"
    out = ["| " + " | ".join(headers) + " |", "| " + " | ".join(["---"] * len(headers)) + " |"]
    for row in rows:
        out.append("| " + " | ".join(str(x) for x in row) + " |")
    return "\n".join(out)


def main() -> int:
    args = parse_args()
    root = repo_root()
    input_dir = normalize_user_path(args.input_dir, root / DEFAULT_INPUT_DIR)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    flow_edges = load_jsonl(input_dir / "flow-edges.jsonl")
    process_events = load_jsonl(input_dir / "process-events.jsonl")
    if not flow_edges:
        if args.allow_missing_input:
            print(f"[generate_semantic_flow_report] no flow edges found under {input_dir}, skipping.", flush=True)
            with open(md_out, "w", encoding="utf-8") as f:
                f.write("# Semantic Flow Report (Skipped)\nNo artifacts found; clean empty input.\n")
            with open(json_out, "w", encoding="utf-8") as f:
                json.dump({"status": "skipped", "reason": "no artifacts", "summary": {}}, f)
            return 0
        raise SystemExit(f"no flow edges found under {input_dir}")

    validate_schema(flow_edges, "flow-edges", EXPECTED_INPUT_SCHEMA_VERSION)
    validate_schema(process_events, "process-events", EXPECTED_INPUT_SCHEMA_VERSION)

    idx_to_node, node_to_idx, idx_to_module, boundary_by_node = build_index(flow_edges, process_events)
    n = len(idx_to_node)

    src_idx: list[int] = []
    dst_idx: list[int] = []
    edge_rate: list[float] = []
    edge_flux: list[float] = []
    edge_debt: list[int] = []
    edge_credit: list[int] = []
    edge_sign: list[int] = []
    edge_rows: list[JsonDict] = []

    for edge in flow_edges:
        src = str(edge.get("src", ""))
        dst = str(edge.get("dst", ""))
        if src not in node_to_idx or dst not in node_to_idx:
            continue
        u = node_to_idx[src]
        v = node_to_idx[dst]
        credit = compute_transport_credit(edge)
        debt = compute_defect_debt(edge)
        polarity = str(edge.get("inferredPolarity", ""))
        sign = chirality_sign_from_polarity(polarity)
        rate = stable_rate(credit, debt)
        flux = float(sign * (1 + debt))

        src_idx.append(u)
        dst_idx.append(v)
        edge_rate.append(rate)
        edge_flux.append(flux)
        edge_credit.append(credit)
        edge_debt.append(debt)
        edge_sign.append(sign)
        edge_rows.append(edge)

    x, max_delta = diffusion_relaxation(
        n=n,
        src_idx=src_idx,
        dst_idx=dst_idx,
        edge_rate=edge_rate,
        edge_charge=edge_flux,
        iterations=args.iterations,
        alpha=args.alpha,
    )

    comp, comp_sizes = kosaraju_scc(n, src_idx, dst_idx)
    harmonic_l1 = [0.0] * len(comp_sizes)
    harmonic_sum = [0.0] * len(comp_sizes)
    harmonic_edges = [0] * len(comp_sizes)
    node_harmonic_incident = [0.0] * n

    edge_obstruction_rows: list[JsonDict] = []
    for i, (u, v, flux, debt, sign, edge) in enumerate(
        zip(src_idx, dst_idx, edge_flux, edge_debt, edge_sign, edge_rows)
    ):
        grad = x[u] - x[v]
        residual = flux - grad
        cid = comp[u]
        in_loop = comp[u] == comp[v] and (comp_sizes[cid] > 1 or u == v)
        if in_loop:
            mag = abs(residual)
            harmonic_l1[cid] += mag
            harmonic_sum[cid] += residual
            harmonic_edges[cid] += 1
            node_harmonic_incident[u] += mag
            node_harmonic_incident[v] += mag
        edge_obstruction_rows.append(
            {
                "src": idx_to_node[u],
                "dst": idx_to_node[v],
                "moduleSrc": idx_to_module[u],
                "moduleDst": idx_to_module[v],
                "polarity": str(edge.get("inferredPolarity", "")),
                "role": str(edge.get("inferredRole", "")),
                "boundary": str(edge.get("inferredBoundary", "")),
                "defectDebt": debt,
                "transportCredit": edge_credit[i],
                "signedFlux": flux,
                "gradient": grad,
                "residual": residual,
                "obstructionScore": abs(residual) + 0.5 * debt,
                "inLoopSCC": in_loop,
                "sccId": cid if in_loop else -1,
                "chiralitySign": sign,
            }
        )

    # Schnakenberg entropy production on unordered node pairs.
    pair_rates: dict[tuple[int, int], list[float]] = {}
    for u, v, rate in zip(src_idx, dst_idx, edge_rate):
        a, b = (u, v) if u <= v else (v, u)
        rec = pair_rates.setdefault((a, b), [0.0, 0.0])  # [a->b, b->a]
        if u == a and v == b:
            rec[0] += rate
        else:
            rec[1] += rate

    pair_entropy_rows: list[JsonDict] = []
    node_entropy = [0.0] * n
    total_entropy = 0.0
    for (a, b), (rab, rba) in pair_rates.items():
        fwd = max(rab, EPS)
        rev = max(rba, EPS)
        sigma = (fwd - rev) * math.log(fwd / rev)
        if sigma < 0.0:
            sigma = 0.0
        total_entropy += sigma
        node_entropy[a] += 0.5 * sigma
        node_entropy[b] += 0.5 * sigma
        pair_entropy_rows.append(
            {
                "nodeA": idx_to_node[a],
                "nodeB": idx_to_node[b],
                "rateAB": rab,
                "rateBA": rba,
                "entropyProduction": sigma,
                "rateAsymmetry": abs(rab - rba),
            }
        )

    scc_rows: list[JsonDict] = []
    for cid, size in enumerate(comp_sizes):
        if size <= 1:
            continue
        l1 = harmonic_l1[cid]
        signed = harmonic_sum[cid]
        wilson = abs(signed) / max(l1, EPS)
        scc_rows.append(
            {
                "sccId": cid,
                "size": size,
                "loopEdgeCount": harmonic_edges[cid],
                "harmonicMassL1": l1,
                "holonomyCharge": signed,
                "wilsonHolonomyProxy": wilson,
            }
        )

    frustration_rows = signed_component_frustration(
        n=n,
        src_idx=src_idx,
        dst_idx=dst_idx,
        edge_sign=edge_sign,
    )

    node_rows: list[JsonDict] = []
    for i, name in enumerate(idx_to_node):
        score = abs(x[i]) + 0.25 * node_harmonic_incident[i] + 0.1 * node_entropy[i]
        node_rows.append(
            {
                "node": name,
                "module": idx_to_module[i],
                "boundaryClass": boundary_by_node.get(name, ""),
                "chiralPotential": x[i],
                "harmonicIncidentMass": node_harmonic_incident[i],
                "entropyIncident": node_entropy[i],
                "obstructionPotential": score,
            }
        )

    top = max(1, int(args.top))
    top_sources = sorted(node_rows, key=lambda r: (-float(r["chiralPotential"]), r["node"]))[:top]
    top_sinks = sorted(node_rows, key=lambda r: (float(r["chiralPotential"]), r["node"]))[:top]
    top_obstruction_nodes = sorted(node_rows, key=lambda r: (-float(r["obstructionPotential"]), r["node"]))[:top]
    top_obstruction_edges = sorted(
        edge_obstruction_rows, key=lambda r: (-float(r["obstructionScore"]), r["src"], r["dst"])
    )[:top]
    top_entropy_pairs = sorted(
        pair_entropy_rows, key=lambda r: (-float(r["entropyProduction"]), r["nodeA"], r["nodeB"])
    )[:top]
    top_scc = sorted(
        scc_rows, key=lambda r: (-float(r["harmonicMassL1"]), -int(r["size"]), int(r["sccId"]))
    )[:top]
    top_frustration = sorted(
        frustration_rows,
        key=lambda r: (-float(r["wilsonFrustrationProxy"]), -int(r["frustratedEdgeCount"]), -int(r["edgeCount"])),
    )[:top]

    polarity_counter = Counter(str(edge.get("inferredPolarity", "")) for edge in edge_rows)
    defect_counter = Counter()
    for edge in edge_rows:
        tags = edge.get("defectTags", [])
        if isinstance(tags, list):
            for tag in tags:
                defect_counter[str(tag)] += 1

    summary: JsonDict = {
        "schemaVersion": REPORT_SCHEMA_VERSION,
        "inputSchemaVersion": EXPECTED_INPUT_SCHEMA_VERSION,
        "nodeCount": n,
        "edgeCount": len(edge_rows),
        "sccCount": len(comp_sizes),
        "nontrivialSccCount": sum(1 for s in comp_sizes if s > 1),
        "iterations": int(args.iterations),
        "alpha": float(args.alpha),
        "maxDelta": max_delta,
        "totalEntropyProduction": total_entropy,
        "totalHarmonicMass": float(sum(harmonic_l1)),
        "totalFrustratedEdges": int(sum(int(row["frustratedEdgeCount"]) for row in frustration_rows)),
    }

    payload: JsonDict = {
        "summary": summary,
        "polarityHistogram": dict(sorted(polarity_counter.items())),
        "defectTagHistogram": dict(sorted(defect_counter.items())),
        "topChiralSources": top_sources,
        "topChiralSinks": top_sinks,
        "topObstructionNodes": top_obstruction_nodes,
        "topObstructionEdges": top_obstruction_edges,
        "topEntropyPairs": top_entropy_pairs,
        "topLoopObstructions": top_scc,
        "topWilsonFrustration": top_frustration,
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    md_lines: list[str] = []
    md_lines.append("# Semantic Flow Report")
    md_lines.append("")
    md_lines.append("This report interprets process-flow artifacts as a signed transport graph with scalable analyzers.")
    md_lines.append("")
    md_lines.append("## Scaling")
    md_lines.append("")
    md_lines.append("- Preprocessing, SCC, entropy, residual scoring: `O(V + E)`.")
    md_lines.append("- Signed diffusion / relaxation: `O(iterations * E)`.")
    md_lines.append("- No full cycle enumeration; loop effects are SCC-level holonomy proxies.")
    md_lines.append("")
    md_lines.append("## Summary")
    md_lines.append("")
    md_lines.extend(
        [
            f"- nodes: `{summary['nodeCount']}`",
            f"- edges: `{summary['edgeCount']}`",
            f"- SCCs: `{summary['sccCount']}` (nontrivial: `{summary['nontrivialSccCount']}`)",
            f"- diffusion iterations: `{summary['iterations']}` with `alpha={summary['alpha']}`",
            f"- diffusion max delta: `{summary['maxDelta']:.6g}`",
            f"- total entropy production (pairwise): `{summary['totalEntropyProduction']:.6g}`",
            f"- total loop harmonic mass proxy: `{summary['totalHarmonicMass']:.6g}`",
            f"- total frustrated edges (Wilson proxy): `{summary['totalFrustratedEdges']}`",
        ]
    )
    md_lines.append("")
    md_lines.append("## Top Chiral Sources")
    md_lines.append("")
    md_lines.append(
        markdown_table(
            ["Node", "Potential", "Obstruction", "Harmonic", "Entropy", "Boundary"],
            [
                [
                    row["node"],
                    f"{float(row['chiralPotential']):.5g}",
                    f"{float(row['obstructionPotential']):.5g}",
                    f"{float(row['harmonicIncidentMass']):.5g}",
                    f"{float(row['entropyIncident']):.5g}",
                    row["boundaryClass"],
                ]
                for row in top_sources
            ],
        )
    )
    md_lines.append("")
    md_lines.append("## Top Chiral Sinks")
    md_lines.append("")
    md_lines.append(
        markdown_table(
            ["Node", "Potential", "Obstruction", "Harmonic", "Entropy", "Boundary"],
            [
                [
                    row["node"],
                    f"{float(row['chiralPotential']):.5g}",
                    f"{float(row['obstructionPotential']):.5g}",
                    f"{float(row['harmonicIncidentMass']):.5g}",
                    f"{float(row['entropyIncident']):.5g}",
                    row["boundaryClass"],
                ]
                for row in top_sinks
            ],
        )
    )
    md_lines.append("")
    md_lines.append("## Top Non-Equilibrium Pairs (Entropy Production)")
    md_lines.append("")
    md_lines.append(
        markdown_table(
            ["Pair", "sigma", "rateAB", "rateBA", "|delta rate|"],
            [
                [
                    f"{row['nodeA']} <-> {row['nodeB']}",
                    f"{float(row['entropyProduction']):.5g}",
                    f"{float(row['rateAB']):.5g}",
                    f"{float(row['rateBA']):.5g}",
                    f"{float(row['rateAsymmetry']):.5g}",
                ]
                for row in top_entropy_pairs
            ],
        )
    )
    md_lines.append("")
    md_lines.append("## Top Loop Obstructions (SCC Holonomy Proxy)")
    md_lines.append("")
    md_lines.append(
        markdown_table(
            ["SCC", "size", "loopEdges", "harmonicL1", "holonomyCharge", "wilsonProxy"],
            [
                [
                    row["sccId"],
                    row["size"],
                    row["loopEdgeCount"],
                    f"{float(row['harmonicMassL1']):.5g}",
                    f"{float(row['holonomyCharge']):.5g}",
                    f"{float(row['wilsonHolonomyProxy']):.5g}",
                ]
                for row in top_scc
            ],
        )
    )
    md_lines.append("")
    md_lines.append("## Top Wilson Frustration Components (Undirected Signed Proxy)")
    md_lines.append("")
    md_lines.append(
        markdown_table(
            ["Component", "nodes", "edges", "frustrated", "frustrationRatio"],
            [
                [
                    row["componentId"],
                    row["nodeCount"],
                    row["edgeCount"],
                    row["frustratedEdgeCount"],
                    f"{float(row['wilsonFrustrationProxy']):.5g}",
                ]
                for row in top_frustration
            ],
        )
    )
    md_lines.append("")
    md_lines.append("## Top Obstruction Corridors (Edges)")
    md_lines.append("")
    md_lines.append(
        markdown_table(
            ["Edge", "Score", "Residual", "Debt", "Role", "Boundary", "Polarity", "LoopSCC"],
            [
                [
                    f"{row['src']} -> {row['dst']}",
                    f"{float(row['obstructionScore']):.5g}",
                    f"{float(row['residual']):.5g}",
                    row["defectDebt"],
                    row["role"],
                    row["boundary"],
                    row["polarity"],
                    row["sccId"] if row["inLoopSCC"] else "-",
                ]
                for row in top_obstruction_edges
            ],
        )
    )
    md_lines.append("")

    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text("\n".join(md_lines), encoding="utf-8")

    print(
        f"[generate_semantic_flow_report] edges={len(edge_rows)} nodes={n} scc={len(comp_sizes)} "
        f"nontrivial_scc={summary['nontrivialSccCount']} wrote {json_out} {md_out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
