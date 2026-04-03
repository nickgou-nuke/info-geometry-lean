#!/usr/bin/env python3
"""Global spectral report on the undirected shadow of the declaration DAG.

Computes combinatorial Hodge invariants on the *symmetrised* dependency
graph (L = D − A, undirected). This is a fast diagnostic tool; it does
**not** operate on the SCC-condensed DAG nor compute Drazin or Moore-Penrose
inverses of the directed Laplacian.

Invariants computed:
- b₀  (exact, via connected_components)
- b₁  bounds from Euler–Poincaré on the transitive-triangle 2-complex
- Fiedler value λ₂ (shift-invert eigsh on largest CC)
- Kirchhoff index K = n·tr(L⁺) via Hutchinson trace + CG
- Effective resistance samples via CG on projected Laplacian
- Frobenius asymmetry ‖L_dir − L_dirᵀ‖/‖L_dir‖
- RepDepth parity-mixing score (sparse; only meaningful when many nodes tagged)

Pseudoinverse method:
  L⁺ = (L + J/n)⁻¹ − J/n   where J = 11ᵀ.
  Practically: CG on the invertible system (L + J/n)x = b, implemented
  matrix-free via scipy.sparse.linalg.LinearOperator.

Relation to Lean formalisation (motivation, not directly computed here):
  lean/InfoGeometry/Singular/Drazin.lean        — IsDrazinInverse
  lean/InfoGeometry/Canonical/MoorePenrose.lean  — IsMoorePenroseInverse, chiralAnomaly
  lean/DAG/GraphHodge.lean                       — combinatorial Laplacians, Dirac, chiral split
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy import sparse
from scipy.sparse.csgraph import connected_components
from scipy.sparse.linalg import LinearOperator, cg, eigsh

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pathing import repo_root

DEFAULT_META = "artifacts/dag/index/meta.json"
DEFAULT_GRAPH = "artifacts/dag/full_graph.json"
DEFAULT_DEPTH_TAGS = "artifacts/dag/representation-depth-tags.json"
DEFAULT_MD_OUT = "reports/dag/graph-hodge-spectrum.md"
DEFAULT_JSON_OUT = "reports/dag/graph-hodge-spectrum.json"

DEPTH_ORDER = ["count", "projective", "operator", "krein", "transport", "thermo"]


# ── graph loading ────────────────────────────────────────────

def load_graph(path: Path):
    obj = json.loads(path.read_text())
    return obj["nodes"], obj["forward"]


def load_depth_tags(path: Path) -> dict[str, int]:
    if not path.exists():
        return {}
    obj = json.loads(path.read_text())
    depth_map: dict[str, int] = {}
    entries = obj.get("declarations", obj.get("tags", obj)) if isinstance(obj, dict) else obj
    for entry in entries:
        name = entry.get("name", "")
        tag = entry.get("depth", entry.get("tag", ""))
        if tag in DEPTH_ORDER:
            depth_map[name] = DEPTH_ORDER.index(tag)
    return depth_map


# ── simplicial complex ──────────────────────────────────────

def build_complex(forward):
    edges: list[tuple[int, int]] = []
    edge_idx: dict[tuple[int, int], int] = {}

    for u, adj in enumerate(forward):
        for item in adj:
            v = item[0] if isinstance(item, list) else item
            e = (u, int(v))
            if e not in edge_idx:
                edge_idx[e] = len(edges)
                edges.append(e)

    faces: list[tuple[int, int, int]] = []
    for i, (u, v) in enumerate(edges):
        for item in forward[v]:
            w = item[0] if isinstance(item, list) else item
            w = int(w)
            if (u, w) in edge_idx:
                j = edge_idx[(v, w)]
                k = edge_idx[(u, w)]
                faces.append((i, j, k))

    return edges, edge_idx, faces


# ── symmetric graph Laplacian ───────────────────────────────

def graph_laplacian_sparse(n_nodes: int, edges: list[tuple[int, int]]):
    """Symmetric graph Laplacian L = D - A (undirected).  O(E)."""
    row, col, data = [], [], []
    deg = np.zeros(n_nodes)
    for u, v in edges:
        row.extend([u, v]); col.extend([v, u]); data.extend([-1.0, -1.0])
        deg[u] += 1; deg[v] += 1
    for i in range(n_nodes):
        row.append(i); col.append(i); data.append(deg[i])
    return sparse.csr_matrix((data, (row, col)), shape=(n_nodes, n_nodes))


# ── directed Laplacian ──────────────────────────────────────

def directed_laplacian_sparse(n_nodes: int, edges: list[tuple[int, int]]):
    """Directed Laplacian L_dir = D_out - A.  Non-symmetric."""
    row, col, data = [], [], []
    out_deg = np.zeros(n_nodes)
    for u, v in edges:
        row.append(u); col.append(v); data.append(-1.0)
        out_deg[u] += 1
    for i in range(n_nodes):
        row.append(i); col.append(i); data.append(out_deg[i])
    return sparse.csr_matrix((data, (row, col)), shape=(n_nodes, n_nodes))


# ── Fiedler value (spectral gap) ────────────────────────────

def fiedler_value(L_cc, n_cc: int):
    """Spectral gap of a connected component via shift-invert."""
    if n_cc <= 2:
        return None
    if n_cc <= 1024:
        eigs = np.sort(np.linalg.eigvalsh(L_cc.toarray()))
        nz = eigs[eigs > 1e-10]
        return float(nz[0]) if len(nz) > 0 else None
    try:
        vals = eigsh(L_cc.astype(float), k=min(6, n_cc - 2),
                     sigma=1e-6, which="LM",
                     return_eigenvectors=False, maxiter=300)
        vals = np.sort(np.abs(vals))
        nz = vals[vals > 1e-8]
        return float(nz[0]) if len(nz) > 0 else None
    except Exception:
        return None


def largest_eigenvalue(L, n: int):
    if n <= 2:
        return None
    try:
        vals = eigsh(L.astype(float), k=1, which="LM",
                     return_eigenvectors=False, maxiter=200)
        return float(np.max(np.abs(vals)))
    except Exception:
        return None


# ── Moore-Penrose pseudoinverse via CG ──────────────────────

def _cg_projected(L, b, n_cc: int, rtol: float = 1e-6, maxiter: int = 500):
    """Solve L⁺·b via the rank-one corrected system (L + J/n).

    Identity:  L⁺ = (L + J/n)⁻¹ − J/n   where J = 11ᵀ.
    Since b is projected off the kernel, the J/n subtraction
    has no effect and we simply solve (L + J/n) x = b_proj.
    The operator (L + J/n) is applied matrix-free.
    """
    n = n_cc
    ones = np.ones(n)
    b_proj = b - ones * (np.sum(b) / n)
    if np.linalg.norm(b_proj) < 1e-14:
        return np.zeros(n)

    def matvec(x):
        return L @ x + ones * (np.sum(x) / n)   # (L + J/n) x

    A = LinearOperator((n, n), matvec=matvec, dtype=float)
    # Exact diagonal of (L + J/n) is diag(L) + 1/n
    diag = L.diagonal().astype(float) + 1.0 / n
    diag[diag < 1e-12] = 1.0
    M = LinearOperator((n, n), matvec=lambda x: x / diag, dtype=float)
    
    x, info = cg(A, b_proj, rtol=rtol, maxiter=maxiter, M=M)
    if info != 0:
        return None
    x -= ones * (np.sum(x) / n)
    return x


def kirchhoff_index_hutchinson(L, n_cc: int, n_probes: int = 30, seed: int = 42):
    """Kirchhoff index K = n·tr(L⁺) via Hutchinson trace estimator.

    Uses random ±1 probes and CG: tr(L⁺) ≈ (1/m) Σ zᵀ L⁺ z.
    """
    if n_cc <= 1:
        return 0.0, True
    rng = np.random.default_rng(seed)
    traces = []
    for _ in range(n_probes):
        z = rng.choice([-1.0, 1.0], size=n_cc)
        x = _cg_projected(L, z, n_cc)
        if x is None:
            continue
        traces.append(np.dot(z, x))
    if not traces:
        return None, False
    return float(n_cc * np.mean(traces)), True


def effective_resistance_samples(L, n_cc: int, pairs: list[tuple[int, int]]):
    """R(u,v) = (e_u - e_v)^T L^+ (e_u - e_v) via direct CG."""
    results = []
    for u, v in pairs:
        b = np.zeros(n_cc, dtype=float)
        b[u] = 1.0
        b[v] = -1.0
        x = _cg_projected(L, b, n_cc)
        r = None if x is None else float(np.dot(b, x))
        results.append((u, v, r))
    return results


# ── Directed asymmetry score ────────────────────────────────

def directed_asymmetry_score(L_dir):
    """Frobenius asymmetry ‖L−Lᵀ‖_F / ‖L‖_F of the directed Laplacian."""
    diff = L_dir - L_dir.T
    asym_norm = sparse.linalg.norm(diff, "fro")
    total_norm = sparse.linalg.norm(L_dir, "fro")
    return float(asym_norm / total_norm) if total_norm > 1e-15 else 0.0


# ── chiral grading ──────────────────────────────────────────

def build_chiral_signs(n_nodes: int, depth_map: dict[str, int], nodes: list[str]):
    signs = np.ones(n_nodes)
    tagged = 0
    for i, name in enumerate(nodes):
        d = depth_map.get(name, -1)
        if d >= 0:
            signs[i] = 1.0 if d % 2 == 0 else -1.0
            tagged += 1
    return signs, tagged


def check_parity_mixing(vertex_signs, edges):
    """Count edges whose endpoints have the same parity sign."""
    same_parity = 0
    for u, v in edges:
        if vertex_signs[u] + vertex_signs[v] != 0.0:
            same_parity += 1
    return same_parity, len(edges)


# ── toy-graph sanity test ───────────────────────────────────

def sanity_check():
    """Verify L⁺ computation on small graphs with known analytical answers.

    Path P₃ (0-1-2):   L = [[1,-1,0],[-1,2,-1],[0,-1,1]]
      L⁺ = (L + J/3)⁻¹ − J/3.   Analytical L⁺ has tr(L⁺) = 4/3.
      Kirchhoff K = 3 · tr(L⁺) = 4.

    Complete K₄:  L = 4I − J₄.   L⁺ = (1/4)(I − J/4).  tr(L⁺) = 3/4.
      K = 4 · 3/4 = 3.
    """
    ok = True

    # ── P₃ ──
    p3_edges = [(0, 1), (1, 2)]
    L_p3 = graph_laplacian_sparse(3, p3_edges)
    # trace via direct solve for all basis vectors
    tr_pinv = 0.0
    for i in range(3):
        ei = np.zeros(3); ei[i] = 1.0
        x = _cg_projected(L_p3, ei, 3)
        if x is None:
            print("[sanity] FAIL: CG failed on P3")
            ok = False; break
        tr_pinv += x[i]
    else:
        K_p3 = 3 * tr_pinv
        if abs(K_p3 - 4.0) > 0.05:
            print(f"[sanity] FAIL: P₃ Kirchhoff = {K_p3:.6f}, expected 4.0")
            ok = False
        else:
            print(f"[sanity] OK:   P₃ Kirchhoff = {K_p3:.6f} ≈ 4.0")

    # ── K₄ ──
    k4_edges = [(i, j) for i in range(4) for j in range(i+1, 4)]
    L_k4 = graph_laplacian_sparse(4, k4_edges)
    tr_pinv = 0.0
    for i in range(4):
        ei = np.zeros(4); ei[i] = 1.0
        x = _cg_projected(L_k4, ei, 4)
        if x is None:
            print("[sanity] FAIL: CG failed on K4")
            ok = False; break
        tr_pinv += x[i]
    else:
        K_k4 = 4 * tr_pinv
        if abs(K_k4 - 3.0) > 0.05:
            print(f"[sanity] FAIL: K₄ Kirchhoff = {K_k4:.6f}, expected 3.0")
            ok = False
        else:
            print(f"[sanity] OK:   K₄ Kirchhoff = {K_k4:.6f} ≈ 3.0")

    # ── effective resistance on K₄: R(u,v) = 1/2 for all pairs ──
    for u, v in [(0, 1), (0, 3), (2, 3)]:
        res = effective_resistance_samples(L_k4, 4, [(u, v)])
        if res and res[0][2] is not None:
            r = res[0][2]
            if abs(r - 0.5) > 0.02:
                print(f"[sanity] FAIL: K₄ R({u},{v}) = {r:.6f}, expected 0.5")
                ok = False
            else:
                print(f"[sanity] OK:   K₄ R({u},{v}) = {r:.6f} ≈ 0.5")
        else:
            print(f"[sanity] FAIL: K₄ R({u},{v}) solve failed")
            ok = False

    return ok


# ── main ────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Graph Hodge spectrum (global spectral report)")
    ap.add_argument("--meta", default=DEFAULT_META)
    ap.add_argument("--graph", default=DEFAULT_GRAPH)
    ap.add_argument("--depth-tags", default=DEFAULT_DEPTH_TAGS)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--kirchhoff-probes", type=int, default=30)
    ap.add_argument("--sanity", action="store_true", help="Run toy-graph sanity checks and exit")
    args = ap.parse_args()

    if args.sanity:
        return 0 if sanity_check() else 1

    root = repo_root()
    t0 = time.time()

    # ── meta check
    meta_path = root / args.meta
    if meta_path.exists():
        meta = json.loads(meta_path.read_text())
        sv = meta.get("schemaVersion", 0)
        ts = meta.get("timestamp", "unknown")
        if sv < 2:
            print(f"[hodge] WARNING: schemaVersion={sv} < 2, artifacts may be stale")
        print(f"[hodge] meta: schemaVersion={sv} timestamp={ts}")
    else:
        print("[hodge] WARNING: meta.json not found")

    # ── load
    nodes, forward = load_graph(root / args.graph)
    depth_map = load_depth_tags(root / args.depth_tags)
    n_nodes = len(nodes)

    # ── build simplicial complex
    edges, edge_idx, faces = build_complex(forward)
    n_edges = len(edges)
    n_faces = len(faces)
    euler = n_nodes - n_edges + n_faces
    print(f"[hodge] complex: V={n_nodes} E={n_edges} F={n_faces} χ={euler}")

    # ── b₀ via connected components (exact, O(V+E))
    adj_row = [u for u, v in edges] + [v for u, v in edges]
    adj_col = [v for u, v in edges] + [u for u, v in edges]
    adj = sparse.csr_matrix(([1]*len(adj_row), (adj_row, adj_col)),
                            shape=(n_nodes, n_nodes))
    b0, labels = connected_components(adj, directed=False)
    print(f"[hodge] b0={b0}")

    comp_sizes = np.bincount(labels)
    largest_cc_id = int(np.argmax(comp_sizes))
    largest_cc_size = int(comp_sizes[largest_cc_id])
    cc_mask = labels == largest_cc_id
    cc_indices = np.where(cc_mask)[0]
    print(f"[hodge] largest CC: {largest_cc_size} nodes")

    # ── b₁ bounds: χ = b₀ − b₁ + b₂, so b₁ = b₀ − χ + b₂ ≥ max(0, b₀ − χ)
    b1_lower = max(0, b0 - euler)
    b1_upper = b0 - euler + n_faces
    print(f"[hodge] b1 ∈ [{b1_lower}, {b1_upper}]")

    # ── extract largest CC subgraph
    idx_map = {int(v): i for i, v in enumerate(cc_indices)}
    cc_edges = [(idx_map[u], idx_map[v]) for u, v in edges
                if u in idx_map and v in idx_map]
    L_cc = graph_laplacian_sparse(largest_cc_size, cc_edges)

    # ── Fiedler value
    print("[hodge] Fiedler ...")
    fiedler = fiedler_value(L_cc, largest_cc_size)
    print(f"[hodge] λ₂ = {fiedler}")

    # ── λ_max
    lam_max = largest_eigenvalue(L_cc, largest_cc_size)
    print(f"[hodge] λ_max = {lam_max}")

    spectral_ratio = None
    if fiedler is not None and lam_max is not None and lam_max > 0:
        spectral_ratio = fiedler / lam_max

    # ── Kirchhoff index (Moore-Penrose trace)
    print(f"[hodge] Kirchhoff ({args.kirchhoff_probes} probes) ...")
    kirchhoff, _ = kirchhoff_index_hutchinson(
        L_cc, largest_cc_size, n_probes=args.kirchhoff_probes)
    mean_eff_res = None
    if kirchhoff is not None:
        denom = largest_cc_size * (largest_cc_size - 1) / 2
        mean_eff_res = kirchhoff / denom if denom > 0 else None
        print(f"[hodge] K ≈ {kirchhoff:.2f}  mean R ≈ {mean_eff_res:.6f}")
    else:
        print("[hodge] Kirchhoff: CG failed")

    # ── effective resistance samples
    eff_res = []
    degrees = np.array(L_cc.diagonal(), dtype=int)
    if largest_cc_size > 6:
        top3 = np.argsort(degrees)[-3:]
        low3 = np.argsort(degrees)[:3]
        pairs = [(int(top3[0]), int(top3[1])),
                 (int(top3[0]), int(low3[0])),
                 (int(low3[0]), int(low3[1]))]
        print("[hodge] effective resistance samples ...")
        eff_res = effective_resistance_samples(L_cc, largest_cc_size, pairs)

    # ── directed asymmetry
    L_dir = directed_laplacian_sparse(n_nodes, edges)
    asymmetry = directed_asymmetry_score(L_dir)
    print(f"[hodge] directed asymmetry = {asymmetry:.6f}")

    # ── parity-mixing score
    vertex_signs, n_tagged = build_chiral_signs(n_nodes, depth_map, nodes)
    parity_same, total_edges = check_parity_mixing(vertex_signs, edges)
    parity_rate = parity_same / max(total_edges, 1)
    print(f"[hodge] parity-mixing: {parity_same}/{total_edges} ({parity_rate:.2%})")

    # ── degree stats
    full_L = graph_laplacian_sparse(n_nodes, edges)
    full_deg = np.array(full_L.diagonal(), dtype=int)
    deg_stats = {
        "mean": round(float(np.mean(full_deg)), 1),
        "median": float(np.median(full_deg)),
        "max": int(np.max(full_deg)),
        "p95": float(np.percentile(full_deg, 95)),
        "isolated": int(np.sum(full_deg == 0)),
    }

    elapsed = time.time() - t0
    print(f"[hodge] done in {elapsed:.1f}s")

    # ── JSON output
    result = {
        "complex": {
            "vertices": n_nodes, "edges": n_edges,
            "faces_triangles": n_faces, "euler_characteristic": euler,
        },
        "betti": {
            "b0": b0, "b1_lower": b1_lower, "b1_upper": b1_upper,
            "note": "exact b1 requires rank(∂₁)+rank(∂₂); bounds from Euler–Poincaré",
        },
        "spectrum": {
            "fiedler_value": fiedler, "lambda_max": lam_max,
            "spectral_ratio": spectral_ratio,
            "largest_component": largest_cc_size,
        },
        "pseudoinverse": {
            "scope": "largest connected component only",
            "method": "L⁺ = (L + J/n)⁻¹ − J/n, CG + Hutchinson trace",
            "kirchhoff_index": kirchhoff,
            "mean_effective_resistance": mean_eff_res,
            "probes": args.kirchhoff_probes,
        },
        "effective_resistance_samples_scope": "largest connected component only",
        "effective_resistance_samples": [
            {"u": nodes[int(cc_indices[u])], "v": nodes[int(cc_indices[v])], "R": r}
            for u, v, r in eff_res
        ],
        "directed_asymmetry": {
            "frobenius_asymmetry": asymmetry,
            "note": "‖L_dir − L_dirᵀ‖_F / ‖L_dir‖_F; purely a Frobenius norm ratio",
        },
        "parity_mixing": {
            "source": "RepDepth parity (even=+1, odd=−1, untagged→+1)",
            "tagged": n_tagged, "untagged": n_nodes - n_tagged,
            "same_parity_edges": parity_same, "total_edges": total_edges,
            "same_parity_rate": round(parity_rate, 4),
            "note": f"Only {n_tagged}/{n_nodes} nodes carry RepDepth tags; "
                    "untagged default to +1 so this metric is dominated by defaults"
                    if n_tagged < n_nodes // 2 else "",
        },
        "degree_statistics": deg_stats,
        "elapsed_seconds": round(elapsed, 1),
    }
    json_out = root / args.json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(result, indent=2))

    # ── markdown output
    md_out = root / args.md_out
    lines = [
        "# Graph Hodge Spectrum",
        "",
        "Global spectral report on the **undirected shadow** of the declaration DAG.",
        "The 2-complex uses transitive triangles (a modelling choice, not intrinsic).",
        "",
        "## Simplicial Complex",
        "",
        f"| | Count |",
        f"|---|---|",
        f"| vertices | {n_nodes} |",
        f"| edges | {n_edges} |",
        f"| triangles | {n_faces} |",
        f"| χ = V−E+F | {euler} |",
        "",
        "## Betti Numbers",
        "",
        f"- b₀ = {b0}  (connected components)",
        f"- b₁ ∈ [{b1_lower}, {b1_upper}]  (Euler bounds)",
        "",
        f"## Spectrum  (largest CC, {largest_cc_size} nodes)",
        "",
        f"- Fiedler λ₂ = `{fiedler}`",
        f"- λ_max = `{lam_max}`",
    ]
    if spectral_ratio is not None:
        lines.append(f"- λ₂/λ_max = `{spectral_ratio:.6f}`")
    lines.extend([
        "",
        f"## Pseudoinverse (largest CC only, {largest_cc_size} nodes)",
        "",
        "L⁺ = (L + J/n)⁻¹ − J/n,  solved by CG on the invertible (L + J/n).",
        "",
    ])
    if kirchhoff is not None:
        lines.append(f"- Kirchhoff index K = n·tr(Δ₀⁺) ≈ `{kirchhoff:.2f}`")
    if mean_eff_res is not None:
        lines.append(f"- mean effective resistance ≈ `{mean_eff_res:.6f}`")
    if eff_res:
        lines.extend(["", "### Effective Resistance Samples", "",
                       "| u | v | R(u,v) |", "|---|---|---|"])
        for u, v, r in eff_res:
            nu = nodes[int(cc_indices[u])]
            nv = nodes[int(cc_indices[v])]
            rs = f"{r:.6f}" if r is not None else "—"
            lines.append(f"| `{nu[:55]}` | `{nv[:55]}` | {rs} |")
    lines.extend([
        "",
        "## Directed Asymmetry",
        "",
        f"‖L_dir − L_dirᵀ‖_F / ‖L_dir‖_F = `{asymmetry:.6f}`",
        "",
        "Frobenius norm ratio measuring how far the directed Laplacian is from symmetric.",
        "",
        "## Parity-Mixing Score",
        "",
        f"- tagged nodes: {n_tagged}/{n_nodes}",
        f"- same-parity edges: {parity_same}/{total_edges} ({parity_rate:.2%})",
    ])
    if n_tagged < n_nodes // 2:
        lines.append(f"- **caveat**: only {n_tagged}/{n_nodes} nodes carry RepDepth "
                     "tags; untagged default to +1, so this metric is dominated by defaults")
    lines.extend([
        "",
        "## Degree Stats",
        "",
        f"mean={deg_stats['mean']}  median={deg_stats['median']}  "
        f"max={deg_stats['max']}  p95={deg_stats['p95']}  "
        f"isolated={deg_stats['isolated']}",
        "",
        f"*Computed in {elapsed:.1f}s.*",
    ])
    md_out.write_text("\n".join(lines) + "\n")
    print(f"[hodge] wrote {json_out}")
    print(f"[hodge] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
