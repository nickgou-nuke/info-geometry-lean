#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_REPO_ROOT = Path(__file__).resolve().parents[2]
_MPLCONFIGDIR = _REPO_ROOT / ".artifacts" / "matplotlib"
_MPLCONFIGDIR.mkdir(parents=True, exist_ok=True)
os.environ.setdefault("MPLCONFIGDIR", str(_MPLCONFIGDIR))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

if __package__ in (None, ""):
    sys.path.insert(0, str(_REPO_ROOT))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root

DEFAULT_GRAPH = "artifacts/dag/full_graph.json"
DEFAULT_DECLS = "artifacts/dag/index/decls.jsonl"
DEFAULT_TOPOLOGY = "artifacts/dag/structural-topology.json"
DEFAULT_FLOW_EDGES = "artifacts/dag/process-flow/flow-edges.jsonl"
DEFAULT_FRAMES_DIR = "reports/dag/theory-cloud/frames"
DEFAULT_MANIFEST = "reports/dag/theory-cloud/manifest.json"
DEFAULT_VIDEO = "reports/dag/theory-cloud/theory-cloud.mp4"

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


@dataclass
class NodeInfo:
    name: str
    kind: str
    module: str
    depth: float
    comp_size: int
    is_root: bool
    is_capstone: bool
    chiral: float
    obstruction: float
    degree: int


@dataclass
class Snapshot:
    label: str
    nodes: dict[str, NodeInfo]
    edges: list[tuple[str, str, float]]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Render the repo DAG as a moving theory-cloud (particle system) using "
            "structural and semantic flow fields."
        )
    )
    parser.add_argument(
        "--mode",
        choices=["structural", "semantic", "commits"],
        default="semantic",
        help="Rendering mode.",
    )
    parser.add_argument("--graph", default=DEFAULT_GRAPH, help="Path to full_graph.json.")
    parser.add_argument("--decls", default=DEFAULT_DECLS, help="Path to decls.jsonl.")
    parser.add_argument("--topology", default=DEFAULT_TOPOLOGY, help="Path to structural-topology.json.")
    parser.add_argument("--flow-edges", default=DEFAULT_FLOW_EDGES, help="Path to process flow edges JSONL.")
    parser.add_argument("--max-nodes", type=int, default=2200, help="Render at most this many nodes.")
    parser.add_argument("--max-edges", type=int, default=12000, help="Render at most this many edges.")
    parser.add_argument("--steps", type=int, default=60, help="Relaxation steps per snapshot.")
    parser.add_argument("--dt", type=float, default=0.08, help="Integrator step.")
    parser.add_argument("--seed", type=int, default=7, help="Random seed.")
    parser.add_argument("--width", type=int, default=1920, help="Frame width.")
    parser.add_argument("--height", type=int, default=1080, help="Frame height.")
    parser.add_argument("--dpi", type=int, default=120, help="Matplotlib DPI.")
    parser.add_argument("--frames-dir", default=DEFAULT_FRAMES_DIR, help="Output frame directory.")
    parser.add_argument("--manifest", default=DEFAULT_MANIFEST, help="Snapshot/frame manifest output.")
    parser.add_argument("--fps", type=int, default=24, help="FPS for optional video export.")
    parser.add_argument("--video-out", default="", help="Optional mp4 output path.")
    parser.add_argument(
        "--ffmpeg-bin",
        default="ffmpeg",
        help="ffmpeg binary for optional video export.",
    )

    parser.add_argument(
        "--commits",
        default="",
        help="Comma-separated commit list for mode=commits.",
    )
    parser.add_argument(
        "--commit-range",
        default="",
        help="Git rev-list range for mode=commits (example: HEAD~8..HEAD).",
    )
    parser.add_argument(
        "--interpolate",
        type=int,
        default=2,
        help="Inter-frame interpolation count between commit keyframes.",
    )
    parser.add_argument(
        "--strict-commit-artifacts",
        action="store_true",
        help=(
            "Fail when a selected commit does not contain required DAG artifacts "
            "(default behavior is to skip such commits with a warning)."
        ),
    )
    return parser.parse_args()


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


# [lossless-compact] read_jsonl folded into igf.common.json_io.read_jsonl
from igf.common.json_io import read_jsonl


def git_show_text(commit: str, rel_path: str) -> str | None:
    try:
        out = subprocess.check_output(
            ["git", "show", f"{commit}:{rel_path}"],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError:
        return None
    return out


def read_json_from_commit(commit: str, rel_path: str) -> dict[str, Any] | None:
    txt = git_show_text(commit, rel_path)
    if txt is None:
        return None
    return json.loads(txt)


def read_jsonl_from_commit(commit: str, rel_path: str) -> list[dict[str, Any]]:
    txt = git_show_text(commit, rel_path)
    if txt is None:
        return []
    out: list[dict[str, Any]] = []
    for line in txt.splitlines():
        s = line.strip()
        if not s:
            continue
        obj = json.loads(s)
        if isinstance(obj, dict):
            out.append(obj)
    return out


def chirality_sign_from_polarity(polarity: str) -> int:
    if polarity in {"descending", "sameLayer"}:
        return 1
    if polarity in {"remote", "regressive", "mixed"}:
        return -1
    return 0


def compute_transport_credit(edge: dict[str, Any]) -> int:
    edge_use = str(edge.get("edgeUse", ""))
    base = 4 if edge_use in {"valueOnly", "both"} else 1 if edge_use in {"typeOnly", "both"} else 0
    role = str(edge.get("inferredRole", "unknown"))
    boundary = str(edge.get("inferredBoundary", "unclear"))
    return base + ROLE_CREDIT.get(role, 0) + BOUNDARY_CREDIT.get(boundary, 0)


def compute_defect_debt(edge: dict[str, Any]) -> int:
    tags = edge.get("defectTags", [])
    if not isinstance(tags, list):
        return 0
    return sum(DEFECT_SEVERITY.get(str(tag), 1) for tag in tags)


def build_decl_meta(decls_rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in decls_rows:
        name = str(row.get("name", ""))
        if name:
            out[name] = row
    return out


def build_topology_meta(topology: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], dict[int, dict[str, Any]]]:
    comp_rows = topology.get("components", [])
    comp_by_index: dict[int, dict[str, Any]] = {}
    if isinstance(comp_rows, list):
        for row in comp_rows:
            if isinstance(row, dict):
                idx = row.get("componentIndex")
                if isinstance(idx, int):
                    comp_by_index[idx] = row

    by_decl: dict[str, dict[str, Any]] = {}
    members = topology.get("membership", [])
    if isinstance(members, list):
        for row in members:
            if not isinstance(row, dict):
                continue
            name = str(row.get("declName", ""))
            idx = row.get("componentIndex")
            comp = comp_by_index.get(idx) if isinstance(idx, int) else None
            if name and comp is not None:
                by_decl[name] = comp
    return by_decl, comp_by_index


def build_rep_depth_map(topology: dict[str, Any], graph_obj: dict[str, Any]) -> dict[str, float]:
    by_decl, _ = build_topology_meta(topology)
    depth_map: dict[str, float] = {}
    nodes = graph_obj.get("nodes", [])
    if not isinstance(nodes, list):
        return depth_map
    for n in nodes:
        if not isinstance(n, str):
            continue
        comp = by_decl.get(n)
        if comp is None:
            continue
        depth = comp.get("depthMin", 0)
        try:
            depth_map[n] = float(depth)
        except Exception:
            depth_map[n] = 0.0
    return depth_map


def build_semantic_fields(flow_edges: list[dict[str, Any]]) -> tuple[dict[str, float], dict[str, float]]:
    chiral: dict[str, float] = defaultdict(float)
    obstruction: dict[str, float] = defaultdict(float)
    for edge in flow_edges:
        src = str(edge.get("src", ""))
        dst = str(edge.get("dst", ""))
        if not src or not dst:
            continue
        sign = chirality_sign_from_polarity(str(edge.get("inferredPolarity", "")))
        credit = compute_transport_credit(edge)
        debt = compute_defect_debt(edge)
        flux = sign * float(max(1, credit)) / (1.0 + float(debt))
        chiral[src] += flux
        chiral[dst] -= flux

        obs = float(debt) + (0.25 if sign < 0 else 0.0)
        obstruction[src] += obs
        obstruction[dst] += obs
    return dict(chiral), dict(obstruction)


def parse_edges(graph_obj: dict[str, Any], names: list[str]) -> tuple[list[tuple[str, str, float]], dict[str, int], dict[str, int]]:
    forward = graph_obj.get("forward", [])
    edges: list[tuple[str, str, float]] = []
    indeg: dict[str, int] = defaultdict(int)
    outdeg: dict[str, int] = defaultdict(int)
    if not isinstance(forward, list):
        return edges, dict(indeg), dict(outdeg)

    for i, row in enumerate(forward):
        if i >= len(names):
            break
        src = names[i]
        if not isinstance(row, list):
            continue
        for e in row:
            if not isinstance(e, list) or not e:
                continue
            try:
                j = int(e[0])
            except Exception:
                continue
            if j < 0 or j >= len(names):
                continue
            dst = names[j]
            et = str(e[1]) if len(e) > 1 else "value"
            w = 1.0 if et == "value" else 0.55 if et == "type" else 0.8
            edges.append((src, dst, w))
            outdeg[src] += 1
            indeg[dst] += 1
    return edges, dict(indeg), dict(outdeg)


def make_snapshot(
    label: str,
    graph_obj: dict[str, Any],
    decl_rows: list[dict[str, Any]],
    topology_obj: dict[str, Any],
    flow_edges: list[dict[str, Any]],
    *,
    max_nodes: int,
    mode: str,
) -> Snapshot:
    raw_nodes = graph_obj.get("nodes", [])
    if not isinstance(raw_nodes, list):
        raise SystemExit("full_graph.json missing 'nodes' list")
    names = [n for n in raw_nodes if isinstance(n, str)]

    decl_meta = build_decl_meta(decl_rows)
    by_decl, _ = build_topology_meta(topology_obj)
    depth_map = build_rep_depth_map(topology_obj, graph_obj)
    chiral, obstruction = build_semantic_fields(flow_edges)
    edges, indeg, outdeg = parse_edges(graph_obj, names)

    # Importance score for bounded rendering.
    ranked: list[tuple[float, str]] = []
    for n in names:
        deg = indeg.get(n, 0) + outdeg.get(n, 0)
        obs = obstruction.get(n, 0.0)
        chi = abs(chiral.get(n, 0.0))
        comp = by_decl.get(n, {})
        comp_size = int(comp.get("size", 1)) if isinstance(comp, dict) else 1
        root_bonus = 12.0 if isinstance(comp, dict) and bool(comp.get("isRoot", False)) else 0.0
        cap_bonus = 16.0 if isinstance(comp, dict) and bool(comp.get("isCapstone", False)) else 0.0
        score = 0.7 * deg + 1.6 * math.log1p(obs) + 1.2 * math.log1p(chi) + 0.3 * math.log1p(comp_size)
        score += root_bonus + cap_bonus
        ranked.append((score, n))

    ranked.sort(reverse=True)
    selected = {n for _, n in ranked[: max(100, min(max_nodes, len(ranked)))]}

    # Keep all nodes that appear in highest-obstruction flow edges.
    if mode != "structural" and flow_edges:
        flow_rank = sorted(
            flow_edges,
            key=lambda e: compute_defect_debt(e) + abs(chirality_sign_from_polarity(str(e.get("inferredPolarity", ""))))
            * compute_transport_credit(e),
            reverse=True,
        )
        for edge in flow_rank[: min(2000, len(flow_rank))]:
            src = str(edge.get("src", ""))
            dst = str(edge.get("dst", ""))
            if src:
                selected.add(src)
            if dst:
                selected.add(dst)
            if len(selected) >= max_nodes:
                break

    nodes: dict[str, NodeInfo] = {}
    for n in names:
        if n not in selected:
            continue
        meta = decl_meta.get(n, {})
        comp = by_decl.get(n, {})
        kind = str(meta.get("kind", "unknown"))
        module = str(meta.get("module", ""))
        depth = float(depth_map.get(n, 0.0))
        comp_size = int(comp.get("size", 1)) if isinstance(comp, dict) else 1
        is_root = bool(comp.get("isRoot", False)) if isinstance(comp, dict) else False
        is_capstone = bool(comp.get("isCapstone", False)) if isinstance(comp, dict) else False
        degree = indeg.get(n, 0) + outdeg.get(n, 0)
        nodes[n] = NodeInfo(
            name=n,
            kind=kind,
            module=module,
            depth=depth,
            comp_size=comp_size,
            is_root=is_root,
            is_capstone=is_capstone,
            chiral=float(chiral.get(n, 0.0)),
            obstruction=float(obstruction.get(n, 0.0)),
            degree=int(degree),
        )

    filtered_edges = [(s, d, w) for (s, d, w) in edges if s in nodes and d in nodes]
    return Snapshot(label=label, nodes=nodes, edges=filtered_edges)


def seeded_rand01(name: str, seed: int) -> float:
    h = hash((name, seed)) & 0xFFFFFFFF
    return (h / 0xFFFFFFFF) if h else 0.5


def initialize_positions(snapshot: Snapshot, seed: int, prev: dict[str, tuple[float, float]] | None = None) -> dict[str, tuple[float, float]]:
    out: dict[str, tuple[float, float]] = {}

    # Module centers from previous positions.
    module_centers: dict[str, tuple[float, float, int]] = {}
    if prev is not None:
        for name, pos in prev.items():
            info = snapshot.nodes.get(name)
            if info is None:
                continue
            x, y = pos
            mx, my, c = module_centers.get(info.module, (0.0, 0.0, 0))
            module_centers[info.module] = (mx + x, my + y, c + 1)

    max_depth = max((n.depth for n in snapshot.nodes.values()), default=1.0)
    max_depth = max(1.0, max_depth)

    for name, info in snapshot.nodes.items():
        if prev is not None and name in prev:
            out[name] = prev[name]
            continue
        if info.module in module_centers and module_centers[info.module][2] > 0:
            sx, sy, c = module_centers[info.module]
            cx, cy = sx / c, sy / c
            jitter = 0.02
            rx = (seeded_rand01(name + ":x", seed) - 0.5) * jitter
            ry = (seeded_rand01(name + ":y", seed) - 0.5) * jitter
            out[name] = (cx + rx, cy + ry)
            continue

        x = -1.1 + 2.2 * (info.depth / max_depth)
        y = (seeded_rand01(name + ":init", seed) - 0.5) * 1.8
        out[name] = (x, y)
    return out


def run_relaxation(
    snapshot: Snapshot,
    pos: dict[str, tuple[float, float]],
    *,
    mode: str,
    steps: int,
    dt: float,
    seed: int,
) -> dict[str, tuple[float, float]]:
    names = list(snapshot.nodes.keys())
    idx = {n: i for i, n in enumerate(names)}
    n = len(names)
    if n == 0:
        return pos

    x = [pos[nm][0] for nm in names]
    y = [pos[nm][1] for nm in names]
    vx = [0.0] * n
    vy = [0.0] * n

    edges = [(idx[s], idx[d], w) for (s, d, w) in snapshot.edges if s in idx and d in idx]

    # Depth anchors.
    max_depth = max((snapshot.nodes[nm].depth for nm in names), default=1.0)
    max_depth = max(1.0, max_depth)
    target_x = [-1.05 + 2.1 * (snapshot.nodes[nm].depth / max_depth) for nm in names]

    # Semantic normalized fields.
    max_abs_chiral = max((abs(snapshot.nodes[nm].chiral) for nm in names), default=1.0)
    max_obs = max((snapshot.nodes[nm].obstruction for nm in names), default=1.0)
    max_abs_chiral = max(1e-6, max_abs_chiral)
    max_obs = max(1e-6, max_obs)

    rand = random.Random(seed)
    for _ in range(max(1, steps)):
        fx = [0.0] * n
        fy = [0.0] * n

        # Edge springs (linear in edge count).
        for u, v, w in edges:
            dx = x[v] - x[u]
            dy = y[v] - y[u]
            dist = math.hypot(dx, dy) + 1e-9
            rest = 0.03
            k = 0.35 * w
            f = k * (dist - rest)
            ux = dx / dist
            uy = dy / dist
            fx[u] += f * ux
            fy[u] += f * uy
            fx[v] -= f * ux
            fy[v] -= f * uy

        # Local repulsion via spatial hashing (near-linear expected).
        cell_size = 0.08
        bins: dict[tuple[int, int], list[int]] = defaultdict(list)
        for i in range(n):
            cx = int(math.floor(x[i] / cell_size))
            cy = int(math.floor(y[i] / cell_size))
            bins[(cx, cy)].append(i)

        neigh = [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]
        for (cx, cy), members in bins.items():
            near: list[int] = []
            for dx, dy in neigh:
                near.extend(bins.get((cx + dx, cy + dy), []))
            for i in members:
                for j in near:
                    if j <= i:
                        continue
                    dx = x[i] - x[j]
                    dy = y[i] - y[j]
                    d2 = dx * dx + dy * dy + 1e-9
                    if d2 > 0.05 * 0.05:
                        continue
                    inv = 0.0007 / d2
                    fx[i] += dx * inv
                    fy[i] += dy * inv
                    fx[j] -= dx * inv
                    fy[j] -= dy * inv

        # Structural anchors and semantic field.
        for i, nm in enumerate(names):
            info = snapshot.nodes[nm]
            # depth anchor keeps layer ordering stable
            fx[i] += 0.12 * (target_x[i] - x[i])

            # mild vertical regularization
            fy[i] += -0.03 * y[i]

            if mode != "structural":
                chi = info.chiral / max_abs_chiral
                obs = info.obstruction / max_obs
                fy[i] += 0.08 * math.tanh(chi)
                fx[i] += 0.03 * (obs - 0.5)

            if info.is_root:
                fx[i] += -0.02
            if info.is_capstone:
                fx[i] += 0.02

            # tiny noise to escape local ties
            fx[i] += (rand.random() - 0.5) * 0.0008
            fy[i] += (rand.random() - 0.5) * 0.0008

        # Integrate with damping.
        for i in range(n):
            vx[i] = 0.82 * vx[i] + dt * fx[i]
            vy[i] = 0.82 * vy[i] + dt * fy[i]
            x[i] += vx[i]
            y[i] += vy[i]

    return {names[i]: (x[i], y[i]) for i in range(n)}


def kind_marker(kind: str) -> str:
    if kind == "theorem":
        return "o"
    if kind == "lemma":
        return "s"
    if kind == "def":
        return "^"
    if kind == "axiom":
        return "X"
    return "."


def render_frame(
    snapshot: Snapshot,
    pos: dict[str, tuple[float, float]],
    frame_path: Path,
    *,
    width: int,
    height: int,
    dpi: int,
    max_edges: int,
    mode: str,
    title_suffix: str,
) -> dict[str, Any]:
    fig_w = max(8.0, width / dpi)
    fig_h = max(5.0, height / dpi)
    fig, ax = plt.subplots(figsize=(fig_w, fig_h), dpi=dpi)
    ax.set_facecolor("#05070a")
    fig.patch.set_facecolor("#05070a")

    # Draw a sampled edge field as faint filaments.
    edge_rows = snapshot.edges
    if len(edge_rows) > max_edges:
        edge_rows = edge_rows[:max_edges]

    for s, d, w in edge_rows:
        ps = pos.get(s)
        pd = pos.get(d)
        if ps is None or pd is None:
            continue
        xs = [ps[0], pd[0]]
        ys = [ps[1], pd[1]]
        alpha = 0.02 + 0.015 * w
        ax.plot(xs, ys, color="#8aa0b5", alpha=min(0.12, alpha), linewidth=0.25)

    # Scatter by kind marker.
    all_nodes = list(snapshot.nodes.keys())
    if all_nodes:
        max_abs_chiral = max(abs(snapshot.nodes[n].chiral) for n in all_nodes)
        max_abs_chiral = max(1e-9, max_abs_chiral)
        max_obs = max(snapshot.nodes[n].obstruction for n in all_nodes)
        max_obs = max(1e-9, max_obs)

        by_marker: dict[str, list[str]] = defaultdict(list)
        for n in all_nodes:
            by_marker[kind_marker(snapshot.nodes[n].kind)].append(n)

        cmap = plt.get_cmap("coolwarm")
        for marker, names in by_marker.items():
            xs = [pos[n][0] for n in names]
            ys = [pos[n][1] for n in names]
            colors = []
            sizes = []
            for n in names:
                info = snapshot.nodes[n]
                chi = info.chiral / max_abs_chiral
                t = 0.5 + 0.5 * max(-1.0, min(1.0, chi))
                colors.append(cmap(t))
                base = 7.0 + 1.5 * math.sqrt(max(1.0, info.degree))
                obs = info.obstruction / max_obs
                sizes.append(base + 14.0 * math.sqrt(max(0.0, obs)))
            ax.scatter(xs, ys, s=sizes, c=colors, marker=marker, edgecolors="none", alpha=0.9)

    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)

    ax.set_title(
        f"Theory Cloud ({mode}) - {snapshot.label}{title_suffix}",
        color="#e8eef6",
        fontsize=11,
        pad=10,
    )

    frame_path.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(frame_path, facecolor=fig.get_facecolor())
    plt.close(fig)

    return {
        "label": snapshot.label,
        "nodes": len(snapshot.nodes),
        "edges": len(snapshot.edges),
        "frame": str(frame_path),
    }


def resolve_commits(args: argparse.Namespace) -> list[str]:
    commits: list[str] = []
    if args.commits.strip():
        commits = [c.strip() for c in args.commits.split(",") if c.strip()]
    elif args.commit_range.strip():
        out = subprocess.check_output(["git", "rev-list", "--reverse", args.commit_range.strip()], text=True)
        commits = [line.strip() for line in out.splitlines() if line.strip()]
    if not commits:
        raise SystemExit("mode=commits requires --commits or --commit-range")
    return commits


def snapshot_from_worktree(args: argparse.Namespace, mode: str) -> Snapshot:
    root = repo_root()
    graph = read_json(normalize_user_path(args.graph, root))
    decls = read_jsonl(normalize_user_path(args.decls, root))
    topology = read_json(normalize_user_path(args.topology, root))
    flow_rows = read_jsonl(normalize_user_path(args.flow_edges, root)) if mode != "structural" else []
    return make_snapshot(
        label="worktree",
        graph_obj=graph,
        decl_rows=decls,
        topology_obj=topology,
        flow_edges=flow_rows,
        max_nodes=args.max_nodes,
        mode=mode,
    )


def snapshot_from_commit(commit: str, args: argparse.Namespace) -> Snapshot | None:
    token = commit.strip()
    if token.upper() in {"WORKTREE", "CURRENT"}:
        snap = snapshot_from_worktree(args, "semantic")
        snap.label = token.upper()
        return snap

    graph = read_json_from_commit(commit, args.graph)
    topology = read_json_from_commit(commit, args.topology)
    if graph is None or topology is None:
        if token == "HEAD" and not args.strict_commit_artifacts:
            print(
                "[theory-cloud] WARN: HEAD artifacts missing in git object; using worktree snapshot",
                file=sys.stderr,
                flush=True,
            )
            snap = snapshot_from_worktree(args, "semantic")
            snap.label = "HEAD*"
            return snap
        if args.strict_commit_artifacts:
            raise SystemExit(f"missing required DAG artifacts in commit {commit[:12]}")
        print(
            f"[theory-cloud] WARN: skipping commit {commit[:12]} (missing required artifacts)",
            file=sys.stderr,
            flush=True,
        )
        return None
    decls = read_jsonl_from_commit(commit, args.decls)
    flow_rows = read_jsonl_from_commit(commit, args.flow_edges)
    return make_snapshot(
        label=commit[:12],
        graph_obj=graph,
        decl_rows=decls,
        topology_obj=topology,
        flow_edges=flow_rows,
        max_nodes=args.max_nodes,
        mode="semantic",
    )


def maybe_render_video(args: argparse.Namespace, frames_dir: Path) -> str | None:
    video_out = args.video_out.strip()
    if not video_out:
        return None
    out_path = normalize_user_path(video_out, repo_root())
    out_path.parent.mkdir(parents=True, exist_ok=True)
    pattern = str((frames_dir / "frame_%06d.png").resolve())
    cmd = [
        args.ffmpeg_bin,
        "-y",
        "-framerate",
        str(args.fps),
        "-i",
        pattern,
        "-c:v",
        "libx264",
        "-pix_fmt",
        "yuv420p",
        str(out_path.resolve()),
    ]
    try:
        subprocess.run(cmd, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError) as exc:
        print(f"[theory-cloud] WARN: video export skipped ({exc})", file=sys.stderr)
        return None
    return str(out_path)


def run_single_mode(args: argparse.Namespace, mode: str) -> dict[str, Any]:
    snapshot = snapshot_from_worktree(args, mode)
    frames_dir = normalize_user_path(args.frames_dir, repo_root())
    frames_dir.mkdir(parents=True, exist_ok=True)

    pos = initialize_positions(snapshot, args.seed, prev=None)
    frames: list[dict[str, Any]] = []

    # Initial frame.
    frame0 = frames_dir / "frame_000000.png"
    frames.append(
        render_frame(
            snapshot,
            pos,
            frame0,
            width=args.width,
            height=args.height,
            dpi=args.dpi,
            max_edges=args.max_edges,
            mode=mode,
            title_suffix=" | init",
        )
    )

    # Relaxation movie.
    frame_idx = 1
    chunks = max(1, args.steps // 10)
    for _ in range(chunks):
        pos = run_relaxation(snapshot, pos, mode=mode, steps=10, dt=args.dt, seed=args.seed)
        out = frames_dir / f"frame_{frame_idx:06d}.png"
        frames.append(
            render_frame(
                snapshot,
                pos,
                out,
                width=args.width,
                height=args.height,
                dpi=args.dpi,
                max_edges=args.max_edges,
                mode=mode,
                title_suffix=" | relax",
            )
        )
        frame_idx += 1

    video_path = maybe_render_video(args, frames_dir)
    return {
        "mode": mode,
        "frames": frames,
        "video": video_path,
    }


def lerp(a: float, b: float, t: float) -> float:
    return a + (b - a) * t


def interpolate_positions(
    prev_pos: dict[str, tuple[float, float]],
    next_pos: dict[str, tuple[float, float]],
    nodes: dict[str, NodeInfo],
    t: float,
) -> dict[str, tuple[float, float]]:
    out: dict[str, tuple[float, float]] = {}
    for n in nodes:
        p0 = prev_pos.get(n)
        p1 = next_pos.get(n)
        if p0 is None and p1 is None:
            continue
        if p0 is None:
            out[n] = p1  # type: ignore[assignment]
            continue
        if p1 is None:
            out[n] = p0
            continue
        out[n] = (lerp(p0[0], p1[0], t), lerp(p0[1], p1[1], t))
    return out


def run_commit_mode(args: argparse.Namespace) -> dict[str, Any]:
    commits = resolve_commits(args)
    frames_dir = normalize_user_path(args.frames_dir, repo_root())
    frames_dir.mkdir(parents=True, exist_ok=True)

    snapshots: list[Snapshot] = []
    kept_commits: list[str] = []
    for c in commits:
        snap = snapshot_from_commit(c, args)
        if snap is None:
            continue
        snapshots.append(snap)
        kept_commits.append(c)

    if not snapshots:
        raise SystemExit("no commit snapshots available after artifact filtering")

    frames: list[dict[str, Any]] = []
    frame_idx = 0
    prev_pos: dict[str, tuple[float, float]] | None = None
    prev_snap: Snapshot | None = None

    for snap in snapshots:
        pos0 = initialize_positions(snap, args.seed, prev=prev_pos)
        pos1 = run_relaxation(snap, pos0, mode="semantic", steps=max(20, args.steps // 2), dt=args.dt, seed=args.seed)

        if prev_snap is not None and prev_pos is not None:
            interp_steps = max(0, args.interpolate)
            for k in range(interp_steps):
                t = float(k + 1) / float(interp_steps + 1)
                mix = interpolate_positions(prev_pos, pos1, snap.nodes, t)
                out = frames_dir / f"frame_{frame_idx:06d}.png"
                frames.append(
                    render_frame(
                        snap,
                        mix,
                        out,
                        width=args.width,
                        height=args.height,
                        dpi=args.dpi,
                        max_edges=args.max_edges,
                        mode="commits",
                        title_suffix=f" | transition {t:.2f}",
                    )
                )
                frame_idx += 1

        out = frames_dir / f"frame_{frame_idx:06d}.png"
        frames.append(
            render_frame(
                snap,
                pos1,
                out,
                width=args.width,
                height=args.height,
                dpi=args.dpi,
                max_edges=args.max_edges,
                mode="commits",
                title_suffix=" | keyframe",
            )
        )
        frame_idx += 1

        prev_pos = pos1
        prev_snap = snap

    video_path = maybe_render_video(args, frames_dir)
    return {
        "mode": "commits",
        "commits": kept_commits,
        "frames": frames,
        "video": video_path,
    }


def main() -> int:
    args = parse_args()

    if args.mode in {"structural", "semantic"}:
        result = run_single_mode(args, args.mode)
    else:
        result = run_commit_mode(args)

    manifest_path = normalize_user_path(args.manifest, repo_root())
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(result, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")

    print(
        f"[theory-cloud] mode={result.get('mode')} frames={len(result.get('frames', []))} "
        f"manifest={manifest_path}",
        flush=True,
    )
    if result.get("video"):
        print(f"[theory-cloud] video={result['video']}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
