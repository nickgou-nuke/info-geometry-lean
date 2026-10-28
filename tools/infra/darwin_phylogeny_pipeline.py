#!/usr/bin/env python3
"""Orchestrate the repository evolution and fingerprint visualization tools.

The default workflow is local and read-only with respect to ArangoDB. Database
ingestion and the legacy DNA bridge are opt-in because they write or query
separate collections. All paths are explicit so generated data is reproducible.
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INFRA = ROOT / "tools" / "infra"


def run(args: list[str]) -> None:
    print("$", " ".join(args), flush=True)
    subprocess.run(args, cwd=ROOT, check=True)


def prepare(out: Path) -> tuple[Path, Path, Path, Path]:
    out.mkdir(parents=True, exist_ok=True)
    commits, paths, numstat, labels = (out / name for name in
                                      ("commits.jsonl", "paths.jsonl", "numstat.jsonl", "labels.jsonl"))
    run([sys.executable, str(INFRA / "evolution_extract.py"), str(commits),
         "--paths-output", str(paths), "--numstat-output", str(numstat)])
    run([sys.executable, str(INFRA / "evolution_taxonomy.py"), str(commits),
         "--paths", str(paths), "--out", str(labels)])
    run([sys.executable, str(INFRA / "evolution_path_habitat.py"), str(paths),
         "--out", str(out / "habitats.json")])
    return commits, paths, numstat, labels


def render(out: Path, since: str, limit: int, edges: Path | None,
           labels: Path | None = None) -> None:
    command = [sys.executable, str(INFRA / "darwin_phylogeny_dashboard.py"),
               "--since", since, "--limit", str(limit), "--out", str(out / "index.html")]
    if edges is not None:
        command.extend(["--edges", str(edges)])
    if labels is not None:
        command.extend(["--labels", str(labels)])
    run(command)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("all", "prepare", "render", "run", "ingest", "bridge", "tree"))
    parser.add_argument("--out-dir", type=Path, default=Path("artifacts/darwin"))
    parser.add_argument("--since", default="1 year ago")
    parser.add_argument("--limit", type=int, default=5000)
    parser.add_argument("--edges", type=Path, help="optional existing commit/declaration JSONL")
    parser.add_argument("--labels", type=Path, help="optional taxonomy JSONL for render")
    parser.add_argument("--database", help="Arango target for the evo_* ingest stage")
    parser.add_argument("--include-paths", action="store_true",
                        help="include file/path streams in evo_* Arango ingestion")
    parser.add_argument("--sync-arango", action="store_true",
                        help="with run, also upsert extracted records into evo_* collections")
    parser.add_argument("--persist-bridge", action="store_true",
                        help="explicitly upsert habitat-cohabitation rows into commit_decl_edges")
    parser.add_argument("--build-bridge", action="store_true",
                        help="with all, export declaration annotations through the Arango bridge")
    parser.add_argument("--tree", action="store_true",
                        help="with all, also export the Arango commit/DNA tree")
    parser.add_argument("--commit-database", default="darwin_commits")
    parser.add_argument(
        "--commit-collection",
        help="Arango collection for tree export (defaults to evo_commits with --sync-arango, else commit_nodes)",
    )
    parser.add_argument("--commit-endpoint")
    parser.add_argument("--dna-endpoint")
    parser.add_argument("--dna-database")
    parser.add_argument("--dna-collection")
    parser.add_argument("--join-mode", choices=("direct", "declaration"))
    parser.add_argument("--fingerprint-join-field")
    parser.add_argument("--commit-edge-collection", default="commit_decl_edges")
    parser.add_argument("--fingerprint-fields",
                        help="comma-separated allow-listed fields for the tree export")
    args = parser.parse_args()
    out = args.out_dir.resolve()
    if args.limit < 1:
        parser.error("--limit must be positive")
    if args.command in ("all", "prepare", "run"):
        commits, paths, numstat, labels = prepare(out)
        annotations = args.edges
        if args.command in ("all", "run") and args.sync_arango:
            ingest(out, args)
        bridge_file = None
        if args.command == "all" and args.build_bridge:
            bridge_file = build_bridge(out, args.persist_bridge)
            annotations = bridge_file
        if args.command in ("all", "prepare", "run"):
            render(out, args.since, args.limit, annotations,
                   args.labels or (out / "labels.jsonl"))
        if args.command == "all" and args.tree:
            export_tree(out, args, declaration_edges=bridge_file or args.edges)
        print(f"Prepared evolution artifacts in {out}")
        return 0
    if args.command == "render":
        render(out, args.since, args.limit, args.edges, args.labels)
        return 0
    if args.command == "ingest":
        ingest(out, args)
        return 0
    if args.command == "bridge":
        bridge_file = build_bridge(out, args.persist_bridge)
        labels_file = args.labels or (out / "labels.jsonl")
        render(out, args.since, args.limit, bridge_file,
               labels_file if labels_file.is_file() else None)
        return 0
    if args.command == "tree":
        export_tree(out, args, parser)
    return 0


def ingest(out: Path, args: argparse.Namespace) -> None:
    commits, labels = out / "commits.jsonl", out / "labels.jsonl"
    paths, numstat = out / "paths.jsonl", out / "numstat.jsonl"
    required = [commits, labels] + ([paths, numstat] if args.include_paths else [])
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        raise SystemExit("run prepare first; missing: " + ", ".join(missing))
    command = [sys.executable, str(INFRA / "evolution_ingest.py"), str(commits), "--labels", str(labels)]
    if args.include_paths:
        command += ["--paths", str(paths), "--numstat", str(numstat)]
    if args.database:
        command += ["--database", args.database]
    run(command)


def build_bridge(out: Path, persist: bool) -> Path:
    bridge_file = out / "commit_decl_edges.jsonl"
    command = [sys.executable, str(INFRA / "darwin_dna_bridge.py"), "--build-edges",
               "--output-jsonl", str(bridge_file), "--no-persist"]
    if persist:
        command.remove("--no-persist")
        command.append("--persist")
    run(command)
    return bridge_file


def export_tree(out: Path, args: argparse.Namespace,
                parser: argparse.ArgumentParser | None = None,
                declaration_edges: Path | None = None) -> None:
    required = ("dna_collection", "join_mode", "fingerprint_join_field")
    missing = [name.replace("_", "-") for name in required if not getattr(args, name)]
    if missing:
        message = "tree export requires --" + ", --".join(missing)
        if parser:
            parser.error(message)
        raise SystemExit(message)
    command = [sys.executable, str(INFRA / "darwin_tree_visualizer.py"),
               "--commit-database", args.commit_database,
               "--commit-collection", args.commit_collection or
               ("evo_commits" if args.sync_arango else "commit_nodes"),
               "--dna-collection", args.dna_collection,
               "--join-mode", args.join_mode,
               "--fingerprint-join-field", args.fingerprint_join_field,
               "--since", args.since,
               "--json-out", str(out / "darwin-tree.json"),
               "--html-out", str(out / "darwin-tree.html")]
    for flag, value in (("--commit-endpoint", args.commit_endpoint),
                        ("--dna-endpoint", args.dna_endpoint),
                        ("--dna-database", args.dna_database),
                        ("--commit-edge-collection", args.commit_edge_collection),
                        ("--fingerprint-fields", args.fingerprint_fields)):
        if value:
            command += [flag, value]
    if declaration_edges is not None and args.join_mode == "declaration":
        command += ["--declaration-edges-jsonl", str(declaration_edges.resolve())]
    run(command)


if __name__ == "__main__":
    raise SystemExit(main())
