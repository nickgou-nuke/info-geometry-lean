#!/usr/bin/env python3
"""
Info-Geometry Spire Orchestrator (IG-CLI)
Central entrypoint for the Level 3 Greenfield Architecture.
"""

import argparse
import json
import os
import subprocess
import sys
import time
import uuid
from pathlib import Path

# --- Configuration ---
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

DEFAULT_RUN_ID_VAR = "IG_RUN_ID"

def generate_run_id() -> str:
    """Generate a canonical run identity."""
    timestamp = time.strftime("%Y%m%dT%H%M%S", time.gmtime())
    git_sha = "unknown"
    try:
        git_sha = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], text=True).strip()
    except Exception:
        pass
    unique = str(uuid.uuid4())[:8]
    return f"run_{timestamp}_{git_sha}_{unique}"

def run_command(cmd: list[str], env: dict[str, str], description: str) -> int:
    """Execute a sub-command with the provided environment."""
    print(f"[ig] {description}...", flush=True)
    print(f"     cmd: {' '.join(cmd)}", flush=True)
    try:
        result = subprocess.run(cmd, cwd=ROOT, env=env)
        return result.returncode
    except KeyboardInterrupt:
        print("\n[ig] interrupted by user")
        return 130
    except Exception as exc:
        print(f"[ig] error: {exc}")
        return 1

def cmd_process(args: argparse.Namespace, env: dict[str, str]) -> int:
    """Process graph patches and signatures."""
    from igf.pipeline.build import build_chiral_patches

    fingerprints = Path(args.fingerprints) if args.fingerprints else None
    if fingerprints is not None and not fingerprints.exists():
        fingerprints = None

    print("[ig] computing chiral patches...", flush=True)
    result = build_chiral_patches(
        nodes=Path(args.nodes),
        edges=Path(args.edges),
        fingerprints=fingerprints,
        output_dir=Path(args.output_dir),
        run_id=env[DEFAULT_RUN_ID_VAR],
        ego_limit=int(args.ego_limit),
        ego_radius=int(args.ego_radius),
        min_scc_size=int(args.min_scc_size),
        binder_min_size=int(args.binder_min_size),
        max_patch_nodes=int(args.max_patch_nodes),
        spectral_k=int(args.spectral_k),
    )
    print(json.dumps(result, ensure_ascii=False), flush=True)
    return 0 if result.get("ok") else int(result.get("returncode", 1))

def main() -> int:
    parser = argparse.ArgumentParser(description="IG Spire Orchestrator")
    parser.add_argument("--run-id", help="Override the automatically generated run identity")
    
    subparsers = parser.add_subparsers(dest="command", required=True)
    
    # ig process
    proc_parser = subparsers.add_parser("process", help="Compute patches and signatures")
    proc_parser.add_argument("--nodes", default="artifacts/leantrail/arango/ig_nodes.jsonl")
    proc_parser.add_argument("--edges", default="artifacts/leantrail/arango/ig_edges.jsonl")
    proc_parser.add_argument("--fingerprints", default="artifacts/dag/index/expr_fingerprints.jsonl")
    proc_parser.add_argument("--output-dir", default="artifacts/dag/index")
    proc_parser.add_argument("--ego-limit", type=int, default=40)
    proc_parser.add_argument("--ego-radius", type=int, default=2)
    proc_parser.add_argument("--min-scc-size", type=int, default=2)
    proc_parser.add_argument("--binder-min-size", type=int, default=3)
    proc_parser.add_argument("--max-patch-nodes", type=int, default=128)
    proc_parser.add_argument("--spectral-k", type=int, default=8)
    
    # ig build (placeholder for now)
    build_parser = subparsers.add_parser("build", help="Build Lean targets")
    
    args = parser.parse_args()
    
    # Initialize Environment
    run_id = args.run_id or os.environ.get(DEFAULT_RUN_ID_VAR) or generate_run_id()
    env = os.environ.copy()
    env[DEFAULT_RUN_ID_VAR] = run_id
    
    print(f"[ig] run_id: {run_id}")
    
    if args.command == "process":
        return cmd_process(args, env)
    elif args.command == "build":
        print("[ig] build command not yet fully integrated; use lake build")
        return 0
        
    return 0

if __name__ == "__main__":
    sys.exit(main())
