#!/usr/bin/env python3
"""
Info-Geometry Spire Orchestrator (IG-CLI)
Central entrypoint for the Level 3 Greenfield Architecture.
"""

import argparse
import os
import subprocess
import sys
import time
import uuid
from pathlib import Path

# --- Configuration ---
ROOT = Path(__file__).resolve().parent.parent
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
    script = ROOT / "tools" / "infra" / "build_chiral_patch_hashes.py"
    cmd = [
        sys.executable,
        str(script),
        "--nodes", str(ROOT / "artifacts" / "dag" / "index" / "ig_nodes.jsonl"),
        "--edges", str(ROOT / "artifacts" / "dag" / "index" / "ig_edges.jsonl"),
        "--fingerprints", str(ROOT / "artifacts" / "dag" / "index" / "expr_fingerprints.jsonl"),
        "--output-dir", str(ROOT / "artifacts" / "dag" / "index"),
        "--print-json"
    ]
    return run_command(cmd, env, "computing chiral patches")

def main() -> int:
    parser = argparse.ArgumentParser(description="IG Spire Orchestrator")
    parser.add_argument("--run-id", help="Override the automatically generated run identity")
    
    subparsers = parser.add_subparsers(dest="command", required=True)
    
    # ig process
    proc_parser = subparsers.add_parser("process", help="Compute patches and signatures")
    
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
