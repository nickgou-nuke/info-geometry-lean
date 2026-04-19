#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib
import json
import os
import platform
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = ROOT / "artifacts" / "leandojo" / "probe.json"


def run(cmd: list[str]) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.returncode, proc.stdout.strip(), proc.stderr.strip()


def try_import(name: str) -> dict[str, object]:
    try:
        mod = importlib.import_module(name)
        return {
            "ok": True,
            "file": getattr(mod, "__file__", None),
            "error_type": None,
            "error": None,
        }
    except Exception as exc:  # pragma: no cover - diagnostic path
        return {
            "ok": False,
            "file": None,
            "error_type": type(exc).__name__,
            "error": str(exc),
        }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Probe the local LeanDojo-v2 installation and emit a deterministic report."
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUT,
        help="Output JSON path (default: artifacts/leandojo/probe.json)",
    )
    args = parser.parse_args()

    out_path = args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)

    lean_rc, lean_out, lean_err = run(["lean", "--version"])
    lake_rc, lake_out, lake_err = run(["lake", "--version"])

    package_import = try_import("lean_dojo_v2")
    interaction_import = try_import("lean_dojo_v2.lean_dojo")

    payload = {
        "schema": "leandojo_probe.v1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "workspace_root": str(ROOT),
        "python": {
            "executable": sys.executable,
            "version": sys.version,
        },
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
        },
        "paths": {
            "lean": shutil.which("lean"),
            "lake": shutil.which("lake"),
        },
        "env": {
            "github_access_token_present": "GITHUB_ACCESS_TOKEN" in os.environ,
        },
        "toolchain": {
            "lean_returncode": lean_rc,
            "lean_stdout": lean_out,
            "lean_stderr": lean_err,
            "lake_returncode": lake_rc,
            "lake_stdout": lake_out,
            "lake_stderr": lake_err,
        },
        "imports": {
            "lean_dojo_v2": package_import,
            "lean_dojo_v2.lean_dojo": interaction_import,
        },
        "notes": [
            "The package import name is lean_dojo_v2.",
            "The interaction/data-extraction surface currently requires GITHUB_ACCESS_TOKEN at import time.",
            "This probe does not trace a repo yet; it only validates the host/runtime prerequisites.",
        ],
    }

    with out_path.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
        f.write("\n")

    print(f"wrote {out_path}")
    if not package_import["ok"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
