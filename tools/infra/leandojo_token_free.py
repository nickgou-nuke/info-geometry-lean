#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib
import json
import platform
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_REPORT = ROOT / "artifacts" / "leandojo" / "token_free_surface.json"
DEFAULT_SAMPLE = ROOT / "artifacts" / "leandojo" / "lean_progress_sample.jsonl"
SITE_PACKAGES = Path("/home/goutev/lean-dojo-venv/lib/python3.12/site-packages/lean_dojo_v2")


def try_import(name: str) -> dict[str, object]:
    try:
        mod = importlib.import_module(name)
        return {
            "ok": True,
            "file": getattr(mod, "__file__", None),
            "error_type": None,
            "error": None,
        }
    except Exception as exc:  # pragma: no cover - diagnostics
        return {
            "ok": False,
            "file": None,
            "error_type": type(exc).__name__,
            "error": str(exc),
        }


def load_sample_rows() -> list[dict[str, object]]:
    mod = importlib.import_module("lean_dojo_v2.lean_progress.create_sample_dataset")
    rows = getattr(mod, "SAMPLE_DATA", None)
    if not isinstance(rows, list):
        raise ValueError("LeanDojo-v2 SAMPLE_DATA is unavailable or malformed")
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Use only the token-free LeanDojo-v2 surface and emit deterministic artifacts."
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_REPORT,
        help="Output JSON report path (default: artifacts/leandojo/token_free_surface.json)",
    )
    parser.add_argument(
        "--sample-out",
        type=Path,
        default=DEFAULT_SAMPLE,
        help="Output JSONL sample dataset path (default: artifacts/leandojo/lean_progress_sample.jsonl)",
    )
    parser.add_argument(
        "--write-sample-dataset",
        action="store_true",
        help="Emit the bundled LeanProgress sample dataset into artifacts/leandojo/",
    )
    args = parser.parse_args()

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.sample_out.parent.mkdir(parents=True, exist_ok=True)

    safe_imports = {
        "lean_dojo_v2": try_import("lean_dojo_v2"),
        "lean_dojo_v2.lean_progress": try_import("lean_dojo_v2.lean_progress"),
        "lean_dojo_v2.lean_progress.create_sample_dataset": try_import(
            "lean_dojo_v2.lean_progress.create_sample_dataset"
        ),
    }
    blocked_imports = {
        "lean_dojo_v2.lean_dojo": try_import("lean_dojo_v2.lean_dojo"),
        "lean_dojo_v2.database": try_import("lean_dojo_v2.database"),
        "lean_dojo_v2.lean_agent": try_import("lean_dojo_v2.lean_agent"),
        "lean_dojo_v2.utils": try_import("lean_dojo_v2.utils"),
    }

    external_api_files = []
    external_api_root = SITE_PACKAGES / "external_api"
    if external_api_root.exists():
        for path in sorted(external_api_root.glob("*")):
            if path.is_file():
                external_api_files.append(str(path))

    sample_dataset = {"written": False, "path": str(args.sample_out), "rows": 0}
    if args.write_sample_dataset:
        rows = load_sample_rows()
        with args.sample_out.open("w", encoding="utf-8") as f:
            for row in rows:
                f.write(json.dumps(row, ensure_ascii=False) + "\n")
        sample_dataset = {
            "written": True,
            "path": str(args.sample_out),
            "rows": len(rows),
        }

    payload = {
        "schema": "leandojo_token_free_surface.v1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "workspace_root": str(ROOT),
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
        },
        "safe_imports": safe_imports,
        "blocked_imports": blocked_imports,
        "external_api_files": external_api_files,
        "sample_dataset": sample_dataset,
        "notes": [
            "This artifact uses only the token-free LeanDojo-v2 surface.",
            "The currently safe local surface is centered on lean_dojo_v2.lean_progress and bundled external_api files.",
            "The deeper interaction/data-extraction modules still require GITHUB_ACCESS_TOKEN on this host.",
        ],
    }

    with args.out.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
        f.write("\n")

    print(f"wrote {args.out}")
    if sample_dataset["written"]:
        print(f"wrote {args.sample_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
