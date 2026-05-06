#!/usr/bin/env python3
"""Check local vLLM CLI compatibility for Mistral-family serving.

This is an operational guard for the vLLM fallback lane. It checks whether the
installed `vllm serve --help` surface exposes the flags we rely on for Mistral
Small 4 / Leanstral-style tool and reasoning parsing.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
from pathlib import Path
from typing import Any


SCHEMA = "info_geometry.vllm_mistral_compat_check.v1"

REQUIRED_FLAGS = [
    "--tool-call-parser",
    "--enable-auto-tool-choice",
    "--reasoning-parser",
]

RECOMMENDED_FLAGS = [
    "--no-enable-flashinfer-autotune",
    "--cudagraph-capture-sizes",
    "--max-cudagraph-capture-size",
    "--attention-backend",
    "--kv-cache-dtype",
]

SOURCE_MARKERS = {
    "mistral_tool_parser": (
        "MistralToolParser",
        "adjust_request",
    ),
    "grammar_injection_pr_38150": (
        "MistralGrammarFactory",
        "structured_outputs",
    ),
    "serving_layer_pr_39217": (
        "MistralToolParser",
        "model_can_reason",
    ),
}


def run_help(vllm_bin: str, timeout: int) -> tuple[int | None, str, str]:
    try:
        proc = subprocess.run(
            [vllm_bin, "serve", "--help"],
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        return proc.returncode, proc.stdout, proc.stderr
    except Exception as exc:  # noqa: BLE001
        return None, "", repr(exc)



def vllm_package_root() -> Path | None:
    spec = importlib.util.find_spec("vllm")
    if spec is None or spec.origin is None:
        return None
    return Path(spec.origin).resolve().parent


def source_text_under(root: Path, *, max_files: int = 400) -> str:
    chunks: list[str] = []
    for idx, path in enumerate(root.rglob("*.py")):
        if idx >= max_files:
            break
        try:
            chunks.append(path.read_text(encoding="utf-8", errors="ignore"))
        except Exception:
            continue
    return "\n".join(chunks)


def source_marker_report(root: Path | None = None) -> dict[str, Any]:
    root = root or vllm_package_root()
    if root is None or not root.exists():
        return {
            "available": False,
            "root": None,
            "markers": {},
            "warnings": ["vLLM Python package source was not found"],
        }
    text = source_text_under(root)
    markers = {
        group: {marker: marker in text for marker in marker_list}
        for group, marker_list in SOURCE_MARKERS.items()
    }
    warnings = [
        f"missing vLLM source marker {group}:{marker}"
        for group, rows in markers.items()
        for marker, present in rows.items()
        if not present
    ]
    return {
        "available": True,
        "root": str(root),
        "markers": markers,
        "warnings": warnings,
    }

def check_compat(*, vllm_bin: str = "vllm", timeout: int = 30, vllm_source_root: Path | None = None) -> dict[str, Any]:
    returncode, stdout, stderr = run_help(vllm_bin, timeout)
    text = stdout + "\n" + stderr
    required = {flag: flag in text for flag in REQUIRED_FLAGS}
    recommended = {flag: flag in text for flag in RECOMMENDED_FLAGS}
    source_report = source_marker_report(vllm_source_root)
    ok = returncode == 0 and all(required.values())
    return {
        "schema": SCHEMA,
        "ok": ok,
        "vllm_bin": vllm_bin,
        "returncode": returncode,
        "required_flags": required,
        "recommended_flags": recommended,
        "source_markers": source_report,
        "warnings": [
            f"missing required vLLM flag {flag}" for flag, present in required.items() if not present
        ]
        + [
            f"missing recommended DGX Spark/vLLM flag {flag}" for flag, present in recommended.items() if not present
        ]
        + list(source_report.get("warnings", [])),
        "authority_boundary": {
            "runtime_compatibility_check_only": True,
            "not_a_proof_certificate": True,
            "lean_remains_proof_authority": True,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vllm-bin", default="vllm")
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    report = check_compat(vllm_bin=args.vllm_bin, timeout=args.timeout)
    text = json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0 if report["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
