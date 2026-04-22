#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.run_proof_prompt_batch import run_copilot_prompt

PIPELINE_DIR = REPO_ROOT / "artifacts" / "hermes_loop" / "copilot_codex_pipeline"
MODULE_HINTS = {
    "repo-softmax-variance-corridor-002": (
        "InfoGeometry.ExponentialFamily.Analytic.Softmax",
        Path("lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean"),
    ),
    "repo-scaled-kl-corridor-001": (
        "InfoGeometry.ExponentialFamily.Analytic.LogSumExp",
        Path("lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean"),
    ),
    "repo-lichnerowicz-corridor-001": (
        "InfoGeometry.Canonical.InformationalLichnerowicz",
        Path("lean/InfoGeometry/Canonical/InformationalLichnerowicz.lean"),
    ),
    "repo-noether-fisher-corridor-001": (
        "InfoGeometry.Canonical.NoetherInference",
        Path("lean/InfoGeometry/Canonical/NoetherInference.lean"),
    ),
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def build_codex_prompt(
    *,
    packet_id: str,
    prompt_text: str,
    copilot_output: str,
    lean_module: str,
    lean_file: Path,
) -> str:
    return (
        f"Packet: {packet_id}\n\n"
        "You are the Codex execution lane for Lean4 theorem work in info-geometry-lean.\n"
        "Use the Copilot formulation only as a candidate. Do not trust it blindly.\n"
        "Preserve theorem-role fidelity and keep edits surgical.\n"
        "If you make edits, verify with Lean before considering the task complete.\n\n"
        "Source proof prompt:\n"
        f"{prompt_text.strip()}\n\n"
        "Copilot candidate formulation:\n"
        f"{copilot_output.strip()}\n\n"
        "Execution instructions:\n"
        f"- Primary Lean file: {lean_file.as_posix()}\n"
        f"- Primary Lean module: {lean_module}\n"
        f"- Lean verification command: lake build {lean_module}\n"
        "- Use tools/infra/lean_interact_wrapper.py for local proof-state or tactic probes when useful.\n"
        "- If the candidate statement is wrong, repair the statement before proof edits.\n"
        "- If no edit is warranted, report the precise reason and stop.\n"
    ).strip() + "\n"


def build_pipeline_payload(
    *,
    run_id: str,
    packet_id: str,
    prompt_path: Path,
    copilot_output: str,
    codex_prompt_path: Path,
    lean_module: str,
    lean_file: Path,
    codex_executed: bool,
) -> dict[str, Any]:
    return {
        "schema": "info_geometry.copilot_codex_lean_pipeline.v1",
        "run_id": run_id,
        "created_at": utc_now(),
        "packet_id": packet_id,
        "prompt_path": str(prompt_path),
        "stages": {
            "copilot": {
                "model": "gpt-4.1",
                "output_text": copilot_output,
            },
            "codex": {
                "prompt_path": str(codex_prompt_path),
                "executed": codex_executed,
            },
            "lean": {
                "module": lean_module,
                "file": lean_file.as_posix(),
                "verify_command": f"lake build {lean_module}",
                "probe_tool": "tools/infra/lean_interact_wrapper.py",
            },
        },
    }


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def run_pipeline(prompt_path: Path, *, model: str, timeout: int) -> Path:
    packet_id = prompt_path.stem
    lean_module, lean_file = MODULE_HINTS.get(packet_id, ("", Path("")))
    prompt_text = prompt_path.read_text(encoding="utf-8")
    response = run_copilot_prompt(prompt_text, model=model, timeout=timeout, workdir=REPO_ROOT)
    copilot_output = response["choices"][0]["message"]["content"].strip()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_id = f"{stamp}-{packet_id}"
    run_dir = PIPELINE_DIR / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    copilot_json = run_dir / "copilot_output.json"
    codex_prompt_path = run_dir / "codex_prompt.md"
    pipeline_json = run_dir / "pipeline.json"
    write_json(copilot_json, response)
    codex_prompt_path.write_text(
        build_codex_prompt(
            packet_id=packet_id,
            prompt_text=prompt_text,
            copilot_output=copilot_output,
            lean_module=lean_module,
            lean_file=lean_file,
        ),
        encoding="utf-8",
    )
    payload = build_pipeline_payload(
        run_id=run_id,
        packet_id=packet_id,
        prompt_path=prompt_path,
        copilot_output=copilot_output,
        codex_prompt_path=codex_prompt_path,
        lean_module=lean_module,
        lean_file=lean_file,
        codex_executed=False,
    )
    write_json(pipeline_json, payload)
    latest_dir = PIPELINE_DIR / f"{packet_id}.latest"
    latest_dir.mkdir(parents=True, exist_ok=True)
    (latest_dir / "codex_prompt.md").write_text(codex_prompt_path.read_text(encoding="utf-8"), encoding="utf-8")
    write_json(latest_dir / "pipeline.json", payload)
    write_json(latest_dir / "copilot_output.json", response)
    return pipeline_json


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Copilot -> Codex -> Lean pipeline artifact generation.")
    parser.add_argument("--prompt", type=Path, required=True)
    parser.add_argument("--model", default="gpt-4.1")
    parser.add_argument("--timeout", type=int, default=180)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    out = run_pipeline(args.prompt, model=args.model, timeout=args.timeout)
    print(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
