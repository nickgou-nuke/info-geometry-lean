#!/usr/bin/env python3
"""Generate an agent-to-agent truth transport packet from Hermes artifacts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT_DIR = REPO_ROOT / "artifacts" / "hermes_loop" / "truth_transport"
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.hermes_bounded_runner import Packet, build_truth_transport_packet, write_json


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def infer_run_id(run_path: Path, run_data: dict[str, Any]) -> str:
    return str(run_data.get("run_id") or run_path.stem)


def build_from_run(run_path: Path, gravity_path: Path | None, out_path: Path | None) -> Path:
    run_data = load_json(run_path)
    run_id = infer_run_id(run_path, run_data)
    packet_path = Path(str(run_data.get("packet_path") or ""))
    packet_data = load_json(packet_path) if packet_path.exists() else {
        "packet_id": run_data.get("packet_id") or run_id,
        "research_goal": "",
        "formalization_targets": [],
    }

    selected_gravity_path = gravity_path
    if selected_gravity_path is None:
        context_path = ((run_data.get("gravity") or {}).get("context_path"))
        selected_gravity_path = Path(context_path) if context_path else REPO_ROOT / "artifacts" / "hermes_loop" / "gravity_context" / f"{run_id}.json"
    gravity_context = load_json(selected_gravity_path) if selected_gravity_path.exists() else {}

    planner_text = str(run_data.get("planner_text") or "")
    if not planner_text.strip():
        raise SystemExit(f"run has no planner_text: {run_path}")

    transport = build_truth_transport_packet(
        run_id=run_id,
        packet=Packet(path=packet_path, data=packet_data),
        planner_text=planner_text,
        gravity_context=gravity_context,
        gravity_path=selected_gravity_path,
    )

    destination = out_path or DEFAULT_OUT_DIR / f"{run_id}.json"
    write_json(destination, transport)
    write_json(destination.parent / "latest.json", transport)
    return destination


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True, help="Hermes run JSON artifact.")
    parser.add_argument("--gravity", type=Path, help="Override gravity context JSON artifact.")
    parser.add_argument("--out", type=Path, help="Output truth transport path.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    path = build_from_run(args.run, args.gravity, args.out)
    print(f"truth transport written to {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
